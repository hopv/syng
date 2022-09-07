--------------------------------------------------------------------------------
-- Evaluation context and redex
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Lang.Ktxred where

open import Base.Level using (↑_)
open import Base.Size using (∞)
open import Base.Func using (_$_)
open import Base.Few using (⊤; ⊥)
open import Base.Eq using (_≡_; refl)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_)
open import Base.Sum using (_⊎_; inj₀; inj₁)
open import Base.Nat using (ℕ)
open import Syho.Lang.Expr using (Type; ◸_; _↷_; Addr; Expr; Expr˂; ▶_; ∇_; nd;
  λ˙; _◁_; _⁏_; 🞰_; _←_; alloc; free; Val; V⇒E; ṽ_; ṽ↷_)

private variable
  X :  Set₀
  T U V :  Type
  e :  Expr ∞ T

-------------------------------------------------------------------------------
-- Redex

infix 6 ▶ᴿ_ 🞰ᴿ_ _←ᴿ_
infixl 5 _◁ᴿ_
infixr 4 _⁏ᴿ_

data  Redex :  Type →  Set₁  where
  ▶ᴿ_ :  Expr˂ ∞ T →  Redex T
  ndᴿ :  Redex (◸ X)
  _◁ᴿ_ :  (X → Expr ∞ T) →  X →  Redex T
  _⁏ᴿ_ :  Val T →  Expr ∞ U →  Redex U
  🞰ᴿ_ :  Addr →  Redex T
  _←ᴿ_ :  Addr →  Val T →  Redex (◸ ⊤)
  allocᴿ :  ℕ →  Redex (◸ Addr)
  freeᴿ :  Addr →  Redex (◸ ⊤)

--------------------------------------------------------------------------------
-- Ktx :  Syntactic evaluation context

infix 6 🞰ᴷ_ _←ᴷʳ_ _←ᴷˡ_
infixl 5 _◁ᴷʳ_ _◁ᴷˡ_
infixr 4 _⁏ᴷ_

data  Ktx :  Type →  Type →  Set₁  where
  -- Hole
  •ᴷ :  Ktx T T
  -- On ◁
  _◁ᴷʳ_ :  Expr ∞ (X ↷ T) →  Ktx U (◸ X) →  Ktx U T
  _◁ᴷˡ_ :  Ktx U (X ↷ T) →  X →  Ktx U T
  -- On ⁏
  _⁏ᴷ_ :  Ktx V T →  Expr ∞ U →  Ktx V U
  -- On 🞰
  🞰ᴷ_ :  Ktx U (◸ Addr) →  Ktx U T
  -- On ←
  _←ᴷʳ_ :  Expr ∞ (◸ Addr) →  Ktx U T →  Ktx U (◸ ⊤)
  _←ᴷˡ_ :  Ktx U (◸ Addr) →  Val T →  Ktx U (◸ ⊤)
  -- On alloc
  allocᴷ :  Ktx T (◸ ℕ) →  Ktx T (◸ Addr)
  -- On free
  freeᴷ :  Ktx T (◸ Addr) →  Ktx T (◸ ⊤)

-- Fill in the hole of Ktx U T with Expr ∞ U to get Expr ∞ T

infix 5 _ᴷ◁_
_ᴷ◁_ :  Ktx U T →  Expr ∞ U →  Expr ∞ T
•ᴷ ᴷ◁ e =  e
(e' ◁ᴷʳ K) ᴷ◁ e =  e' ◁ (K ᴷ◁ e)
(K ◁ᴷˡ x) ᴷ◁ e =  (K ᴷ◁ e) ◁ ∇ x
(K ⁏ᴷ e') ᴷ◁ e =  (K ᴷ◁ e) ⁏ e'
🞰ᴷ K ᴷ◁ e =  🞰 (K ᴷ◁ e)
(e' ←ᴷʳ K) ᴷ◁ e =  e' ← (K ᴷ◁ e)
(K ←ᴷˡ v) ᴷ◁ e =  (K ᴷ◁ e) ← V⇒E v
allocᴷ K ᴷ◁ e =  alloc $ K ᴷ◁ e
freeᴷ K ᴷ◁ e =  free $ K ᴷ◁ e

-- Compose Ktx U T and Ktx V U

infix 5 _ᴷ∘ᴷ_
_ᴷ∘ᴷ_ :  Ktx U T →  Ktx V U →  Ktx V T
•ᴷ ᴷ∘ᴷ K =  K
(e ◁ᴷʳ K) ᴷ∘ᴷ K' =  e ◁ᴷʳ (K ᴷ∘ᴷ K')
(K ◁ᴷˡ x) ᴷ∘ᴷ K' =  (K ᴷ∘ᴷ K') ◁ᴷˡ x
(K ⁏ᴷ e) ᴷ∘ᴷ K' =  (K ᴷ∘ᴷ K') ⁏ᴷ e
🞰ᴷ K ᴷ∘ᴷ K' =  🞰ᴷ (K ᴷ∘ᴷ K')
(e ←ᴷʳ K) ᴷ∘ᴷ K' =  e ←ᴷʳ (K ᴷ∘ᴷ K')
(K ←ᴷˡ v) ᴷ∘ᴷ K' =  (K ᴷ∘ᴷ K') ←ᴷˡ v
allocᴷ K ᴷ∘ᴷ K' =  allocᴷ $ K ᴷ∘ᴷ K'
freeᴷ K ᴷ∘ᴷ K' =  freeᴷ $ K ᴷ∘ᴷ K'

-- Type for a context-redex pair

Ktxred :  Type →  Set₁
Ktxred T =  ∑ U , Ktx U T × Redex U

-- Pattern for Ktxred

infix 0 _ᴷ|_
pattern _ᴷ|_ K red =  -, K , red

-- Type for either a value or a context-redex pair

Val/Ktxred :  Type →  Set₁
Val/Ktxred T =  Val T ⊎ Ktxred T

private variable
  K K' :  Ktx U T
  kr :  Ktxred T
  v :  Val T

abstract

  -- On ᴷ∘ᴷ and ᴷ◁

  ᴷ∘ᴷ-ᴷ◁ :  (K ᴷ∘ᴷ K') ᴷ◁ e ≡ K ᴷ◁ (K' ᴷ◁ e)
  ᴷ∘ᴷ-ᴷ◁ {K = •ᴷ} =  refl
  ᴷ∘ᴷ-ᴷ◁ {K = _ ◁ᴷʳ K} {K' = K'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {K = K} {K' = K'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {K = K ◁ᴷˡ _} {K' = K'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {K = K} {K' = K'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {K = K ⁏ᴷ _} {K' = K'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {K = K} {K' = K'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {K = 🞰ᴷ K} {K' = K'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {K = K} {K' = K'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {K = _ ←ᴷʳ K} {K' = K'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {K = K} {K' = K'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {K = K ←ᴷˡ _} {K' = K'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {K = K} {K' = K'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {K = allocᴷ K} {K' = K'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {K = K} {K' = K'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {K = freeᴷ K} {K' = K'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {K = K} {K' = K'} {e} =  refl

--------------------------------------------------------------------------------
-- Calculate the value or context-redex pair of the expression

val/ktxred :  Expr ∞ T →  Val/Ktxred T
val/ktxred (∇ x) =  inj₀ $ ṽ x
val/ktxred (λ˙ e˙) =  inj₀ $ ṽ↷ e˙
val/ktxred (▶ e˂) =  inj₁ $ •ᴷ ᴷ| ▶ᴿ e˂
val/ktxred nd =  inj₁ $ •ᴷ ᴷ| ndᴿ
val/ktxred (e' ◁ e) =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  … | inj₁ (K ᴷ| red) =  e' ◁ᴷʳ K ᴷ| red
  … | inj₀ (ṽ x)  with val/ktxred e'
  …   | inj₁ (K ᴷ| red) =  K ◁ᴷˡ x ᴷ| red
  …   | inj₀ (ṽ↷ v) =  •ᴷ ᴷ| v ◁ᴿ x
val/ktxred (e ⁏ e') =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  … | inj₀ v =  •ᴷ ᴷ| v ⁏ᴿ e'
  … | inj₁ (K ᴷ| red) =  K ⁏ᴷ e' ᴷ| red
val/ktxred (🞰 e) =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  … | inj₁ (K ᴷ| red) =  🞰ᴷ K ᴷ| red
  … | inj₀ (ṽ θ) =  •ᴷ ᴷ| 🞰ᴿ θ
val/ktxred (e' ← e) =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  … | inj₁ (K ᴷ| red) =  e' ←ᴷʳ K ᴷ| red
  … | inj₀ v  with val/ktxred e'
  …   | inj₁ (K ᴷ| red) =  K ←ᴷˡ v ᴷ| red
  …   | inj₀ (ṽ θ) =  •ᴷ ᴷ| θ ←ᴿ v
val/ktxred (alloc e) =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  … | inj₁ (K ᴷ| red) =  allocᴷ K ᴷ| red
  … | inj₀ (ṽ n) =  •ᴷ ᴷ| allocᴿ n
val/ktxred (free e) =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  … | inj₁ (K ᴷ| red) =  freeᴷ K ᴷ| red
  … | inj₀ (ṽ θ) =  •ᴷ ᴷ| freeᴿ θ

-- Judge if the expression is non-value

nonval :  Expr ∞ T →  Set₀
nonval e  with val/ktxred e
… | inj₀ _ =  ⊥
… | inj₁ _ =  ⊤

abstract

  -- val/ktxred (V⇒E v) returns inj₀ v

  val/ktxred-V⇒E :  val/ktxred (V⇒E v) ≡ inj₀ v
  val/ktxred-V⇒E {v = ṽ _} =  refl
  val/ktxred-V⇒E {v = ṽ↷ _} =  refl

  -- Nonval enriched with an evaluation context

  nonval-ktx :  nonval e →  nonval (K ᴷ◁ e)
  nonval-ktx {K = •ᴷ} n'e =  n'e
  nonval-ktx {K = _ ◁ᴷʳ _} =  _
  nonval-ktx {K = _ ◁ᴷˡ _} =  _
  nonval-ktx {K = _ ⁏ᴷ _} =  _
  nonval-ktx {K = 🞰ᴷ _} =  _
  nonval-ktx {K = _ ←ᴷʳ _} =  _
  nonval-ktx {K = _ ←ᴷˡ _} =  _
  nonval-ktx {K = allocᴷ _} =  _
  nonval-ktx {K = freeᴷ _} =  _

  -- Calculate val/ktxred (K ᴷ◁ e)

  val/ktxred-ktx :  val/ktxred e ≡ inj₁ kr →  let K' ᴷ| red = kr in
                    val/ktxred (K ᴷ◁ e) ≡ inj₁ (K ᴷ∘ᴷ K' ᴷ| red)
  val/ktxred-ktx {K = •ᴷ} eq =  eq
  val/ktxred-ktx {e = e} {K = _ ◁ᴷʳ K} eq
    rewrite val/ktxred-ktx {e = e} {K = K} eq =  refl
  val/ktxred-ktx {e = e} {K = K ◁ᴷˡ _} eq
    rewrite val/ktxred-ktx {e = e} {K = K} eq =  refl
  val/ktxred-ktx {e = e} {K = K ⁏ᴷ _} eq
    rewrite val/ktxred-ktx {e = e} {K = K} eq =  refl
  val/ktxred-ktx {e = e} {K = 🞰ᴷ K} eq
    rewrite val/ktxred-ktx {e = e} {K = K} eq =  refl
  val/ktxred-ktx {e = e} {K = _ ←ᴷʳ K} eq
    rewrite val/ktxred-ktx {e = e} {K = K} eq =  refl
  val/ktxred-ktx {e = e} {K = K ←ᴷˡ v} eq
    rewrite val/ktxred-V⇒E {v = v} | val/ktxred-ktx {e = e} {K = K} eq =  refl
  val/ktxred-ktx {e = e} {K = allocᴷ K} eq
    rewrite val/ktxred-ktx {e = e} {K = K} eq =  refl
  val/ktxred-ktx {e = e} {K = freeᴷ K} eq
    rewrite val/ktxred-ktx {e = e} {K = K} eq =  refl

  -- Invert from val/ktxred (K ᴷ◁ e)

  val/ktxred-ktx-inv :  nonval e →
    val/ktxred (K ᴷ◁ e) ≡ inj₁ kr →  let K'' ᴷ| red = kr in
    ∑ K' ,  K'' ≡ K ᴷ∘ᴷ K'  ×  val/ktxred e ≡ inj₁ (K' ᴷ| red)
  val/ktxred-ktx-inv {K = •ᴷ} _ eq =  -, refl , eq
  val/ktxred-ktx-inv {e = e} {K = _ ◁ᴷʳ K} nv'e eq
    with val/ktxred (K ᴷ◁ e) | nonval-ktx {K = K} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {K = K} {kr} nv'e)
  …   | inj₁ _ | _ | refl | ind  with ind refl
  …     | K' , refl , eq' =  K' , refl , eq'
  val/ktxred-ktx-inv {e = e} {K = K ◁ᴷˡ _} nv'e eq
    with val/ktxred (K ᴷ◁ e) | nonval-ktx {K = K} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {K = K} {kr} nv'e)
  … | inj₁ _ | _ | refl | ind  with ind refl
  …   | K , refl , eq' =  K , refl , eq'
  val/ktxred-ktx-inv {e = e} {K = K ⁏ᴷ _} nv'e eq
    with val/ktxred (K ᴷ◁ e) | nonval-ktx {K = K} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {K = K} {kr} nv'e)
  … | inj₁ _ | _ | refl | ind  with ind refl
  …   | K , refl , eq' =  K , refl , eq'
  val/ktxred-ktx-inv {e = e} {K = 🞰ᴷ K} nv'e eq
    with val/ktxred (K ᴷ◁ e) | nonval-ktx {K = K} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {K = K} {kr} nv'e)
  … | inj₁ _ | _ | refl | ind  with ind refl
  …   | K , refl , eq' =  K , refl , eq'
  val/ktxred-ktx-inv {e = e} {K = _ ←ᴷʳ K} nv'e eq
    with val/ktxred (K ᴷ◁ e) | nonval-ktx {K = K} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {K = K} {kr} nv'e)
  … | inj₁ _ | _ | refl | ind  with ind refl
  …   | K , refl , eq' =  K , refl , eq'
  val/ktxred-ktx-inv {e = e} {K = K ←ᴷˡ ṽ _} nv'e eq
    with val/ktxred (K ᴷ◁ e) | nonval-ktx {K = K} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {K = K} {kr} nv'e)
  … | inj₁ _ | _ | refl | ind  with ind refl
  …   | K , refl , eq' =  K , refl , eq'
  val/ktxred-ktx-inv {e = e} {K = K ←ᴷˡ ṽ↷ _} nv'e eq
    with val/ktxred (K ᴷ◁ e) | nonval-ktx {K = K} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {K = K} {kr} nv'e)
  … | inj₁ _ | _ | refl | ind  with ind refl
  …   | K , refl , eq' =  K , refl , eq'
  val/ktxred-ktx-inv {e = e} {K = allocᴷ K} nv'e eq
    with val/ktxred (K ᴷ◁ e) | nonval-ktx {K = K} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {K = K} {kr} nv'e)
  … | inj₁ _ | _ | refl | ind  with ind refl
  …   | K , refl , eq' =  K , refl , eq'
  val/ktxred-ktx-inv {e = e} {K = freeᴷ K} nv'e eq
    with val/ktxred (K ᴷ◁ e) | nonval-ktx {K = K} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {K = K} {kr} nv'e)
  … | inj₁ _ | _ | refl | ind  with ind refl
  …   | K , refl , eq' =  K , refl , eq'
