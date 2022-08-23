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
open import Syho.Lang.Expr using (Type; ◸_; _→*_; Addr; Expr; Expr˂; ▶_; ∇_; nd;
  λ˙; _◁_; _⁏_; 🞰_; _←_; alloc; free; Val; V⇒E; val; val→*)

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

-- Converting Redex to Expr

R⇒E :  Redex T →  Expr ∞ T
R⇒E (▶ᴿ e˂) =  ▶ e˂
R⇒E ndᴿ =  nd
R⇒E (e˙ ◁ᴿ x) =  λ˙ e˙ ◁ ∇ x
R⇒E (v ⁏ᴿ e) =  V⇒E v ⁏ e
R⇒E (🞰ᴿ θ) =  🞰 ∇ θ
R⇒E (θ ←ᴿ v) =  ∇ θ ← V⇒E v
R⇒E (allocᴿ n) =  alloc $ ∇ n
R⇒E (freeᴿ θ) =  free $ ∇ θ

--------------------------------------------------------------------------------
-- Ktx :  Syntactic evaluation context

infix 6 🞰ᴷ_ _←ᴷʳ_ _←ᴷˡ_
infixl 5 _◁ᴷʳ_ _◁ᴷˡ_
infixr 4 _⁏ᴷ_

data  Ktx :  Type →  Type →  Set₁  where
  -- Hole
  •ᴷ :  Ktx T T
  -- On ◁
  _◁ᴷʳ_ :  Expr ∞ (X →* T) →  Ktx U (◸ X) →  Ktx U T
  _◁ᴷˡ_ :  Ktx U (X →* T) →  X →  Ktx U T
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
(e' ◁ᴷʳ ktx) ᴷ◁ e =  e' ◁ (ktx ᴷ◁ e)
(ktx ◁ᴷˡ x) ᴷ◁ e =  (ktx ᴷ◁ e) ◁ ∇ x
(ktx ⁏ᴷ e') ᴷ◁ e =  (ktx ᴷ◁ e) ⁏ e'
🞰ᴷ ktx ᴷ◁ e =  🞰 (ktx ᴷ◁ e)
(e' ←ᴷʳ ktx) ᴷ◁ e =  e' ← (ktx ᴷ◁ e)
(ktx ←ᴷˡ v) ᴷ◁ e =  (ktx ᴷ◁ e) ← V⇒E v
allocᴷ ktx ᴷ◁ e =  alloc $ ktx ᴷ◁ e
freeᴷ ktx ᴷ◁ e =  free $ ktx ᴷ◁ e

-- Compose Ktx U T and Ktx V U

infix 5 _ᴷ∘ᴷ_
_ᴷ∘ᴷ_ :  Ktx U T →  Ktx V U →  Ktx V T
•ᴷ ᴷ∘ᴷ ktx =  ktx
(e ◁ᴷʳ ktx) ᴷ∘ᴷ ktx' =  e ◁ᴷʳ (ktx ᴷ∘ᴷ ktx')
(ktx ◁ᴷˡ x) ᴷ∘ᴷ ktx' =  (ktx ᴷ∘ᴷ ktx') ◁ᴷˡ x
(ktx ⁏ᴷ e) ᴷ∘ᴷ ktx' =  (ktx ᴷ∘ᴷ ktx') ⁏ᴷ e
🞰ᴷ ktx ᴷ∘ᴷ ktx' =  🞰ᴷ (ktx ᴷ∘ᴷ ktx')
(e ←ᴷʳ ktx) ᴷ∘ᴷ ktx' =  e ←ᴷʳ (ktx ᴷ∘ᴷ ktx')
(ktx ←ᴷˡ v) ᴷ∘ᴷ ktx' =  (ktx ᴷ∘ᴷ ktx') ←ᴷˡ v
allocᴷ ktx ᴷ∘ᴷ ktx' =  allocᴷ $ ktx ᴷ∘ᴷ ktx'
freeᴷ ktx ᴷ∘ᴷ ktx' =  freeᴷ $ ktx ᴷ∘ᴷ ktx'

-- Type for a context-redex pair

Ktxred :  Type →  Set₁
Ktxred T =  ∑ U , Ktx U T × Redex U

-- Pattern for Ktxred

infix 0 _ᴷ|_
pattern _ᴷ|_ ktx red =  -, ktx , red

-- Type for either a value or a context-redex pair

Val/Ktxred :  Type →  Set₁
Val/Ktxred T =  Val T ⊎ Ktxred T

private variable
  ktx ktx' :  Ktx U T
  kr :  Ktxred T
  v :  Val T

abstract

  -- On ᴷ∘ᴷ and ᴷ◁

  ᴷ∘ᴷ-ᴷ◁ :  (ktx ᴷ∘ᴷ ktx') ᴷ◁ e ≡ ktx ᴷ◁ (ktx' ᴷ◁ e)
  ᴷ∘ᴷ-ᴷ◁ {ktx = •ᴷ} =  refl
  ᴷ∘ᴷ-ᴷ◁ {ktx = _ ◁ᴷʳ ktx} {ktx' = ktx'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {ktx = ktx} {ktx' = ktx'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {ktx = ktx ◁ᴷˡ _} {ktx' = ktx'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {ktx = ktx} {ktx' = ktx'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {ktx = ktx ⁏ᴷ _} {ktx' = ktx'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {ktx = ktx} {ktx' = ktx'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {ktx = 🞰ᴷ ktx} {ktx' = ktx'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {ktx = ktx} {ktx' = ktx'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {ktx = _ ←ᴷʳ ktx} {ktx' = ktx'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {ktx = ktx} {ktx' = ktx'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {ktx = ktx ←ᴷˡ _} {ktx' = ktx'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {ktx = ktx} {ktx' = ktx'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {ktx = allocᴷ ktx} {ktx' = ktx'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {ktx = ktx} {ktx' = ktx'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {ktx = freeᴷ ktx} {ktx' = ktx'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {ktx = ktx} {ktx' = ktx'} {e} =  refl

--------------------------------------------------------------------------------
-- Calculate the value or context-redex pair of the expression

val/ktxred :  Expr ∞ T →  Val/Ktxred T
val/ktxred (∇ x) =  inj₀ $ val x
val/ktxred (λ˙ e˙) =  inj₀ $ val→* e˙
val/ktxred (▶ e˂) =  inj₁ $ •ᴷ ᴷ| ▶ᴿ e˂
val/ktxred nd =  inj₁ $ •ᴷ ᴷ| ndᴿ
val/ktxred (e' ◁ e) =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  ... | inj₁ (ktx ᴷ| red) =  e' ◁ᴷʳ ktx ᴷ| red
  ... | inj₀ (val x)  with val/ktxred e'
  ...   | inj₁ (ktx ᴷ| red) =  ktx ◁ᴷˡ x ᴷ| red
  ...   | inj₀ (val→* v) =  •ᴷ ᴷ| v ◁ᴿ x
val/ktxred (e ⁏ e') =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  ... | inj₀ v =  •ᴷ ᴷ| v ⁏ᴿ e'
  ... | inj₁ (ktx ᴷ| red) =  ktx ⁏ᴷ e' ᴷ| red
val/ktxred (🞰 e) =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  ... | inj₁ (ktx ᴷ| red) =  🞰ᴷ ktx ᴷ| red
  ... | inj₀ (val θ) =  •ᴷ ᴷ| 🞰ᴿ θ
val/ktxred (e' ← e) =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  ... | inj₁ (ktx ᴷ| red) =  e' ←ᴷʳ ktx ᴷ| red
  ... | inj₀ v  with val/ktxred e'
  ...   | inj₁ (ktx ᴷ| red) =  ktx ←ᴷˡ v ᴷ| red
  ...   | inj₀ (val θ) =  •ᴷ ᴷ| θ ←ᴿ v
val/ktxred (alloc e) =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  ... | inj₁ (ktx ᴷ| red) =  allocᴷ ktx ᴷ| red
  ... | inj₀ (val n) =  •ᴷ ᴷ| allocᴿ n
val/ktxred (free e) =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  ... | inj₁ (ktx ᴷ| red) =  freeᴷ ktx ᴷ| red
  ... | inj₀ (val θ) =  •ᴷ ᴷ| freeᴿ θ

-- Judge if the expression is non-value

nonval :  Expr ∞ T →  Set₀
nonval e  with val/ktxred e
... | inj₀ _ =  ⊥
... | inj₁ _ =  ⊤

abstract

  -- val/ktxred (V⇒E v) returns inj₀ v

  val/ktxred-V⇒E :  val/ktxred (V⇒E v) ≡ inj₀ v
  val/ktxred-V⇒E {v = val _} =  refl
  val/ktxred-V⇒E {v = val→* _} =  refl

  -- Nonval enriched with an evaluation context

  nonval-ktx :  nonval e →  nonval (ktx ᴷ◁ e)
  nonval-ktx {ktx = •ᴷ} n'e =  n'e
  nonval-ktx {ktx = _ ◁ᴷʳ _} =  _
  nonval-ktx {ktx = _ ◁ᴷˡ _} =  _
  nonval-ktx {ktx = _ ⁏ᴷ _} =  _
  nonval-ktx {ktx = 🞰ᴷ _} =  _
  nonval-ktx {ktx = _ ←ᴷʳ _} =  _
  nonval-ktx {ktx = _ ←ᴷˡ _} =  _
  nonval-ktx {ktx = allocᴷ _} =  _
  nonval-ktx {ktx = freeᴷ _} =  _

  -- Calculate val/ktxred (ktx ᴷ◁ e)

  val/ktxred-ktx :  val/ktxred e ≡ inj₁ kr →  let ktx' ᴷ| red = kr in
                    val/ktxred (ktx ᴷ◁ e) ≡ inj₁ (ktx ᴷ∘ᴷ ktx' ᴷ| red)
  val/ktxred-ktx {ktx = •ᴷ} eq =  eq
  val/ktxred-ktx {e = e} {ktx = _ ◁ᴷʳ ktx} eq
    rewrite val/ktxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ktxred-ktx {e = e} {ktx = ktx ◁ᴷˡ _} eq
    rewrite val/ktxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ktxred-ktx {e = e} {ktx = ktx ⁏ᴷ _} eq
    rewrite val/ktxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ktxred-ktx {e = e} {ktx = 🞰ᴷ ktx} eq
    rewrite val/ktxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ktxred-ktx {e = e} {ktx = _ ←ᴷʳ ktx} eq
    rewrite val/ktxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ktxred-ktx {e = e} {ktx = ktx ←ᴷˡ v} eq
    rewrite val/ktxred-V⇒E {v = v} | val/ktxred-ktx {e = e} {ktx = ktx} eq
    =  refl
  val/ktxred-ktx {e = e} {ktx = allocᴷ ktx} eq
    rewrite val/ktxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ktxred-ktx {e = e} {ktx = freeᴷ ktx} eq
    rewrite val/ktxred-ktx {e = e} {ktx = ktx} eq =  refl

  -- Invert from val/ktxred (ktx ᴷ◁ e)

  val/ktxred-ktx-inv :  nonval e →
    val/ktxred (ktx ᴷ◁ e) ≡ inj₁ kr →  let ktx'' ᴷ| red = kr in
    ∑ ktx' ,  ktx'' ≡ ktx ᴷ∘ᴷ ktx'  ×  val/ktxred e ≡ inj₁ (ktx' ᴷ| red)
  val/ktxred-ktx-inv {ktx = •ᴷ} _ eq =  -, refl , eq
  val/ktxred-ktx-inv {e = e} {ktx = _ ◁ᴷʳ ktx} nv'e eq
    with val/ktxred (ktx ᴷ◁ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {ktx = ktx} {kr} nv'e)
  ...   | inj₁ _ | _ | refl | ind  with ind refl
  ...     | ktx' , refl , eq' =  ktx' , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = ktx ◁ᴷˡ _} nv'e eq
    with val/ktxred (ktx ᴷ◁ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {ktx = ktx} {kr} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = ktx ⁏ᴷ _} nv'e eq
    with val/ktxred (ktx ᴷ◁ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {ktx = ktx} {kr} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = 🞰ᴷ ktx} nv'e eq
    with val/ktxred (ktx ᴷ◁ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {ktx = ktx} {kr} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = _ ←ᴷʳ ktx} nv'e eq
    with val/ktxred (ktx ᴷ◁ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {ktx = ktx} {kr} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = ktx ←ᴷˡ val _} nv'e eq
    with val/ktxred (ktx ᴷ◁ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {ktx = ktx} {kr} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = ktx ←ᴷˡ val→* _} nv'e eq
    with val/ktxred (ktx ᴷ◁ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {ktx = ktx} {kr} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = allocᴷ ktx} nv'e eq
    with val/ktxred (ktx ᴷ◁ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {ktx = ktx} {kr} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = freeᴷ ktx} nv'e eq
    with val/ktxred (ktx ᴷ◁ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {ktx = ktx} {kr} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
