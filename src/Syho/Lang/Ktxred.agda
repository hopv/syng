--------------------------------------------------------------------------------
-- Evaluation context and redex
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Lang.Ktxred where

open import Base.Level using (↑_)
open import Base.Func using (_$_)
open import Base.Few using (⊤; ⊥)
open import Base.Eq using (_≡_; refl)
open import Base.Size using (∞)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_)
open import Base.Sum using (_⨿_; ĩ₀_; ĩ₁_)
open import Base.Nat using (ℕ)
open import Syho.Lang.Expr using (Type; ◸_; _↷_; Addr; Expr; Expr˂; ▶_; ∇_; nd;
  λ˙; _◁_; _⁏_; fork; 🞰_; _←_; alloc; free; Val; V⇒E; ṽ_; ṽ↷_)

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
  -- For ▶
  ▶ᴿ_ :  Expr˂ ∞ T →  Redex T
  -- For nd
  ndᴿ :  Redex (◸ X)
  -- For ◁
  _◁ᴿ_ :  (X → Expr ∞ T) →  X →  Redex T
  -- For ⁏
  _⁏ᴿ_ :  Val T →  Expr ∞ U →  Redex U
  -- For fork
  forkᴿ :  Expr ∞ T →  Redex (◸ ⊤)
  -- For 🞰
  🞰ᴿ_ :  Addr →  Redex T
  -- For ←
  _←ᴿ_ :  Addr →  Val T →  Redex (◸ ⊤)
  -- For alloc
  allocᴿ :  ℕ →  Redex (◸ Addr)
  -- For free
  freeᴿ :  Addr →  Redex (◸ ⊤)

--------------------------------------------------------------------------------
-- Ktx :  Syntactic evaluation context

infix 6 🞰ᴷ_ _←ᴷʳ_ _←ᴷˡ_
infixl 5 _◁ᴷʳ_ _◁ᴷˡ_
infixr 4 _⁏ᴷ_

data  Ktx :  Type →  Type →  Set₁  where
  -- Hole
  •ᴷ :  Ktx T T
  -- For ◁
  _◁ᴷʳ_ :  Expr ∞ (X ↷ T) →  Ktx U (◸ X) →  Ktx U T
  _◁ᴷˡ_ :  Ktx U (X ↷ T) →  X →  Ktx U T
  -- For ⁏
  _⁏ᴷ_ :  Ktx V T →  Expr ∞ U →  Ktx V U
  -- For 🞰
  🞰ᴷ_ :  Ktx U (◸ Addr) →  Ktx U T
  -- For ←
  _←ᴷʳ_ :  Expr ∞ (◸ Addr) →  Ktx U T →  Ktx U (◸ ⊤)
  _←ᴷˡ_ :  Ktx U (◸ Addr) →  Val T →  Ktx U (◸ ⊤)
  -- For alloc
  allocᴷ :  Ktx T (◸ ℕ) →  Ktx T (◸ Addr)
  -- For free
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

-- Compose Ktx

infix 5 _ᴷ∘ᴷ_
_ᴷ∘ᴷ_ :  Ktx U V →  Ktx T U →  Ktx T V
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
Val/Ktxred T =  Val T ⨿ Ktxred T

private variable
  K K' :  Ktx T U
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
val/ktxred (∇ x) =  ĩ₀ ṽ x
val/ktxred (λ˙ e˙) =  ĩ₀ ṽ↷ e˙
val/ktxred (▶ e˂) =  ĩ₁ (•ᴷ ᴷ| ▶ᴿ e˂)
val/ktxred nd =  ĩ₁ (•ᴷ ᴷ| ndᴿ)
val/ktxred (e' ◁ e) =  ĩ₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  … | ĩ₁ (K ᴷ| red) =  e' ◁ᴷʳ K ᴷ| red
  … | ĩ₀ ṽ x  with val/ktxred e'
  …   | ĩ₁ (K ᴷ| red) =  K ◁ᴷˡ x ᴷ| red
  …   | ĩ₀ ṽ↷ v =  •ᴷ ᴷ| v ◁ᴿ x
val/ktxred (e ⁏ e') =  ĩ₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  … | ĩ₀ v =  •ᴷ ᴷ| v ⁏ᴿ e'
  … | ĩ₁ (K ᴷ| red) =  K ⁏ᴷ e' ᴷ| red
val/ktxred (fork e) =  ĩ₁ (•ᴷ ᴷ| forkᴿ e)
val/ktxred (🞰 e) =  ĩ₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  … | ĩ₁ (K ᴷ| red) =  🞰ᴷ K ᴷ| red
  … | ĩ₀ ṽ θ =  •ᴷ ᴷ| 🞰ᴿ θ
val/ktxred (e' ← e) =  ĩ₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  … | ĩ₁ (K ᴷ| red) =  e' ←ᴷʳ K ᴷ| red
  … | ĩ₀ v  with val/ktxred e'
  …   | ĩ₁ (K ᴷ| red) =  K ←ᴷˡ v ᴷ| red
  …   | ĩ₀ ṽ θ =  •ᴷ ᴷ| θ ←ᴿ v
val/ktxred (alloc e) =  ĩ₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  … | ĩ₁ (K ᴷ| red) =  allocᴷ K ᴷ| red
  … | ĩ₀ ṽ n =  •ᴷ ᴷ| allocᴿ n
val/ktxred (free e) =  ĩ₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  … | ĩ₁ (K ᴷ| red) =  freeᴷ K ᴷ| red
  … | ĩ₀ ṽ θ =  •ᴷ ᴷ| freeᴿ θ

abstract

  -- If val/ktxred e equlas ĩ₀ v, then e equals V⇒E v

  val/ktxred-ĩ₀ :  val/ktxred e ≡ ĩ₀ v →  e ≡ V⇒E v
  val/ktxred-ĩ₀ {e = ∇ _} refl =  refl
  val/ktxred-ĩ₀ {e = λ˙ _} refl =  refl

  -- val/ktxred (V⇒E v) returns ĩ₀ v

  val/ktxred-V⇒E :  val/ktxred (V⇒E v) ≡ ĩ₀ v
  val/ktxred-V⇒E {v = ṽ _} =  refl
  val/ktxred-V⇒E {v = ṽ↷ _} =  refl

  -- Calculate val/ktxred (K ᴷ◁ e)

  val/ktxred-ktx :  val/ktxred e ≡ ĩ₁ kr →  let K' ᴷ| red = kr in
                    val/ktxred (K ᴷ◁ e) ≡ ĩ₁ (K ᴷ∘ᴷ K' ᴷ| red)
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
