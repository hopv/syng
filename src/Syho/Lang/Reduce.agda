--------------------------------------------------------------------------------
-- Reduction
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Lang.Reduce where

open import Base.Level using (↑_)
open import Base.Func using (_$_)
open import Base.Eq using (_≡_; refl; ◠_)
open import Base.Size using (∞; !)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_)
open import Base.Sum using (ĩ₁_)
open import Base.Option using (¿_; š_; ň; _$¿_; _»-¿_)
open import Base.Dec using (upd˙)
open import Base.Nat using (ℕ; Cofin; ∀⇒Cofin; Cofin-upd˙)
open import Base.List using (List; _‼_; upd; rep)
open import Syho.Lang.Expr using (Type; ◸_; Addr; addr; Expr; Expr˂; ∇_; Val;
  V⇒E; TyVal; ⊤ṽ)
open import Syho.Lang.Ktxred using (Redex; ▶ᴿ_; ndᴿ; _◁ᴿ_; _⁏ᴿ_; 🞰ᴿ_; _←ᴿ_;
  allocᴿ; freeᴿ; Ktx; _ᴷ◁_; ᴷ∘ᴷ-ᴷ◁; Ktxred; _ᴷ|_; val/ktxred; nonval;
  val/ktxred-ktx; val/ktxred-ktx-inv)

--------------------------------------------------------------------------------
-- Memory

Mem :  Set₁
Mem =  ℕ →  ¿ List TyVal

private variable
  M M' :  Mem
  o :  ℕ
  ᵗv :  TyVal
  avsˇ :  ¿ List TyVal
  θ :  Addr

-- Memory read

infix 5 _‼ᴹ_
_‼ᴹ_ :  Mem →  Addr →  ¿ TyVal
M ‼ᴹ addr o i =  M o »-¿ _‼ i

-- Empty memory

empᴹ :  Mem
empᴹ _ =  ň

-- Memory update

updᴹ :  Addr →  TyVal →  Mem →  Mem
updᴹ (addr o i) ᵗv M =  upd˙ o (upd i ᵗv $¿ M o) M

-- Memory validity

infix 3 ✓ᴹ_
✓ᴹ_ :  Mem →  Set₁
✓ᴹ M =  Cofin (λ _ → _≡ ň) M

abstract

  -- ✓ᴹ holds for empᴹ

  ✓ᴹ-empᴹ :  ✓ᴹ empᴹ
  ✓ᴹ-empᴹ =  ∀⇒Cofin {F = λ _ → _≡ ň} λ _ → refl

  -- ✓ᴹ is preserved by upd˙ and updᴹ

  ✓ᴹ-upd˙ :  ✓ᴹ M →  ✓ᴹ (upd˙ o avsˇ M)
  ✓ᴹ-upd˙ =  Cofin-upd˙ {F = λ _ → _≡ ň}

  ✓ᴹ-updᴹ :  ✓ᴹ M →  ✓ᴹ (updᴹ θ ᵗv M)
  ✓ᴹ-updᴹ =  ✓ᴹ-upd˙

--------------------------------------------------------------------------------
-- Reduction

private variable
  T U V :  Type
  X :  Set₀
  e e' e'' :  Expr ∞ T
  e˂ :  Expr˂ ∞ T
  e˙ :  X → Expr ∞ T
  K :  Ktx U T
  red : Redex T
  x :  X
  v :  Val V
  n :  ℕ
  kr :  Ktxred T

infix 4 _⇒ᴿ_ _⇒ᴷᴿ_

-- Reduction on a redex

data  _⇒ᴿ_ :  ∀{T} →  (Redex T × Mem) →  (Expr ∞ T × Mem) →  Set₁  where
  ▶-red :  (▶ᴿ e˂ , M) ⇒ᴿ (e˂ .! , M)
  nd-red :  ∀(x : X) →  (ndᴿ , M) ⇒ᴿ (∇ x , M)
  ◁-red :  (e˙ ◁ᴿ x , M) ⇒ᴿ (e˙ x , M)
  ⁏-red :  (v ⁏ᴿ e , M) ⇒ᴿ (e , M)
  🞰-red :  M ‼ᴹ θ ≡ š (V , v) →  (🞰ᴿ θ , M) ⇒ᴿ (V⇒E v , M)
  ←-red :  (θ ←ᴿ v , M) ⇒ᴿ (∇ _ , updᴹ θ (V , v) M)
  alloc-red :  ∀ o →  M o ≡ ň →
    (allocᴿ n , M) ⇒ᴿ (∇ addr o 0 , upd˙ o (š rep n ⊤ṽ) M)
  free-red :  (freeᴿ (addr o 0) , M) ⇒ᴿ (∇ _ , upd˙ o ň M)

-- Reduction on a context-redex pair

data  _⇒ᴷᴿ_ {T} :  (Ktxred T × Mem) →  (Expr ∞ T × Mem) →  Set₁  where
  redᴷᴿ :  (red , M) ⇒ᴿ (e' , M') →  (K ᴷ| red , M) ⇒ᴷᴿ (K ᴷ◁ e' , M')

-- Reduction on an expression

data  _⇒ᴱ_ :  (Expr ∞ T × Mem) →  (Expr ∞ T × Mem) →  Set₁  where
  redᴱ :  val/ktxred e ≡ ĩ₁ kr →  (kr , M) ⇒ᴷᴿ (e' , M') →
          (e , M) ⇒ᴱ (e' , M')

abstract

  -- Enrich a reduction with an evaluation context

  red-ktx :  (e , M) ⇒ᴱ (e' , M') →  (K ᴷ◁ e , M) ⇒ᴱ (K ᴷ◁ e' , M')
  red-ktx {K = K} (redᴱ eq (redᴷᴿ {e' = e'} {K = K'} r⇒))
    rewrite ◠ ᴷ∘ᴷ-ᴷ◁ {K = K} {K' = K'} {e'}
    =  redᴱ (val/ktxred-ktx eq) (redᴷᴿ r⇒)

  -- Unwrap an evaluation context from a reduction

  red-ktx-inv :  nonval e →  (K ᴷ◁ e , M) ⇒ᴱ (e'' , M') →
                 ∑ e' ,  e'' ≡ K ᴷ◁ e'  ×  (e , M) ⇒ᴱ (e' , M')
  red-ktx-inv {K = K} nv'e (redᴱ eq (redᴷᴿ r⇒))  with val/ktxred-ktx-inv nv'e eq
  … | -, refl , eq' =  -, ᴷ∘ᴷ-ᴷ◁ {K = K} , redᴱ eq' $ redᴷᴿ r⇒
