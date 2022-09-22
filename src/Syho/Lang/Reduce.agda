--------------------------------------------------------------------------------
-- Reduction
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Lang.Reduce where

open import Base.Level using (↑_)
open import Base.Func using (_$_; flip)
open import Base.Few using (⊤)
open import Base.Eq using (_≡_; refl; ◠_)
open import Base.Size using (Size; ∞; Thunk; !)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_)
open import Base.Sum using (ĩ₁_)
open import Base.Option using (¿_; š_; ň; ¿-case; _$¿_; _»-¿_)
open import Base.Dec using (upd˙)
open import Base.Nat using (ℕ; Cofin˙; ∀⇒Cofin˙; Cofin˙-upd˙; Cofin˙-∑)
open import Base.List using (List; _∷_; _‼_; upd; rep)
open import Syho.Lang.Expr using (Type; ◸_; Addr; ad; Expr; Expr˂; ∇_; Val;
  V⇒E; TyVal; ⊤ṽ)
open import Syho.Lang.Ktxred using (Redex; ▶ᴿ_; ndᴿ; _◁ᴿ_; _⁏ᴿ_; forkᴿ; 🞰ᴿ_;
  _←ᴿ_; allocᴿ; freeᴿ; Ktx; _ᴷ◁_; Ktxred; _ᴷ|_; val/ktxred)

--------------------------------------------------------------------------------
-- Memory

-- Mblo :  Memory block state
-- Mem :  Memory state
Mblo Mem :  Set₁
Mblo =  ¿ List TyVal
Mem =  ℕ →  Mblo

private variable
  M M' M'' :  Mem
  Mb :  Mblo
  o :  ℕ
  θ :  Addr
  ᵗv :  TyVal

-- Memory read

infix 5 _‼ᴹ_
_‼ᴹ_ :  Mem →  Addr →  ¿ TyVal
M ‼ᴹ ad o i =  M o »-¿ _‼ i

-- Empty memory

empᴹ :  Mem
empᴹ _ =  ň

-- Memory update

updᴹ :  Addr →  TyVal →  Mem →  Mem
updᴹ (ad o i) ᵗv M =  upd˙ o (upd i ᵗv $¿ M o) M

-- Memory validity

infix 3 ✓ᴹ_
✓ᴹ_ :  Mem →  Set₁
✓ᴹ M =  Cofin˙ (λ _ → _≡ ň) M

abstract

  -- ✓ᴹ holds for empᴹ

  ✓ᴹ-empᴹ :  ✓ᴹ empᴹ
  ✓ᴹ-empᴹ =  ∀⇒Cofin˙ {F = λ _ → _≡ ň} λ _ → refl

  -- ✓ᴹ is preserved by upd˙ and updᴹ

  ✓ᴹ-upd˙ :  ✓ᴹ M →  ✓ᴹ (upd˙ o Mb M)
  ✓ᴹ-upd˙ =  Cofin˙-upd˙ {F = λ _ → _≡ ň}

  -- If ✓ᴹ M holds, then M o ≡ ň for some o

  ✓ᴹ-∑ň :  ✓ᴹ M →  ∑ o , M o ≡ ň
  ✓ᴹ-∑ň =  Cofin˙-∑ {F = λ _ → _≡ ň}

--------------------------------------------------------------------------------
-- Reduction

-- Thrpool T :  Thread pool, consisting of the head thread Expr ∞ T and
--              the tail threads List (Expr ∞ (◸ ⊤))

Thrpool :  Type →  Set₁
Thrpool T =  Expr ∞ T  ×  List (Expr ∞ (◸ ⊤))

private variable
  T U :  Type
  X :  Set₀
  e e' e'' :  Expr ∞ T
  e˂ :  Expr˂ ∞ T
  e˙ :  X → Expr ∞ T
  eˇ :  ¿ Expr ∞ (◸ ⊤)
  es es' :  List (Expr ∞ (◸ ⊤))
  tp tp' tp'' :  Thrpool T
  K :  Ktx T U
  red : Redex T
  x :  X
  v :  Val T
  n :  ℕ
  kr :  Ktxred T
  ι :  Size

infix 4 _⇒ᴿ_ _⇒ᴷᴿ_ _⇒ᴱ_ _⇐ᴷᴿ_ _⇐ᴱ_

-- ⇒ᴿ :  Reduction of a redex
--       The ¿ Expr ∞ (◸ ⊤) part is a possibly forked thread

data  _⇒ᴿ_ :  Redex T × Mem →  Expr ∞ T × ¿ Expr ∞ (◸ ⊤) × Mem →  Set₁  where

  -- For ▶
  ▶⇒ :  (▶ᴿ e˂ , M) ⇒ᴿ (e˂ .! , ň , M)

  -- For nd
  nd⇒ :  ∀(x : X) →  (ndᴿ , M) ⇒ᴿ (∇ x , ň , M)

  -- For ◁
  ◁⇒ :  (e˙ ◁ᴿ x , M) ⇒ᴿ (e˙ x , ň , M)

  -- For ⁏
  ⁏⇒ :  (v ⁏ᴿ e , M) ⇒ᴿ (e , ň , M)

  -- For fork
  fork⇒ :  (forkᴿ e , M) ⇒ᴿ (∇ _ , š e , M)

  -- For 🞰
  🞰⇒ :  M ‼ᴹ θ ≡ š (-, v) →  (🞰ᴿ θ , M) ⇒ᴿ (V⇒E v , ň , M)

  -- For ←, with a check that θ is in the domain of M
  ←⇒ :  ∑ ᵗu , M ‼ᴹ θ ≡ š ᵗu →  (θ ←ᴿ v , M) ⇒ᴿ (∇ _ , ň , updᴹ θ (-, v) M)

  -- For alloc, for any o out of the domain of M
  alloc⇒ :  ∀ o →  M o ≡ ň →
    (allocᴿ n , M) ⇒ᴿ (∇ ad o 0 , ň , upd˙ o (š rep n ⊤ṽ) M)

  -- For free, with a check that o is in the domain of M
  free⇒ :  ∑ ᵗvs , M o ≡ š ᵗvs →  (freeᴿ (ad o 0) , M) ⇒ᴿ (∇ _ , ň , upd˙ o ň M)

-- ⇒ᴷᴿ :  Reduction of a context-redex pair

data  _⇒ᴷᴿ_ :  Ktxred T × Mem →  Expr ∞ T × ¿ Expr ∞ (◸ ⊤) × Mem →  Set₁  where
  redᴷᴿ :  (red , M) ⇒ᴿ (e' , eˇ , M') →  (K ᴷ| red , M) ⇒ᴷᴿ (K ᴷ◁ e' , eˇ , M')

-- ⇒ᴱ :  Reduction of an expression

data  _⇒ᴱ_ :  Expr ∞ T × Mem →  Expr ∞ T × ¿ Expr ∞ (◸ ⊤) × Mem →  Set₁  where
  redᴱ :  val/ktxred e ≡ ĩ₁ kr →  (kr , M) ⇒ᴷᴿ (e' , eˇ , M') →
          (e , M) ⇒ᴱ (e' , eˇ , M')

-- ⇒ᵀ :  Reduction of a thread list

data  _⇒ᵀ_ :  Thrpool T × Mem →  Thrpool T × Mem →  Set₁  where
  -- Reduce the head thread
  redᵀ-hd :  (e , M) ⇒ᴱ (e' , eˇ , M') →
             ((e , es) , M) ⇒ᵀ ((e' , ¿-case (_∷ es) es eˇ) , M')

  -- Continue to the tail threads
  redᵀ-tl :  ((e' , es) , M) ⇒ᵀ ((e'' , es') , M') →
             ((e , e' ∷ es) , M) ⇒ᵀ ((e , e'' ∷ es') , M')

-- ⇐ᴷᴿ, ⇐ᴱ :  Flipped ⇒ᴷᴿ, ⇒ᴱ

_⇐ᴷᴿ_ :  Expr ∞ T × ¿ Expr ∞ (◸ ⊤) × Mem →  Ktxred T × Mem →  Set₁
_⇐ᴷᴿ_ =  flip _⇒ᴷᴿ_

_⇐ᴱ_ :  Expr ∞ T × ¿ Expr ∞ (◸ ⊤) × Mem →  Expr ∞ T × Mem →  Set₁
_⇐ᴱ_ =  flip _⇒ᴱ_

-- ⇒ᴷᴿ∑ :  A contex-redex pair is reducible

infix 4 _⇒ᴷᴿ∑
_⇒ᴷᴿ∑ :  ∀{T} →  Ktxred T × Mem →  Set₁
redM ⇒ᴷᴿ∑ =  ∑ e'M' , redM ⇒ᴷᴿ e'M'

--------------------------------------------------------------------------------
-- ⇒ᵀ* :  Finite reduction sequence

infix 4 _⇒ᵀ*_

data  _⇒ᵀ*_ :  Thrpool T × Mem →  Thrpool T × Mem →  Set₁  where

  -- End reduction
  ⇒ᵀ*-refl :  (tp , M) ⇒ᵀ* (tp , M)

  -- Continue reduction
  ⇒ᵀ*-step :  (tp , M) ⇒ᵀ (tp' , M') →  (tp' , M') ⇒ᵀ* (tp'' , M'') →
              (tp , M) ⇒ᵀ* (tp'' , M'')
