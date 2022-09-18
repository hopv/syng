--------------------------------------------------------------------------------
-- Example
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Lang.Example where

open import Base.Func using (_$_)
open import Base.Few using (⊤; ¬_)
open import Base.Eq using (_≡_; refl)
open import Base.Size using (Size; ∞; !)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_)
open import Base.Nat using (ℕ; ṡ_; _+_)
open import Syho.Lang.Expr using (Addr; addr; Type; ◸_; _↷_; Expr; ▶_; ∇_; nd;
  λ-syntax; _◁_; _⁏_; let-syntax; 🞰_; _←_; free)
open import Syho.Lang.Reduce using (Mem; nd⇒; ▶⇒; ◁⇒; redᴷᴿ; _⇒ᴱ_; redᴱ)

private variable
  ι :  Size
  T :  Type
  e :  Expr ∞ T
  M M' :  Mem
  n :  ℕ

--------------------------------------------------------------------------------
-- Constructing Expr

-- ▶ ▶ ▶ …

loop :  Expr ι (◸ ⊤)
loop =  ▶ λ{ .! → loop }

-- Some stuck expression

stuck :  Expr ι (◸ ⊤)
stuck =  free $ ∇ addr 42 42

-- Just add two natural-number arguments

plus :  Expr ι $ (ℕ × ℕ) ↷ ◸ ℕ
plus =  λ' (m , n) ,  ∇ (m + n)

-- plus on 3 & 4

plus◁3,4 :  Expr ι $ ◸ ℕ
plus◁3,4 =  plus ◁ ∇ (3 , 4)

-- Non-deterministic natural number

ndnat :  Expr ι $ ◸ ℕ
ndnat =  nd

-- Decrement the natural number at the address until it becomes zero

decrloop :  Addr →  Expr ι $ ◸ ⊤
decrloop' :  Addr →  ℕ →  Expr ι $ ◸ ⊤

decrloop θ =  let' n := 🞰 ∇ θ in' decrloop' θ n

decrloop' θ 0 =  ∇ _
decrloop' θ (ṡ n) =  ∇ θ ← ∇ n ⁏ ▶ λ{ .! → decrloop θ }

-- decrloop with initialization with ndnat

nddecrloop :  Addr →  Expr ι $ ◸ ⊤
nddecrloop θ =  ∇ θ ← ndnat ⁏ decrloop θ

--------------------------------------------------------------------------------
-- Constructing Red

abstract

  -- Reduce loop

  loop-red :  (loop , M) ⇒ᴱ (loop , M)
  loop-red =  redᴱ refl $ redᴷᴿ ▶⇒

  -- Reduce plus◁3,4

  plus◁3,4-red :  (plus◁3,4 , M) ⇒ᴱ (∇ 7 , M)
  plus◁3,4-red =  redᴱ refl $ redᴷᴿ ◁⇒

  -- Reduce ndnat

  ndnat-red :  (ndnat , M) ⇒ᴱ (∇ n , M)
  ndnat-red =  redᴱ refl $ redᴷᴿ $ nd⇒ _

--------------------------------------------------------------------------------
-- Destructing Red

abstract

  -- Invert reduction on loop

  loop-red-inv :  (loop , M) ⇒ᴱ (e , M') →  (e , M') ≡ (loop , M)
  loop-red-inv (redᴱ refl (redᴷᴿ ▶⇒)) =  refl

  -- stuck can't be reduced (it's stuck!)

  stuck-no-red :  ¬ (stuck , M) ⇒ᴱ (e , M')
  stuck-no-red (redᴱ refl (redᴷᴿ r⇒))  with r⇒
  … | ()

  -- Invert reduction on plus◁3,4

  plus◁3,4-red-inv :  (plus◁3,4 , M) ⇒ᴱ (e , M') →  (e , M') ≡ (∇ 7 , M)
  plus◁3,4-red-inv (redᴱ refl (redᴷᴿ ◁⇒)) =  refl

  -- Invert reduction on ndnat

  ndnat-red-inv :  (ndnat , M) ⇒ᴱ (e , M') →  ∑ n , (e , M') ≡ (∇ n , M)
  ndnat-red-inv (redᴱ refl (redᴷᴿ (nd⇒ _))) =  -, refl
