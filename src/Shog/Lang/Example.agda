--------------------------------------------------------------------------------
-- Example
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Lang.Example (ℓ : Level) where

open import Base.Size using (Size; ∞)
open import Base.Level using (Up; ↑_)
open import Base.Thunk using (!)
open import Base.Func using (_$_)
open import Base.Few using (⊤)
open import Base.Eq using (_≡_; refl⁼)
open import Base.Prod using (_×_; _,_)
open import Base.Nat using (ℕ; _+_)
open import Shog.Lang.Expr ℓ using (Type; ◸_; _➔_; Expr; ▶_; ∇_; _◁_; λ-syntax)
open import Shog.Lang.Reduce ℓ using (Mem; Red; ▶-red; ◁-red)

private variable
  ι :  Size
  T :  Type
  e :  Expr ∞ T
  M M' :  Mem

--------------------------------------------------------------------------------
-- Constructing Expr

plus :  Expr ι $ Up (ℕ × ℕ) ➔ ◸ Up ℕ
plus =  λ' (↑ (m , n)) ,  ∇ ↑ (m + n)

plus◁ :  Expr ι $ ◸ Up ℕ
plus◁ =  plus ◁ ∇ ↑ (3 , 4)

loop :  Expr ι (◸ ⊤)
loop =  ▶ λ{ .! → loop }

--------------------------------------------------------------------------------
-- Constructing Red

plus◁-red :  Red plus◁ M (∇ ↑ 7) M
plus◁-red =  ◁-red

loop-red :  Red loop M loop M
loop-red =  ▶-red

--------------------------------------------------------------------------------
-- Destructing Red

plus◁-red-inv :  Red plus◁ M e M' →  (e , M') ≡ ((∇ ↑ 7) , M)
plus◁-red-inv ◁-red =  refl⁼

loop-red-inv :  Red loop M e M' →  (e , M') ≡ (loop , M)
loop-red-inv ▶-red =  refl⁼
