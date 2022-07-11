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
open import Base.Few using (⊤; ¬_)
open import Base.Eq using (_≡_; refl)
open import Base.Prod using (_×_; _,_)
open import Base.Nat using (ℕ; _+_)
open import Shog.Lang.Expr ℓ using (Addr; addr; Type; ◸_; _→*_; Expr; ▶_; ∇_;
  _◁_; free; λ-syntax)
open import Shog.Lang.Reduce ℓ using (Mem; Red; ▶-red; ◁-red)

private variable
  ι :  Size
  T :  Type
  e :  Expr ∞ T
  M M' :  Mem

--------------------------------------------------------------------------------
-- Constructing Expr

loop :  Expr ι (◸ ⊤)
loop =  ▶ λ{ .! → loop }

stuck :  Expr ι (◸ ⊤)
stuck =  free $ ∇ ↑ addr 42 42

plus :  Expr ι $ Up (ℕ × ℕ) →* ◸ Up ℕ
plus =  λ' (↑ (m , n)) ,  ∇ ↑ (m + n)

plus◁3'4 :  Expr ι $ ◸ Up ℕ
plus◁3'4 =  plus ◁ ∇ ↑ (3 , 4)

--------------------------------------------------------------------------------
-- Constructing Red

loop-red :  Red loop M loop M
loop-red =  ▶-red

plus◁3'4-red :  Red plus◁3'4 M (∇ ↑ 7) M
plus◁3'4-red =  ◁-red

--------------------------------------------------------------------------------
-- Destructing Red

loop-red-inv :  Red loop M e M' →  (e , M') ≡ (loop , M)
loop-red-inv ▶-red =  refl

stuck-no-red :  ¬ Red stuck M e M'
stuck-no-red ()

plus◁3'4-red-inv :  Red plus◁3'4 M e M' →  (e , M') ≡ (∇ ↑ 7 , M)
plus◁3'4-red-inv ◁-red =  refl
