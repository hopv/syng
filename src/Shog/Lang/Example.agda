--------------------------------------------------------------------------------
-- Example
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Lang.Example where

open import Base.Size using (Size; ∞)
open import Base.Thunk using (!)
open import Base.Func using (_$_)
open import Base.Few using (⊤; ¬_)
open import Base.Eq using (_≡_; refl)
open import Base.Prod using (∑-syntax; _×_; _,_)
open import Base.Nat using (ℕ; _+_)
open import Shog.Lang.Expr using (Addr; addr; Type; ◸_; _→*_; Expr; ▶_; ∇_; nd;
  _◁_; free; λ-syntax)
open import Shog.Lang.Reduce using (Mem; nd-red; ▶-red; ◁-red; _⇒ᴱ_; redᴱ)

private variable
  ι :  Size
  T :  Type
  e :  Expr ∞ T
  M M' :  Mem
  n :  ℕ

--------------------------------------------------------------------------------
-- Constructing Expr

loop :  Expr ι (◸ ⊤)
loop =  ▶ λ{ .! → loop }

stuck :  Expr ι (◸ ⊤)
stuck =  free $ ∇ addr 42 42

plus :  Expr ι $ (ℕ × ℕ) →* ◸ ℕ
plus =  λ' (m , n) ,  ∇ (m + n)

plus◁3'4 :  Expr ι $ ◸ ℕ
plus◁3'4 =  plus ◁ ∇ (3 , 4)

ndnat :  Expr ι $ ◸ ℕ
ndnat =  nd

--------------------------------------------------------------------------------
-- Constructing Red

abstract

  loop-red :  (loop , M) ⇒ᴱ (loop , M)
  loop-red =  redᴱ refl ▶-red

  plus◁3'4-red :  (plus◁3'4 , M) ⇒ᴱ (∇ 7 , M)
  plus◁3'4-red =  redᴱ refl ◁-red

  ndnat-red :  (ndnat , M) ⇒ᴱ (∇ n , M)
  ndnat-red =  redᴱ refl (nd-red _)

--------------------------------------------------------------------------------
-- Destructing Red

abstract

  loop-red-inv :  (loop , M) ⇒ᴱ (e , M') →  (e , M') ≡ (loop , M)
  loop-red-inv (redᴱ refl ▶-red) =  refl

  stuck-no-red :  ¬ (stuck , M) ⇒ᴱ (e , M')
  stuck-no-red (redᴱ refl r⇒)  with r⇒
  ... | ()

  plus◁3'4-red-inv :  (plus◁3'4 , M) ⇒ᴱ (e , M') →  (e , M') ≡ (∇ 7 , M)
  plus◁3'4-red-inv (redᴱ refl ◁-red) =  refl

  ndnat-red-inv :  (ndnat , M) ⇒ᴱ (e , M') →  ∑ n , (e , M') ≡ (∇ n , M)
  ndnat-red-inv (redᴱ refl (nd-red _)) =  _ , refl
