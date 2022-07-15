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
open import Shog.Lang.Reduce ℓ using (Mem; ▶-red; ◁-red; _⇒ᴱ_; redᴱ)

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

abstract

  loop-red :  (loop , M) ⇒ᴱ (loop , M)
  loop-red =  redᴱ refl ▶-red

  plus◁3'4-red :  (plus◁3'4 , M) ⇒ᴱ (∇ ↑ 7 , M)
  plus◁3'4-red =  redᴱ refl ◁-red

--------------------------------------------------------------------------------
-- Destructing Red

abstract

  loop-red-inv :  (loop , M) ⇒ᴱ (e , M') →  (e , M') ≡ (loop , M)
  loop-red-inv (redᴱ refl ▶-red) =  refl

  stuck-no-red :  ¬ (stuck , M) ⇒ᴱ (e , M')
  stuck-no-red (redᴱ refl r⇒)  with r⇒
  ... | ()

  plus◁3'4-red-inv :  (plus◁3'4 , M) ⇒ᴱ (e , M') →  (e , M') ≡ (∇ ↑ 7 , M)
  plus◁3'4-red-inv (redᴱ refl ◁-red) =  refl
