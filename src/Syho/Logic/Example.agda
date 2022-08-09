--------------------------------------------------------------------------------
-- Example
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Example where

open import Base.Level using (↑_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (!)
open import Base.Func using (_$_)
open import Base.Eq using (_≡_; refl)
open import Syho.Logic.Prop using (⊤'; ⊥'; ⌜_⌝₀)
open import Syho.Logic.Core using (⌜⌝₀-intro)
open import Syho.Logic.Hor using (_⊢[_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ_; hor-val; horᴾ-▶;
  hor-◁)

open import Syho.Lang.Example using (loop; plus◁3'4)

private variable
  ι :  Size

abstract

  loop-⊥ :  ⊤' ⊢[ ι ]⟨ loop ⟩ᴾ λ _ → ⊥'
  loop-⊥ =  horᴾ-▶ λ{ .! → loop-⊥ }

  plus◁3'4-7 :  ⊤' ⊢[ ∞ ]⟨ plus◁3'4 ⟩ᵀ λ (↑ n) → ⌜ n ≡ 7 ⌝₀
  plus◁3'4-7 =  hor-◁ $ hor-val $ ⌜⌝₀-intro refl
