--------------------------------------------------------------------------------
-- Example
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Logic.Example (ℓ : Level) where

open import Base.Level using (Up; ↑_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (!)
open import Base.Func using (_$_)
open import Base.Eq using (_≡_; refl)
open import Shog.Logic.Prop ℓ using (⊤'; ⊥'; ⌜_⌝)
open import Shog.Logic.Core ℓ using (⌜⌝-intro)
open import Shog.Logic.Hor ℓ using (_⊢[_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ_; hor-val; hor-▶;
  hor-◁)

open import Shog.Lang.Example ℓ using (loop; plus◁3'4)

private variable
  ι :  Size

abstract

  loop-⊥ :  ⊤' ⊢[ ι ]⟨ loop ⟩ᴾ λ _ → ⊥'
  loop-⊥ =  hor-▶ λ{ .! → loop-⊥ }

  plus◁3'4-7 :  ⊤' ⊢[ ∞ ]⟨ plus◁3'4 ⟩ᵀ λ (↑ ↑ n) → ⌜ Up (n ≡ 7) ⌝
  plus◁3'4-7 =  hor-◁ $ hor-val $ ⌜⌝-intro $ ↑ refl
