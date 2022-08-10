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
open import Syho.Logic.Prop using (Prop'; ⊤'; ⊥'; ⌜_⌝₀; □_; ○_)
open import Syho.Logic.Core using (_»_; ∧-elimˡ; ⌜⌝₀-intro; →-intro)
open import Syho.Logic.Supd using (_⊢[_]=>>_)
open import Syho.Logic.Ind using (□○-alloc-rec)
open import Syho.Logic.Hor using (_⊢[_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ_; hor-val; horᴾ-▶;
  hor-◁)

open import Syho.Lang.Example using (loop; plus◁3'4)

private variable
  ι :  Size

-- □ ○ □ ○ □ ○ ...

□○-loop :  Prop' ι
□○-loop =  □ ○ λ{ .! → □○-loop }

abstract

  -- We can get □ ○ □ ○ □ ○ ... for free

  □○-loop-alloc :  ⊤' ⊢[ ι ]=>> □○-loop
  □○-loop-alloc =  →-intro ∧-elimˡ » □○-alloc-rec

  loop-⊥ :  ⊤' ⊢[ ι ]⟨ loop ⟩ᴾ λ _ → ⊥'
  loop-⊥ =  horᴾ-▶ λ{ .! → loop-⊥ }

  plus◁3'4-7 :  ⊤' ⊢[ ∞ ]⟨ plus◁3'4 ⟩ᵀ λ (↑ n) → ⌜ n ≡ 7 ⌝₀
  plus◁3'4-7 =  hor-◁ $ hor-val $ ⌜⌝₀-intro refl
