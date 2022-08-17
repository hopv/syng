--------------------------------------------------------------------------------
-- Example
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Example where

open import Base.Size using (Size; ∞)
open import Base.Thunk using (!)
open import Base.Func using (_$_)
open import Base.Eq using (_≡_; refl)
open import Base.Nat using (ℕ)
open import Syho.Lang.Expr using (λᵛ-syntax)
open import Syho.Logic.Prop using (Prop'; ⊤'; ⊥'; ⌜_⌝₀; □_; ○_)
open import Syho.Logic.Core using (_»_; ∧-elimˡ; ⌜⌝₀-intro; →-intro)
open import Syho.Logic.Supd using (_⊢[_][_]=>>_)
open import Syho.Logic.Ind using (□○-alloc-rec)
open import Syho.Logic.Hor using (_⊢[_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ[_]_; hor-val; horᴾ-▶;
  hor-◁)

open import Syho.Lang.Example using (loop; plus◁3,4)

private variable
  ι :  Size
  i :  ℕ

-- □ ○ □ ○ □ ○ ...

□○-loop :  Prop' ι
□○-loop =  □ ○ λ{ .! → □○-loop }

abstract

  -- Get □ ○ □ ○ □ ○ ... for free

  □○-loop-alloc :  ⊤' ⊢[ ι ][ i ]=>> □○-loop
  □○-loop-alloc =  →-intro ∧-elimˡ » □○-alloc-rec

  -- Get ⊥' after ▶ ▶ ▶ ... under partial Hoare triple

  loop-⊥ :  ⊤' ⊢[ ι ]⟨ loop ⟩ᴾ λ _ → ⊥'
  loop-⊥ =  horᴾ-▶ λ{ .! → loop-⊥ }

  -- Execute plus ◁ ∇ (3 , 4)

  plus◁3,4-7 :  ⊤' ⊢[ ∞ ]⟨ plus◁3,4 ⟩ᵀ[ 0 ] λᵛ n , ⌜ n ≡ 7 ⌝₀
  plus◁3,4-7 =  hor-◁ $ hor-val $ ⌜⌝₀-intro refl
