--------------------------------------------------------------------------------
-- Interpreting save tokens
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Model.Save.X (ℓ : Level) where

open import Base.Size using (∞)
open import Base.Func using (_$_)
open import Base.Nat using (ℕ)
open import Base.Level using (↓ˡ_)
open import Shog.Logic.Prop ℓ using (Prop'; _∧_; Basic)
open import Shog.Logic.Judg ℓ using (_⊢[_]_)
open import Shog.Model.RA using (RA)
open import Shog.Model.RA.Glob ℓ using (Globᴿᴬ; Glob; module MAllIᴳ;
  module MFinˢˣ; module MExcᴾ)
open MAllIᴳ using (injᴬ)
open MFinˢˣ using (injᶠ)
open MExcᴾ using (#ˣ_)
open import Shog.Model.Prop Globᴿᴬ using (Propᵒ; _⊨_; ∃^-syntax; _∧ᵒ_; ⌜_⌝^;
  own)
open import Shog.Model.Basic ℓ using ([|_|]ᴮ)

--------------------------------------------------------------------------------
-- Interpreting exclusive save tokens

lineˢˣ :  ℕ →  Prop' ∞ →  Glob
lineˢˣ i P =  injᴬ 0 $ injᶠ i $ #ˣ P

saveˣᵒ :  Prop' ∞ →  Propᵒ
saveˣᵒ P =  ∃^ P' , ∃^ Q , ∃^ BaQ , ∃^ i ,
  ⌜ Q ∧ P' ⊢[ ∞ ] P ⌝^  ∧ᵒ  [| Q |]ᴮ {{ BaQ }}  ∧ᵒ  own (lineˢˣ (↓ˡ i) P')
