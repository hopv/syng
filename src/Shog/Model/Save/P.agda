--------------------------------------------------------------------------------
-- Interpreting save tokens
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Model.Save.P (ℓ : Level) where

open import Base.Size using (∞)
open import Base.Func using (_$_)
open import Base.Nat using (ℕ)
open import Base.Level using (Up; ↑_)
open import Base.Prod using (_,_)
open import Shog.Logic.Prop ℓ using (Prop'; _∧_; Basic)
open import Shog.Logic.Judg ℓ using (_⊢[_]_)
open import Shog.Model.RA using (RA)
open import Shog.Model.RA.Glob ℓ using (Globᴿᴬ; Glob; module ModGlobI;
  module ModSave□; module ModAgᴾ)
open RA Globᴿᴬ using (_≈_; ⌞_⌟; _◇˜_)
open ModGlobI using (injᴬ; injᴬ-cong; injᴬ-⌞⌟)
open ModSave□ using (injᶠ; injᶠ-⌞⌟)
open ModAgᴾ using (ag)
open import Shog.Model.Prop Globᴿᴬ using (Propᵒ; _⊨_; ∃^-syntax; ∃^∈-syntax;
  _∧ᵒ_; ⌜_⌝^; own)
open import Shog.Model.Basic ℓ using ([|_|]ᴮ)

private variable
  i :  ℕ
  P :  Prop' ∞

--------------------------------------------------------------------------------
-- Interpreting persistent save tokens

lineˢ□ :  ℕ →  Prop' ∞ →  Glob
lineˢ□ i P =  injᴬ 1 $ injᶠ i $ ag P

save□ᵒ :  Prop' ∞ →  Propᵒ
save□ᵒ P =  ∃^ P' , ∃^ Q , ∃^ BaQ , ∃^ (↑ i) ∈ Up _ ,
  ⌜ Q ∧ P' ⊢[ ∞ ] P ⌝^  ∧ᵒ  [| Q |]ᴮ {{ BaQ }}  ∧ᵒ  own (lineˢ□ i P')

abstract

  lineˢ□-⌞⌟ :  ⌞ lineˢ□ i P ⌟ ≈ lineˢ□ i P
  lineˢ□-⌞⌟ =  injᴬ-⌞⌟ ◇˜ injᴬ-cong injᶠ-⌞⌟
