--------------------------------------------------------------------------------
-- Interpreting save tokens
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Model.Save.P (ℓ : Level) where

open import Base.Size using (∞)
open import Base.Func using (_$_)
open import Base.Nat using (ℕ)
open import Base.Level using (↓ˡ_)
open import Base.Prod using (_,_)
open import Shog.Logic.Prop ℓ using (Prop'; _∗_; Basic)
open import Shog.Logic.Judg ℓ using (_⊢[_]_)
open import Shog.Model.RA using (RA)
open import Shog.Model.RA.Glob ℓ using (Globᴿᴬ; Glob; module MAllIᴳ;
  module MFinˢ□; module MAgᴾ)
open RA Globᴿᴬ using (_≈_; ⌞_⌟; _»˜_)
open MAllIᴳ using (injᴬ; injᴬ-cong; injᴬ-⌞⌟)
open MFinˢ□ using (injᶠ; injᶠ-⌞⌟)
open MAgᴾ using (ag)
open import Shog.Model.Prop Globᴿᴬ using (Propᵒ; _⊨_; ∃^-syntax; _∧ᵒ_; ⌜_⌝^;
  own)
open import Shog.Model.Basic ℓ using ([|_|]ᴮ)

private variable
  i :  ℕ
  P :  Prop' ∞

--------------------------------------------------------------------------------
-- Interpreting persistent save tokens

lineˢ□ :  ℕ →  Prop' ∞ →  Glob
lineˢ□ i P =  injᴬ 1 $ injᶠ i $ ag P

save□ᵒ :  Prop' ∞ →  Propᵒ
save□ᵒ P =  ∃^ P' , ∃^ Q , ∃^ BaQ , ∃^ i ,
  ⌜ Q ∗ P' ⊢[ ∞ ] P ⌝^  ∧ᵒ  [| Q |]ᴮ {{ BaQ }}  ∧ᵒ  own (lineˢ□ (↓ˡ i) P')

abstract

  lineˢ□-⌞⌟ :  ⌞ lineˢ□ i P ⌟ ≈ lineˢ□ i P
  lineˢ□-⌞⌟ =  injᴬ-⌞⌟ »˜ injᴬ-cong injᶠ-⌞⌟
