--------------------------------------------------------------------------------
-- Interpreting persistent save tokens
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Model.Save.Pers (ℓ : Level) where

open import Base.Size using (∞)
open import Base.Func using (_$_)
open import Base.Nat using (ℕ)
open import Base.Level using (Up; ↑_)
open import Base.Prod using (_,_)
open import Shog.Logic.Prop ℓ using (Prop'; _∧_; Basic)
open import Shog.Logic.Judg ℓ using (_⊢[_]_)
open import Shog.Model.RA using (RA)
open import Shog.Model.RA.Glob ℓ using (GlobRA; Glob; module ModGlobI;
  module ModSave□; module ModAgᴾ)
open RA GlobRA using (_≈_; ⌞_⌟; _◇˜_)
open ModGlobI using (injaᴬ; injaᴬ-cong; injaᴬ-⌞⌟)
open ModSave□ using (injaᶠᵐ; injaᶠᵐ-⌞⌟)
open ModAgᴾ using (ag)
open import Shog.Model.Prop GlobRA using (Propᵒ; _⊨_; ∃^-syntax; ∃^∈-syntax;
  _∧ᵒ_; ⌜_⌝^; Own)
open import Shog.Model.Basic ℓ using (⸨_⸩ᴮ)

private variable
  i :  ℕ
  P :  Prop' ∞

--------------------------------------------------------------------------------
-- Interpreting persistent save tokens

lineˢ□ :  ℕ →  Prop' ∞ →  Glob
lineˢ□ i P =  injaᴬ 1 $ injaᶠᵐ i $ ag P

Save□ᵒ :  Prop' ∞ →  Propᵒ
Save□ᵒ P =  ∃^ P' , ∃^ Q , ∃^ BaQ , ∃^ (↑ i) ∈ Up _ ,
  ⌜ Q ∧ P' ⊢[ ∞ ] P ⌝^  ∧ᵒ  ⸨ Q ⸩ᴮ {{ BaQ }}  ∧ᵒ  Own (lineˢ□ i P')

abstract

  lineˢ□-⌞⌟ :  ⌞ lineˢ□ i P ⌟ ≈ lineˢ□ i P
  lineˢ□-⌞⌟ =  injaᴬ-⌞⌟ ◇˜ injaᴬ-cong injaᶠᵐ-⌞⌟