--------------------------------------------------------------------------------
-- Interpreting persistent save tokens
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Save.Pers where

open import Base.Size using (∞)
open import Base.Func using (_$_)
open import Base.Nat using (ℕ)
open import Base.Prod using (_,_)
open import Syho.Logic.Prop using (Prop'; _∧_; Basic)
open import Syho.Logic.Judg using (_⊢[_]_)
open import Syho.Model.RA using (RA)
open import Syho.Model.RA.Glob using (GlobRA; Glob; module ModGlobI;
  module ModSave□; module ModAgᴾ)
open RA GlobRA using (_≈_; ⌞_⌟; _◇˜_)
open ModGlobI using (injaᴬ; injaᴬ-cong; injaᴬ-⌞⌟)
open ModSave□ using (injaᶠᵐ; injaᶠᵐ-⌞⌟)
open ModAgᴾ using (ag)
open import Syho.Model.Prop GlobRA using (Propᵒ; _⊨_; ∃₂ᵒ-syntax; ∃₀ᵒ-syntax;
  _∧ᵒ_; ⌜_⌝₂ᵒ; Own)
open import Syho.Model.Basic using (⸨_⸩ᴮ)

private variable
  i :  ℕ
  P :  Prop' ∞

--------------------------------------------------------------------------------
-- Interpreting persistent save tokens

lineˢ□ :  ℕ →  Prop' ∞ →  Glob
lineˢ□ i P =  injaᴬ 1 $ injaᶠᵐ i $ ag P

Save□ᵒ :  Prop' ∞ →  Propᵒ
Save□ᵒ P =  ∃₂ᵒ P' , ∃₂ᵒ Q , ∃₂ᵒ BaQ , ∃₀ᵒ i ,
  ⌜ Q ∧ P' ⊢[ ∞ ] P ⌝₂ᵒ  ∧ᵒ  ⸨ Q ⸩ᴮ {{ BaQ }}  ∧ᵒ  Own (lineˢ□ i P')

abstract

  lineˢ□-⌞⌟ :  ⌞ lineˢ□ i P ⌟ ≈ lineˢ□ i P
  lineˢ□-⌞⌟ =  injaᴬ-⌞⌟ ◇˜ injaᴬ-cong injaᶠᵐ-⌞⌟
