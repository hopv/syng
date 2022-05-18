--------------------------------------------------------------------------------
-- On FracAgRA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Setoid using (Setoid)
module Shog.Model.RA.FracAg.More {ℓ ℓ≈} {S : Setoid ℓ ℓ≈} where
open Setoid S using (_≈_) renaming (Car to A)

open import Base.RatPos using (ℚ⁺; _≤1ᴿ⁺; 1ᴿ⁺; 1≤1ᴿ⁺; ?+1-not-≤1ᴿ⁺)
open import Base.List.Set S using (homo-[?]; homo-agree)
open import Base.Prod using (_,_)
open import Base.Few using (absurd)
open import Base.Func using (_$_)
open import Shog.Model.RA using (RA)
open import Shog.Model.RA.FracAg S using (FracAgRA; ⟨_⟩ᶠ_; ⟨_⟩ᶠᴸ_; εᶠ)
open RA FracAgRA using (_∙_; ✓_; _↝_)

private variable
  p q :  ℚ⁺
  a b :  A

abstract

  -- ⟨ p ⟩ᶠ a is valid for p ≤1ᴿ⁺

  ✓-⟨⟩ᶠ :  p ≤1ᴿ⁺ →  ✓ ⟨ p ⟩ᶠ a
  ✓-⟨⟩ᶠ p≤1 =  p≤1 , homo-[?]

  -- ⟨ 1ᴿ⁺ ⟩ᶠ a is valid

  ✓-⟨1⟩ᶠ :  ✓ ⟨ 1ᴿ⁺ ⟩ᶠ a
  ✓-⟨1⟩ᶠ =  ✓-⟨⟩ᶠ 1≤1ᴿ⁺

  -- Agreement

  agreeᶠ :  ✓ ⟨ p ⟩ᶠ a ∙ ⟨ q ⟩ᶠ b →  a ≈ b
  agreeᶠ (_ , homo'ab) =  homo-agree homo'ab

  -- Update

  updateᶠ :  ⟨ 1ᴿ⁺ ⟩ᶠ a ↝ ⟨ 1ᴿ⁺ ⟩ᶠ b
  updateᶠ εᶠ _ =  ✓-⟨1⟩ᶠ
  updateᶠ (⟨ p ⟩ᶠᴸ _) (p+1≤1 , _) =  absurd $ ?+1-not-≤1ᴿ⁺ {p} p+1≤1
