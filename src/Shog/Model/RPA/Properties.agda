----------------------------------------------------------------------
-- Properties on RPA
----------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Shog.Model.RPA

module Shog.Model.RPA.Properties {ℓ ℓ≤ ℓ✓} (A : RPA ℓ ℓ≤ ℓ✓) where
open RPA A

open import Level using (Level; _⊔_; suc)
open import Size using (Size; ∞)

private variable
  a a' b b' c d : ⌞_⌟

∙-mono₁ : a ≤ b → c ∙ a ≤ c ∙ b
∙-mono₁ a≤b = ∙-comm »ʳ ∙-mono₀ a≤b »ʳ ∙-comm

∙-mono : a ≤ b → c ≤ d → a ∙ c ≤ b ∙ d
∙-mono a≤b c≤d = ∙-mono₀ a≤b »ʳ ∙-mono₁ c≤d

∙-assoc₁ : a ∙ (b ∙ c) ≤ (a ∙ b) ∙ c
∙-assoc₁ = ∙-comm »ʳ ∙-mono₀ ∙-comm »ʳ ∙-assoc₀ »ʳ ∙-comm »ʳ ∙-mono₀ ∙-comm
