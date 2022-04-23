------------------------------------------------------------------------
-- Level-polymorphic n-element set
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
module Shog.Base.NElem (ℓ : Level) where

private variable
  ℓ' : Level

-- 2-element
data ⟨2⟩ : Set ℓ where
  0₂ 1₂ : ⟨2⟩

-- 1-element
record ⟨1⟩ : Set ℓ where
  instance constructor 0₁

-- 0-element
data ⟨0⟩ : Set ℓ where

-- Function from ⟨2⟩
2-ary : ∀{F : ⟨2⟩ → Set ℓ'} → F 0₂ → F 1₂ → ∀ <2 → F <2
2-ary a _ 0₂ = a
2-ary _ b 1₂ = b

-- Function from ⟨0⟩
0-ary : ∀{F : ⟨0⟩ → Set ℓ'} → ∀ <0 → F <0
0-ary ()
