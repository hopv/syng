------------------------------------------------------------------------
-- Level-polymorphic n-element set
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Level using (Level)
module Base.NElem where

private variable
  ℓ ℓ' : Level

-- 2-element
data ⟨2⟩ {ℓ} : Set ℓ where
  0₂ 1₂ : ⟨2⟩

-- 1-element
record ⟨1⟩ {ℓ} : Set ℓ where
  instance constructor 0₁

-- 0-element
data ⟨0⟩ {ℓ} : Set ℓ where

-- Function from ⟨2⟩
2-ary : ∀{F : ⟨2⟩ {ℓ} → Set ℓ'} → F 0₂ → F 1₂ → ∀ <2 → F <2
2-ary a _ 0₂ = a
2-ary _ b 1₂ = b

-- Function from ⟨0⟩
0-ary : ∀{F : ⟨0⟩ {ℓ} → Set ℓ'} → ∀ <0 → F <0
0-ary ()
