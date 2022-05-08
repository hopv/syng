--------------------------------------------------------------------------------
-- Level-polymorphic 2/1/0-element set
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Level using (Level; 0ˡ)
module Base.Few where

private variable
  ℓ ℓA ℓF : Level
  A : Set ℓA

--------------------------------------------------------------------------------
-- ⟨2⟩: 2-element set / Doubleton

data ⟨2⟩ {ℓ} : Set ℓ where
  0₂ 1₂ : ⟨2⟩

-- Function from ⟨2⟩

2-ary : ∀{F : ⟨2⟩ {ℓ} → Set ℓF} → F 0₂ → F 1₂ → ∀ <2 → F <2
2-ary a _ 0₂ = a
2-ary _ b 1₂ = b

--------------------------------------------------------------------------------
-- ⟨1⟩: 1-element set / Singleton

record ⟨1⟩ {ℓ} : Set ℓ where
  instance constructor 0₁

--------------------------------------------------------------------------------
-- ⟨0⟩: 0-element set / Empty

data ⟨0⟩ {ℓ} : Set ℓ where

-- Function from ⟨0⟩

0-ary : ∀{F : ⟨0⟩ {ℓ} → Set ℓF} → ∀ <0 → F <0
0-ary ()

--------------------------------------------------------------------------------
-- ¬: Negation

¬ : Set ℓA → Set ℓA
¬ A = A → ⟨0⟩ {0ˡ}

-- Introducing ¬¬

¬¬-intro : A → ¬ (¬ A)
¬¬-intro a ¬a = ¬a a
