--------------------------------------------------------------------------------
-- Sums
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Sum where

open import Base.Level using (Level; _⊔ᴸ_)

private variable
  ΛA ΛB ΛF :  Level
  A :  Set ΛA
  B :  Set ΛB

--------------------------------------------------------------------------------
-- Sum

infixr 0 _⊎_
data  _⊎_ (A : Set ΛA) (B : Set ΛB) :  Set (ΛA ⊔ᴸ ΛB)  where
  inj₀ :  A →  A ⊎ B
  inj₁ :  B →  A ⊎ B

-- Pattern matching on ⊎

⊎-case :  ∀ {F : A ⊎ B → Set ΛF} →
  (∀ a → F (inj₀ a)) →  (∀ b → F (inj₁ b)) →  (a/b : A ⊎ B) →  F a/b
⊎-case f _ (inj₀ a) =  f a
⊎-case _ g (inj₁ b) =  g b

-- Utility patterns

pattern inj₁₀ a =  inj₁ (inj₀ a)
pattern inj₁₁ a =  inj₁ (inj₁ a)
pattern inj₁₁₀ a =  inj₁₁ (inj₀ a)
pattern inj₁₁₁ a =  inj₁₁ (inj₁ a)
