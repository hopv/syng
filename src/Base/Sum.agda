--------------------------------------------------------------------------------
-- Sums
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Sum where

open import Base.Level using (Level; _⊔ˡ_)

private variable
  ℓA ℓB ℓF : Level
  A : Set ℓA
  B : Set ℓB

--------------------------------------------------------------------------------
-- Sum
infixr 1 _⊎_
data _⊎_ (A : Set ℓA) (B : Set ℓB) : Set (ℓA ⊔ˡ ℓB) where
  inj₀ : A → A ⊎ B
  inj₁ : B → A ⊎ B

-- Pattern matching on ⊎
[_,_] : ∀ {F : A ⊎ B → Set ℓF} →
  (∀ a → F (inj₀ a)) → (∀ b → F (inj₁ b)) → ∀ a/b → F a/b
[ f , g ] (inj₀ a) = f a
[ f , g ] (inj₁ b) = g b
