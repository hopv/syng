--------------------------------------------------------------------------------
-- Sigma type / Product
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Prod where

open import Base.Level using (Level; _⊔ˡ_)

--------------------------------------------------------------------------------
-- Sigma type
open import Agda.Builtin.Sigma public using (_,_)
  renaming (Σ to Σ˙; fst to proj₀; snd to proj₁)

private variable
  ℓA ℓB ℓF : Level

-- Syntax for Σ
Σ∈-syntax : ∀ (A : Set ℓA) → (A → Set ℓF) → Set (ℓA ⊔ˡ ℓF)
Σ∈-syntax = Σ˙
syntax Σ∈-syntax A (λ a → b) = Σ a ∈ A , b

infix 2 Σ-syntax
Σ-syntax : ∀ {A : Set ℓA} → (A → Set ℓF) → Set (ℓA ⊔ˡ ℓF)
Σ-syntax = Σ˙ _
syntax Σ-syntax (λ a → B) = Σ a , B

-- Product
infixr 2 _×_
_×_ : Set ℓA → Set ℓB → Set (ℓA ⊔ˡ ℓB)
A × B = Σ _ ∈ A , B
