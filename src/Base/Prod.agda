--------------------------------------------------------------------------------
-- Products
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Prod where

open import Base.Level using (Level; _⊔ˡ_)

open import Agda.Builtin.Sigma public using (Σ; _,_)
  renaming (fst to proj₀; snd to proj₁)

private variable
  ℓA ℓB ℓF : Level

infix 2 Σ-syntax
Σ-syntax : ∀ (A : Set ℓA) → (A → Set ℓF) → Set (ℓA ⊔ˡ ℓF)
Σ-syntax = Σ
syntax Σ-syntax A (λ a → b) = Σ[ a ∈ A ] b

infixr 2 _×_
_×_ : Set ℓA → Set ℓB → Set (ℓA ⊔ˡ ℓB)
A × B = Σ[ _ ∈ A ] B

∃ : ∀ {A : Set ℓA} → (A → Set ℓF) → Set (ℓA ⊔ˡ ℓF)
∃ = Σ _

infix 2 ∃-syntax
∃-syntax : ∀ {A : Set ℓA} → (A → Set ℓF) → Set (ℓA ⊔ˡ ℓF)
∃-syntax = ∃
syntax ∃-syntax (λ a → b) = ∃[ a ] b
