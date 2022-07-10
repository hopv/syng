--------------------------------------------------------------------------------
-- Sigma type / Product
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Prod where

open import Base.Level using (Level; _⌴_)

--------------------------------------------------------------------------------
-- Sigma type

open import Agda.Builtin.Sigma public using (_,_)
  renaming (Σ to ∑˙; fst to proj₀; snd to proj₁)

private variable
  ℓA ℓB ℓF :  Level

-- Syntax for ∑

∑∈-syntax :  ∀ (A : Set ℓA) →  (A → Set ℓF) →  Set (ℓA ⌴ ℓF)
∑∈-syntax =  ∑˙
syntax ∑∈-syntax A (λ a → b) =  ∑ a ∈ A , b

infix 2 ∑-syntax
∑-syntax :  ∀ {A : Set ℓA} →  (A → Set ℓF) →  Set (ℓA ⌴ ℓF)
∑-syntax =  ∑˙ _
syntax ∑-syntax (λ a → B) =  ∑ a , B

--------------------------------------------------------------------------------
-- Product

infixr 2 _×_
_×_ :  Set ℓA →  Set ℓB →  Set (ℓA ⌴ ℓB)
A × B =  ∑ _ ∈ A , B
