----------------------------------------------------------------------
-- Syntax for the Shog proposition
----------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Logic.Prop where

open import Size
open import Level
open import Data.Bool.Base
open import Codata.Sized.Thunk

open import Shog.Util

----------------------------------------------------------------------
-- Syntax for the Shog proposition: Propₛ ℓ i

data Propₛ ℓ (i : Size) : Set (suc ℓ) where
  -- universal/existential quantification
  ∀^ ∃^ : (A : Set ℓ) → (A → Propₛ ℓ i) → Propₛ ℓ i
  -- implication
  _→ₛ_ : Propₛ ℓ i → Propₛ ℓ i → Propₛ ℓ i
  -- separating conjunction / magic wand
  _∗_ _-∗_ : Propₛ ℓ i → Propₛ ℓ i → Propₛ ℓ i
  -- persistence modality / update modality
  □ |=> : Propₛ ℓ i → Propₛ ℓ i
  -- save token
  save : Bool → Thunk (Propₛ ℓ) i → Propₛ ℓ i

infix 3 ∀^ ∃^
syntax ∀^ A (λ x → P) = ∀ₛ x ∈ A , P
syntax ∃^ A (λ x → P) = ∃ₛ x ∈ A , P

∀^' ∃^' : ∀ {ℓ i} {A : Set ℓ} → (A → Propₛ ℓ i) → Propₛ ℓ i
∀^' = ∀^ _
∃^' = ∃^ _
infix 3 ∀^' ∃^'
syntax ∀^' (λ x → P) = ∀ₛ x , P
syntax ∃^' (λ x → P) = ∃ₛ x , P

infixr 5 _→ₛ_ _-∗_
infixr 7 _∗_

----------------------------------------------------------------------
-- Derived propositions

private variable
  ℓ : Level
  i : Size

-- Deriving from universal/existential quantification ∀ₛ / ∃ₛ

-- -- Conjunction ∧ₛ / Disjunction ∨ₛ

infixr 7 _∧ₛ_
infixr 6 _∨ₛ_

_∧ₛ_ _∨ₛ_ : Propₛ ℓ i → Propₛ ℓ i → Propₛ ℓ i
P ∧ₛ Q = ∀^' (binary P Q)
P ∨ₛ Q = ∃^' (binary P Q)

-- -- Truth ⊤ₛ / Falsehood ⊥ₛ

⊤ₛ ⊥ₛ : Propₛ ℓ i
⊤ₛ = ∀^ _ nullary
⊥ₛ = ∃^ _ nullary

-- Set embedding

⌜_⌝ : Set ℓ → Propₛ ℓ i
⌜ A ⌝ = ∃^ A (λ _ → ⊤ₛ)
