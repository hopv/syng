{-# OPTIONS --sized-types #-}

module Shog.Logic.Prop where

open import Size
open import Level
open import Data.Bool.Base
open import Codata.Sized.Thunk

open import Shog.Util

-- syntax for a proposition in Shog
data Propₛ ℓ (i : Size) : Set (suc ℓ) where
  -- universal/existential quantification
  ∀! ∃! : (A : Set ℓ) → (A → Propₛ ℓ i) → Propₛ ℓ i
  -- implication
  _→ₛ_ : Propₛ ℓ i → Propₛ ℓ i → Propₛ ℓ i
  -- lifting a pure proposition
  ⌜_⌝ : Set ℓ → Propₛ ℓ i
  -- separating conjunction
  _∗_ _-∗_ : Propₛ ℓ i → Propₛ ℓ i → Propₛ ℓ i
  -- persistence and update modalities
  □ |=> : Propₛ ℓ i → Propₛ ℓ i
  -- save token
  save : Bool → Thunk (Propₛ ℓ) i → Propₛ ℓ i

infix 3 ∀! ∃!
syntax ∀! A (λ x → P) = ∀ₛ x ∈ A , P
syntax ∃! A (λ x → P) = ∃ₛ x ∈ A , P

∀!' ∃!' : ∀ {ℓ i} {A : Set ℓ} → (A → Propₛ ℓ i) → Propₛ ℓ i
∀!' = ∀! _
∃!' = ∃! _
infix 3 ∀!' ∃!'
syntax ∀!' (λ x → P) = ∀ₛ x , P
syntax ∃!' (λ x → P) = ∃ₛ x , P

infixr 5 _→ₛ_ _-∗_
infixr 7 _∗_

-- deriving conjunction ∧ / disjunction ∨ and top ⊤ / bottom ⊥
-- from universal/existential quantification ∀ / ∃

private variable
  ℓ : Level
  i : Size

infixr 7 _∧ₛ_
infixr 6 _∨ₛ_

_∧ₛ_ _∨ₛ_ : Propₛ ℓ i → Propₛ ℓ i → Propₛ ℓ i
P ∧ₛ Q = ∀!' (binary P Q)
P ∨ₛ Q = ∃!' (binary P Q)

⊤ₛ ⊥ₛ : Propₛ ℓ i
⊤ₛ = ∀! _ nullary
⊥ₛ = ∃! _ nullary
