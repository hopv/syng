{-# OPTIONS --sized-types #-}

module Shog.Logic.Prop where

open import Size
open import Level
open import Data.Bool
open import Codata.Sized.Thunk
open import Shog.Util

-- syntax for a proposition in Shog
data SProp ℓ (i : Size) : Set (suc ℓ) where
  -- universal/existential quantification
  ∀! ∃! : (A : Set ℓ) → (A → SProp ℓ i) → SProp ℓ i
  -- implication
  _→'_ : SProp ℓ i → SProp ℓ i → SProp ℓ i
  -- lifting a pure proposition
  ⌈_⌉ : Set ℓ → SProp ℓ i
  -- separating conjunction
  _∗_ _-∗_ : SProp ℓ i → SProp ℓ i → SProp ℓ i
  -- update and persistence modalities
  |=> □ : SProp ℓ i → SProp ℓ i
  -- save token
  save : Bool → Thunk (SProp ℓ) i → SProp ℓ i

infix 0 ∀! ∃!
syntax ∀! A (λ x → P) = ∀' x ∈ A , P
syntax ∃! A (λ x → P) = ∃' x ∈ A , P

infixr 5 _→'_ _-∗_
infixr 7 _∗_

-- deriving conjunction ∧ / disjunction ∨ and top ⊤ / bottom ⊥
-- from universal/existential quantification ∀ / ∃

private variable
  ℓ : Level
  i : Size

infixr 7 _∧'_
infixr 6 _∨'_

_∧'_ _∨'_ : SProp ℓ i → SProp ℓ i → SProp ℓ i
P ∧' Q = ∀! _ (binary P Q)
P ∨' Q = ∃! _ (binary P Q)

⊤' ⊥' : SProp ℓ i
⊤' = ∀! _ nullary
⊥' = ∃! _ nullary
