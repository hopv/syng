{-# OPTIONS --sized-types #-}

module Logic.Prop where

open import Size
open import Level
open import Data.Empty
open import Data.Bool
open import Codata.Sized.Thunk

-- syntax for a proposition in Shog
data SProp {ℓ} (i : Size) : Set (suc ℓ) where
  -- universal/existential quantification
  `forall `exists : {A : Set ℓ} → (A → SProp {ℓ} i) → SProp i
  -- implication
  _`⇒_ : SProp {ℓ} i → SProp {ℓ} i → SProp i
  -- lifting a pure proposition
  ⌈_⌉ : Set ℓ → SProp i
  -- separating conjunction
  _∗_ _-∗_ : SProp {ℓ} i → SProp {ℓ} i → SProp i
  -- update and persistence modalities
  |=> □ : SProp {ℓ} i → SProp i
  -- save token
  save : Bool → Thunk (SProp {ℓ}) i → SProp i

infixr 7 _∗_
infixr 5 _-∗_

-- syntax for universal/existential quantification

infix 0 `forall `exists
syntax `forall (λ x → P) = `∀ x `→ P
syntax `exists (λ x → P) = `∃ x `→ P

`forall-dom `exists-dom :
  ∀ {ℓ i} → (A : Set ℓ) → (A → SProp {ℓ} i) → SProp i
`forall-dom A = `forall
`exists-dom A = `exists
infix 0 `forall-dom `exists-dom
syntax `forall-dom A (λ x → P) = `∀ x ∈ A `→ P
syntax `exists-dom A (λ x → P) = `∃ x ∈ A `→ P

-- conjunction and disjunction as
-- binary universal/existential quantification

infixr 7 _`∧_
infixr 6 _`∨_

_`∧_ _`∨_ : ∀{i} → SProp i → SProp i → SProp i
P `∧ Q = `∀ b `→ if b then P else Q
P `∨ Q = `∃ b `→ if b then P else Q

-- truth and falsehood as
-- nullary universal/existential quantification

`⊤ `⊥ : ∀{i} → SProp i
`⊤ = `forall ⊥-elim
`⊥ = `exists ⊥-elim
