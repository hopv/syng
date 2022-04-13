{-# OPTIONS --sized-types #-}

module Shog.Logic.Prop where

open import Size
open import Level
open import Data.Bool
open import Codata.Sized.Thunk

-- syntax for a proposition in Shog
data SProp ℓ (i : Size) : Set (suc ℓ) where
  -- universal/existential quantification
  `forall `exists : {A : Set ℓ} → (A → SProp ℓ i) → SProp ℓ i
  -- implication
  _`⇒_ : SProp ℓ i → SProp ℓ i → SProp ℓ i
  -- lifting a pure proposition
  ⌈_⌉ : Set ℓ → SProp ℓ i
  -- separating conjunction
  _∗_ _-∗_ : SProp ℓ i → SProp ℓ i → SProp ℓ i
  -- update and persistence modalities
  |=> □ : SProp ℓ i → SProp ℓ i
  -- save token
  save : Bool → Thunk (SProp ℓ) i → SProp ℓ i

infixr 7 _∗_
infixr 5 _-∗_

-- syntax for universal/existential quantification

infix 0 `forall `exists
syntax `forall (λ x → P) = `∀ x `→ P
syntax `exists (λ x → P) = `∃ x `→ P

`forall-dom `exists-dom :
  ∀ {ℓ i} → (A : Set ℓ) → (A → SProp ℓ i) → SProp ℓ i
`forall-dom _ = `forall
`exists-dom _ = `exists
infix 0 `forall-dom `exists-dom
syntax `forall-dom A (λ x → P) = `∀ x ∈ A `→ P
syntax `exists-dom A (λ x → P) = `∃ x ∈ A `→ P

-- universe-polymorphic Bool and Empty

data BoolU ℓ : Set ℓ where
  trueU falseU : BoolU ℓ

data EmptyU ℓ : Set ℓ where

-- conjunction and disjunction as
-- binary universal/existential quantification

infixr 7 _`∧_
infixr 6 _`∨_

_`∧_ _`∨_ : ∀{ℓ i} → SProp ℓ i → SProp ℓ i → SProp ℓ i
P `∧ Q = `forall-dom (BoolU _) (λ { trueU → P; falseU → Q })
P `∨ Q = `exists-dom (BoolU _) (λ { trueU → P; falseU → Q })

-- truth and falsehood as
-- nullary universal/existential quantification

`⊤ `⊥ : ∀{ℓ i} → SProp ℓ i
`⊤ = `forall-dom (EmptyU _) (λ ())
`⊥ = `exists-dom (EmptyU _) (λ ())
