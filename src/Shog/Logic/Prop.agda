{-# OPTIONS --sized-types #-}

module Shog.Logic.Prop where

open import Size
open import Level
open import Data.Bool
open import Codata.Sized.Thunk

-- syntax for a proposition in Shog
data SProp ℓ (i : Size) : Set (suc ℓ) where
  -- universal/existential quantification
  `∀! `∃! : (A : Set ℓ) → (A → SProp ℓ i) → SProp ℓ i
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

infix 0 `∀! `∃!
syntax `∀! A (λ x → P) = `∀ x ∈ A `→ P
syntax `∃! A (λ x → P) = `∃ x ∈ A `→ P

-- universe-polymorphic Bool and Empty

data BoolU ℓ : Set ℓ where
  trueU falseU : BoolU ℓ

data EmptyU ℓ : Set ℓ where

private variable
  ℓ : Level
  i : Size

-- conjunction `∧ and disjunction `∨

infixr 7 _`∧_
infixr 6 _`∨_

_`∧_ _`∨_ : SProp ℓ i → SProp ℓ i → SProp ℓ i
P `∧ Q = `∀! (BoolU _) (λ { trueU → P; falseU → Q })
P `∨ Q = `∃! (BoolU _) (λ { trueU → P; falseU → Q })

-- truth `⊤ and falsehood `⊥

`⊤ `⊥ : SProp ℓ i
`⊤ = `∀! (EmptyU _) (λ ())
`⊥ = `∃! (EmptyU _) (λ ())
