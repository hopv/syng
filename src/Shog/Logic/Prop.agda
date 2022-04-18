----------------------------------------------------------------------
-- Syntax for the Shog proposition
----------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Logic.Prop where

open import Level using (Level; suc)
open import Size using (Size)
open import Codata.Sized.Thunk using (Thunk)
open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; foldr; map)

open import Shog.Util using (binary; nullary)

----------------------------------------------------------------------
-- Syntax for the Shog proposition: Propₛ ℓ i

data Propₛ ℓ (i : Size) : Set (suc ℓ)

PropTh : ∀ ℓ → Size → Set (suc ℓ)
PropTh ℓ i = Thunk (Propₛ ℓ) i

data Propₛ ℓ i where
  -- universal/existential quantification
  ∀^ ∃^ : (A : Set ℓ) → (A → Propₛ ℓ i) → Propₛ ℓ i
  -- implication
  _→ₛ_ : Propₛ ℓ i → Propₛ ℓ i → Propₛ ℓ i
  -- separating conjunction / magic wand
  _∗_ _-∗_ : Propₛ ℓ i → Propₛ ℓ i → Propₛ ℓ i
  -- update modality / persistence modality
  |=> □ : Propₛ ℓ i → Propₛ ℓ i
  -- save token
  save : Bool → PropTh ℓ i → Propₛ ℓ i

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

private variable
  ℓ ℓ' : Level
  i : Size
  A : Set ℓ'

----------------------------------------------------------------------
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

----------------------------------------------------------------------
-- Set embedding

⌜_⌝ : Set ℓ → Propₛ ℓ i
⌜ A ⌝ = ∃^ A (λ _ → ⊤ₛ)

----------------------------------------------------------------------
-- On the save token

savex save□ : PropTh ℓ i → Propₛ ℓ i
savex Pt = save false Pt
save□ Pt = save true Pt

----------------------------------------------------------------------
-- Iterated separating conjunction

[∗] : List (Propₛ ℓ i) → Propₛ ℓ i
[∗] = foldr _∗_ ⊤ₛ

[∗]-map : (A → Propₛ ℓ i) → List A → Propₛ ℓ i
[∗]-map Pf as = [∗] (map Pf as)

syntax [∗]-map (λ a → P) as = [∗] a ∈ as , P
