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
-- Syntax for the Shog proposition: Propˢ ℓ i

data Propˢ ℓ (i : Size) : Set (suc ℓ)

PropTh : ∀ ℓ → Size → Set (suc ℓ)
PropTh ℓ i = Thunk (Propˢ ℓ) i

data Propˢ ℓ i where
  -- universal/existential quantification
  ∀^ ∃^ : (A : Set ℓ) → (A → Propˢ ℓ i) → Propˢ ℓ i
  -- implication
  _→ˢ_ : Propˢ ℓ i → Propˢ ℓ i → Propˢ ℓ i
  -- separating conjunction / magic wand
  _∗_ _-∗_ : Propˢ ℓ i → Propˢ ℓ i → Propˢ ℓ i
  -- update modality / persistence modality
  |=> □ : Propˢ ℓ i → Propˢ ℓ i
  -- save token
  save : Bool → PropTh ℓ i → Propˢ ℓ i

infix 3 ∀^ ∃^
syntax ∀^ A (λ x → P) = ∀ˢ x ∈ A , P
syntax ∃^ A (λ x → P) = ∃ˢ x ∈ A , P

∀^' ∃^' : ∀ {ℓ i} {A : Set ℓ} → (A → Propˢ ℓ i) → Propˢ ℓ i
∀^' = ∀^ _
∃^' = ∃^ _
infix 3 ∀^' ∃^'
syntax ∀^' (λ x → P) = ∀ˢ x , P
syntax ∃^' (λ x → P) = ∃ˢ x , P

infixr 5 _→ˢ_ _-∗_
infixr 7 _∗_

private variable
  ℓ ℓ' : Level
  i : Size
  A : Set ℓ'

----------------------------------------------------------------------
-- Deriving from universal/existential quantification ∀ˢ / ∃ˢ

-- -- Conjunction ∧ˢ / Disjunction ∨ˢ

infixr 7 _∧ˢ_
infixr 6 _∨ˢ_

_∧ˢ_ _∨ˢ_ : Propˢ ℓ i → Propˢ ℓ i → Propˢ ℓ i
P ∧ˢ Q = ∀^' (binary P Q)
P ∨ˢ Q = ∃^' (binary P Q)

-- -- Truth ⊤ˢ / Falsehood ⊥ˢ

⊤ˢ ⊥ˢ : Propˢ ℓ i
⊤ˢ = ∀^ _ nullary
⊥ˢ = ∃^ _ nullary

----------------------------------------------------------------------
-- Set embedding

⌜_⌝ : Set ℓ → Propˢ ℓ i
⌜ A ⌝ = ∃^ A (λ _ → ⊤ˢ)

----------------------------------------------------------------------
-- On the save token

savex save□ : PropTh ℓ i → Propˢ ℓ i
savex Pt = save false Pt
save□ Pt = save true Pt

----------------------------------------------------------------------
-- Iterated separating conjunction

[∗] : List (Propˢ ℓ i) → Propˢ ℓ i
[∗] = foldr _∗_ ⊤ˢ

[∗]-map : (A → Propˢ ℓ i) → List A → Propˢ ℓ i
[∗]-map Pf as = [∗] (map Pf as)

syntax [∗]-map (λ a → P) as = [∗] a ∈ as , P
