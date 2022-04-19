----------------------------------------------------------------------
-- Syntax for the Shog proposition
----------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Logic.Prop where

open import Level using (Level; suc)
open import Size using (Size; ∞)
open import Codata.Thunk using (Thunk)
open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; foldr; map)
open import Function.Base using (_$_; _∘_; it)

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
  -- update modality / basicistence modality
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
  A : Set ℓ
  D : Set ℓ'
  P Q R S : Propˢ ℓ ∞
  Pf : A → Propˢ ℓ ∞

----------------------------------------------------------------------
-- Deriving from universal/existential quantification ∀ˢ / ∃ˢ

infixr 7 _∧ˢ_
infixr 6 _∨ˢ_

_∧ˢ_ _∨ˢ_ : Propˢ ℓ i → Propˢ ℓ i → Propˢ ℓ i
P ∧ˢ Q = ∀^' (binary P Q) -- Conjunction
P ∨ˢ Q = ∃^' (binary P Q) -- Disjunction

⊤ˢ ⊥ˢ : Propˢ ℓ i
⊤ˢ = ∀^ _ nullary -- Truth
⊥ˢ = ∃^ _ nullary -- Falsehood

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
-- Iterated separating conjunction: [∗]

[∗] : List (Propˢ ℓ i) → Propˢ ℓ i
[∗] = foldr _∗_ ⊤ˢ

-- [∗] with map

[∗]-map : (D → Propˢ ℓ i) → List D → Propˢ ℓ i
[∗]-map Pf ds = [∗] $ map Pf ds

syntax [∗]-map (λ d → P) ds = [∗] d ∈ ds , P

----------------------------------------------------------------------
-- Basic Shog proposition

data IsBasic {ℓ} : Propˢ ℓ ∞ → Set (suc ℓ) where
  ∀-IsBasic : (∀ a → IsBasic (Pf a)) → IsBasic (∀^ A Pf)
  ∃-IsBasic : (∀ a → IsBasic (Pf a)) → IsBasic (∃^ A Pf)
  ∗-IsBasic : IsBasic P → IsBasic Q → IsBasic (P ∗ Q)

record Basic {ℓ} (P : Propˢ ℓ ∞) : Set (suc ℓ) where
  field basic : IsBasic P
open Basic {{...}}

-- ∀-Basic and ∃-Basic are not instances, because unfortunately
-- Agda can't search a universally quantified instance (∀ a → ...)

∀-Basic : (∀ a → Basic (Pf a)) → Basic (∀^ A Pf)
∀-Basic ∀Basic .basic = ∀-IsBasic $ λ a → ∀Basic a .basic

∃-Basic : (∀ a → Basic (Pf a)) → Basic (∃^ A Pf)
∃-Basic ∀Basic .basic = ∃-IsBasic $ λ a → ∀Basic a .basic

instance

  ∧-Basic : {{Basic P}} → {{Basic Q}} → Basic (P ∧ˢ Q)
  ∧-Basic = ∀-Basic $ binary it it

  ∨-Basic : {{Basic P}} → {{Basic Q}} → Basic (P ∨ˢ Q)
  ∨-Basic = ∃-Basic $ binary it it

  ⊤-Basic : Basic {ℓ} ⊤ˢ
  ⊤-Basic = ∀-Basic nullary

  ⊥-Basic : Basic {ℓ} ⊥ˢ
  ⊥-Basic = ∃-Basic nullary

  ∗-Basic : {{Basic P}} → {{Basic Q}} → Basic (P ∗ Q)
  ∗-Basic .basic = ∗-IsBasic basic basic

  ⌜⌝-Basic : Basic ⌜ A ⌝
  ⌜⌝-Basic = ∃-Basic $ λ _ → ⊤-Basic
