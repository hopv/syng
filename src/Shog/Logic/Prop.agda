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

private variable
  ℓ ℓ' : Level
  i : Size

----------------------------------------------------------------------
-- Syntax for the Shog proposition: Propˢ ℓ i

data Propˢ ℓ (i : Size) : Set (suc ℓ)

Propᵗ : ∀ ℓ → Size → Set (suc ℓ)
Propᵗ ℓ i = Thunk (Propˢ ℓ) i

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
  save : Bool → Propᵗ ℓ i → Propˢ ℓ i

infixr 5 _→ˢ_ _-∗_
infixr 7 _∗_

-- ∀^/∃^ with the set argument implicit
∀^' ∃^' : ∀ {ℓ} {A : Set ℓ} → (A → Propˢ ℓ i) → Propˢ ℓ i
∀^' = ∀^ _
∃^' = ∃^ _

-- Syntax for ∀/∃

∀∈-syntax ∃∈-syntax : (A : Set ℓ) → (A → Propˢ ℓ i) → Propˢ ℓ i
∀∈-syntax = ∀^
∃∈-syntax = ∃^

∀-syntax ∃-syntax : ∀ {ℓ} {A : Set ℓ} → (A → Propˢ ℓ i) → Propˢ ℓ i
∀-syntax = ∀^'
∃-syntax = ∃^'

infix 3 ∀∈-syntax ∃∈-syntax ∀-syntax ∃-syntax
syntax ∀∈-syntax A (λ x → P) = ∀ˢ x ∈ A , P
syntax ∃∈-syntax A (λ x → P) = ∃ˢ x ∈ A , P
syntax ∀-syntax (λ x → P) = ∀ˢ x , P
syntax ∃-syntax (λ x → P) = ∃ˢ x , P

private variable
  A : Set ℓ
  D : Set ℓ'
  P Q R S : Propˢ ℓ ∞
  Pᶠ : A → Propˢ ℓ ∞

----------------------------------------------------------------------
-- Deriving from universal/existential quantification ∀ˢ / ∃ˢ

infixr 7 _∧_
infixr 6 _∨_

-- Conjunction ∧ and disjunction ∨
_∧_ _∨_ : Propˢ ℓ i → Propˢ ℓ i → Propˢ ℓ i
P ∧ Q = ∀^' (binary P Q) -- Conjunction
P ∨ Q = ∃^' (binary P Q) -- Disjunction

-- Truth ⊤ and falsehood ⊥
⊤ ⊥ : Propˢ ℓ i
⊤ = ∀^ _ nullary -- Truth
⊥ = ∃^ _ nullary -- Falsehood

----------------------------------------------------------------------
-- Set embedding

⌜_⌝ : Set ℓ → Propˢ ℓ i
⌜ A ⌝ = ∃^ A (λ _ → ⊤)

----------------------------------------------------------------------
-- On the save token

savex save□ : Propᵗ ℓ i → Propˢ ℓ i
savex Pᵗ = save false Pᵗ
save□ Pᵗ = save true Pᵗ

----------------------------------------------------------------------
-- Iterated separating conjunction: [∗]

[∗] : List (Propˢ ℓ i) → Propˢ ℓ i
[∗] = foldr _∗_ ⊤

-- [∗] with map

[∗]-map : (D → Propˢ ℓ i) → List D → Propˢ ℓ i
[∗]-map Pᶠ ds = [∗] $ map Pᶠ ds

[∗]-map-syntax : (D → Propˢ ℓ i) → List D → Propˢ ℓ i
[∗]-map-syntax = [∗]-map

infix 3 [∗]-map-syntax
syntax [∗]-map-syntax (λ d → P) ds = [∗] d ∈ ds , P

----------------------------------------------------------------------
-- Basic Shog proposition

-- IsBasic P : Predicate
-- IsBasic P holds when P consists only of ∀, ∃ and ∗
data IsBasic {ℓ} : Propˢ ℓ ∞ → Set (suc ℓ) where
  ∀-IsBasic : (∀ a → IsBasic (Pᶠ a)) → IsBasic (∀^ A Pᶠ)
  ∃-IsBasic : (∀ a → IsBasic (Pᶠ a)) → IsBasic (∃^ A Pᶠ)
  ∗-IsBasic : IsBasic P → IsBasic Q → IsBasic (P ∗ Q)

-- Basic P : Type class wrapping IsBasic P
record Basic {ℓ} (P : Propˢ ℓ ∞) : Set (suc ℓ) where
  field basic : IsBasic P
open Basic {{...}}

-- For ∀/∃

-- -- They are not instances, because unfortunately
-- -- Agda can't search a universally quantified instance (∀ a → ...)

∀-Basic : (∀ a → Basic (Pᶠ a)) → Basic (∀^ A Pᶠ)
∀-Basic ∀Basic .basic = ∀-IsBasic $ λ a → ∀Basic a .basic

∃-Basic : (∀ a → Basic (Pᶠ a)) → Basic (∃^ A Pᶠ)
∃-Basic ∀Basic .basic = ∃-IsBasic $ λ a → ∀Basic a .basic

instance

  -- For ∧/∨/⊤/⊥

  ∧-Basic : {{Basic P}} → {{Basic Q}} → Basic (P ∧ Q)
  ∧-Basic = ∀-Basic $ binary it it

  ∨-Basic : {{Basic P}} → {{Basic Q}} → Basic (P ∨ Q)
  ∨-Basic = ∃-Basic $ binary it it

  ⊤-Basic : Basic {ℓ} ⊤
  ⊤-Basic = ∀-Basic nullary

  ⊥-Basic : Basic {ℓ} ⊥
  ⊥-Basic = ∃-Basic nullary

  -- For ∗

  ∗-Basic : {{Basic P}} → {{Basic Q}} → Basic (P ∗ Q)
  ∗-Basic .basic = ∗-IsBasic basic basic

  -- For ⌜ ⌝

  ⌜⌝-Basic : Basic ⌜ A ⌝
  ⌜⌝-Basic = ∃-Basic $ λ _ → ⊤-Basic
