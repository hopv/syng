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
  ι : Size

----------------------------------------------------------------------
-- Syntax for the Shog proposition: Propˢ ℓ ι

data Propˢ ℓ (ι : Size) : Set (suc ℓ)

Propˢ< : ∀ ℓ → Size → Set (suc ℓ)
Propˢ< ℓ ι = Thunk (Propˢ ℓ) ι

data Propˢ ℓ ι where
  -- universal/existential quantification
  ∀^ ∃^ : (A : Set ℓ) → (A → Propˢ ℓ ι) → Propˢ ℓ ι
  -- implication
  _→ˢ_ : Propˢ ℓ ι → Propˢ ℓ ι → Propˢ ℓ ι
  -- separating conjunction / magic wand
  _∗_ _-∗_ : Propˢ ℓ ι → Propˢ ℓ ι → Propˢ ℓ ι
  -- update modality / basicistence modality
  |=> □ : Propˢ ℓ ι → Propˢ ℓ ι
  -- save token
  save : Bool → Propˢ< ℓ ι → Propˢ ℓ ι

infixr 5 _→ˢ_ _-∗_
infixr 7 _∗_

-- ∀^/∃^ with the set argument implicit
∀^' ∃^' : ∀ {ℓ} {A : Set ℓ} → (A → Propˢ ℓ ι) → Propˢ ℓ ι
∀^' = ∀^ _
∃^' = ∃^ _

-- Syntax for ∀/∃

∀∈-syntax ∃∈-syntax : (A : Set ℓ) → (A → Propˢ ℓ ι) → Propˢ ℓ ι
∀∈-syntax = ∀^
∃∈-syntax = ∃^

∀-syntax ∃-syntax : ∀ {ℓ} {A : Set ℓ} → (A → Propˢ ℓ ι) → Propˢ ℓ ι
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
_∧_ _∨_ : Propˢ ℓ ι → Propˢ ℓ ι → Propˢ ℓ ι
P ∧ Q = ∀^' (binary P Q) -- Conjunction
P ∨ Q = ∃^' (binary P Q) -- Disjunction

-- Truth ⊤ and falsehood ⊥
⊤ ⊥ : Propˢ ℓ ι
⊤ = ∀^ _ nullary -- Truth
⊥ = ∃^ _ nullary -- Falsehood

----------------------------------------------------------------------
-- Set embedding

⌜_⌝ : Set ℓ → Propˢ ℓ ι
⌜ A ⌝ = ∃^ A (λ _ → ⊤)

----------------------------------------------------------------------
-- On the save token

savex save□ : Propˢ< ℓ ι → Propˢ ℓ ι
savex Pᶺ = save false Pᶺ
save□ Pᶺ = save true Pᶺ

----------------------------------------------------------------------
-- Iterated separating conjunction: [∗]

[∗] : List (Propˢ ℓ ι) → Propˢ ℓ ι
[∗] = foldr _∗_ ⊤

-- [∗] with map

[∗]-map : (D → Propˢ ℓ ι) → List D → Propˢ ℓ ι
[∗]-map Pᶠ ds = [∗] $ map Pᶠ ds

[∗]-map-syntax : (D → Propˢ ℓ ι) → List D → Propˢ ℓ ι
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
