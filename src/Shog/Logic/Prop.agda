--------------------------------------------------------------------------------
-- Syntax for the Shog proposition
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Logic.Prop (ℓ : Level) where

open import Base.Level using (sucˡ)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk)
open import Base.Func using (_$_; _∘_; it)
open import Base.NElem using (2-ary; 0-ary)
open import Base.Bool using (Bool; tt; ff)
open import Data.List.Base using (List; foldr; map)

--------------------------------------------------------------------------------
-- Syntax for the Shog proposition: Prop' ι

data Prop' (ι : Size) : Set (sucˡ ℓ)

Prop< : Size → Set (sucˡ ℓ)
Prop< ι = Thunk Prop' ι

data Prop' ι where
  -- universal/existential quantification
  ∀˙ ∃˙ : (A : Set ℓ) → (A → Prop' ι) → Prop' ι
  -- implication
  _→'_ : Prop' ι → Prop' ι → Prop' ι
  -- separating conjunction / magic wand
  _∗_ _-∗_ : Prop' ι → Prop' ι → Prop' ι
  -- update modality / basicistence modality
  |=> □ : Prop' ι → Prop' ι
  -- save token (with the flag for persistency)
  save : Bool → Prop< ι → Prop' ι

infixr 5 _→'_ _-∗_
infixr 7 _∗_

private variable
  ι : Size
  A : Set ℓ
  P˙ : A → Prop' ∞
  P Q R S : Prop' ∞
  ℓ' : Level
  D : Set ℓ'

-- ∀˙/∃˙ with the set argument implicit
∀˙- ∃˙- : (A → Prop' ι) → Prop' ι
∀˙- = ∀˙ _
∃˙- = ∃˙ _

-- Syntax for ∀/∃

∀∈-syntax ∃∈-syntax : (A : Set ℓ) → (A → Prop' ι) → Prop' ι
∀∈-syntax = ∀˙
∃∈-syntax = ∃˙

∀-syntax ∃-syntax : (A → Prop' ι) → Prop' ι
∀-syntax = ∀˙-
∃-syntax = ∃˙-

infix 3 ∀∈-syntax ∃∈-syntax ∀-syntax ∃-syntax
syntax ∀∈-syntax A (λ x → P) = ∀' x ∈ A , P
syntax ∃∈-syntax A (λ x → P) = ∃ x ∈ A , P
syntax ∀-syntax (λ x → P) = ∀' x , P
syntax ∃-syntax (λ x → P) = ∃ x , P

--------------------------------------------------------------------------------
-- Deriving from universal/existential quantification ∀' / ∃

infixr 7 _∧_
infixr 6 _∨_

-- Conjunction ∧ and disjunction ∨
_∧_ _∨_ : Prop' ι → Prop' ι → Prop' ι
P ∧ Q = ∀˙- (2-ary P Q) -- Conjunction
P ∨ Q = ∃˙- (2-ary P Q) -- Disjunction

-- Truth ⊤ and falsehood ⊥
⊤ ⊥ : Prop' ι
⊤ = ∀˙- 0-ary -- Truth
⊥ = ∃˙- 0-ary -- Falsehood

--------------------------------------------------------------------------------
-- Set embedding

⌜_⌝ : Set ℓ → Prop' ι
⌜ A ⌝ = ∃˙ A (λ _ → ⊤)

--------------------------------------------------------------------------------
-- On the save token

-- exclusive / persistent save token
savex save□ : Prop< ι → Prop' ι
savex P^ = save ff P^
save□ P^ = save tt P^

--------------------------------------------------------------------------------
-- Iterated separating conjunction: [∗]

[∗] : List (Prop' ι) → Prop' ι
[∗] = foldr _∗_ ⊤

-- [∗] with map

[∗]-map : (D → Prop' ι) → List D → Prop' ι
[∗]-map P˙ ds = [∗] $ map P˙ ds

[∗]-map-syntax : (D → Prop' ι) → List D → Prop' ι
[∗]-map-syntax = [∗]-map

infix 3 [∗]-map-syntax
syntax [∗]-map-syntax (λ d → P) ds = [∗] d ∈ ds , P

--------------------------------------------------------------------------------
-- Basic Shog proposition

-- IsBasic P : Predicate
-- IsBasic P holds when P consists only of ∀, ∃ and ∗
data IsBasic : Prop' ∞ → Set (sucˡ ℓ) where
  ∀-IsBasic : (∀ a → IsBasic (P˙ a)) → IsBasic (∀˙ A P˙)
  ∃-IsBasic : (∀ a → IsBasic (P˙ a)) → IsBasic (∃˙ A P˙)
  ∗-IsBasic : IsBasic P → IsBasic Q → IsBasic (P ∗ Q)

-- Basic P : Type class wrapping IsBasic P
record Basic (P : Prop' ∞) : Set (sucˡ ℓ) where
  field basic : IsBasic P
open Basic {{...}}

abstract
  -- For ∀/∃

  -- -- They are not instances, because unfortunately
  -- -- Agda can't search a universally quantified instance (∀ a → ...)

  ∀-Basic : (∀ a → Basic (P˙ a)) → Basic (∀˙ A P˙)
  ∀-Basic ∀Basic .basic = ∀-IsBasic $ λ a → ∀Basic a .basic

  ∃-Basic : (∀ a → Basic (P˙ a)) → Basic (∃˙ A P˙)
  ∃-Basic ∀Basic .basic = ∃-IsBasic $ λ a → ∀Basic a .basic

  instance

    -- For ∧/∨/⊤/⊥

    ∧-Basic : {{Basic P}} → {{Basic Q}} → Basic (P ∧ Q)
    ∧-Basic = ∀-Basic $ 2-ary it it

    ∨-Basic : {{Basic P}} → {{Basic Q}} → Basic (P ∨ Q)
    ∨-Basic = ∃-Basic $ 2-ary it it

    ⊤-Basic : Basic ⊤
    ⊤-Basic = ∀-Basic 0-ary

    ⊥-Basic : Basic ⊥
    ⊥-Basic = ∃-Basic 0-ary

    -- For ∗

    ∗-Basic : {{Basic P}} → {{Basic Q}} → Basic (P ∗ Q)
    ∗-Basic .basic = ∗-IsBasic basic basic

    -- For ⌜ ⌝

    ⌜⌝-Basic : Basic ⌜ A ⌝
    ⌜⌝-Basic = ∃-Basic $ λ _ → ⊤-Basic
