--------------------------------------------------------------------------------
-- Proposition
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Logic.Prop (ℓ : Level) where

open import Base.Level using (sucˡ)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk)
open import Base.Func using (_$_; _∘_; it)
open import Base.Few using (binary; absurd)
open import Base.Bool using (Bool; tt; ff)
open import Base.List using (List; []; _∷_; map)

--------------------------------------------------------------------------------
-- Proposition: Prop' ι

data Prop' (ι : Size) : Set (sucˡ ℓ)

-- Prop' under Thunk
Prop< : Size → Set (sucˡ ℓ)
Prop< ι = Thunk Prop' ι

infixr 5 _→'_ _-∗_
infixr 7 _∗_
infix 8 |=>_ □_

data Prop' ι where
  -- Universal/existential quantification
  ∀˙ ∃˙ : (A : Set ℓ) → (A → Prop' ι) → Prop' ι
  -- Implication
  _→'_ : Prop' ι → Prop' ι → Prop' ι
  -- Separating conjunction / magic wand
  _∗_ _-∗_ : Prop' ι → Prop' ι → Prop' ι
  -- Update / persistence modality
  |=>_ □_ : Prop' ι → Prop' ι
  -- Save token, with the persistence flag
  save : Bool → Prop< ι → Prop' ι

private variable
  ι : Size
  A : Set ℓ
  P˙ : A → Prop' ∞
  P Q R S : Prop' ∞
  ℓ' : Level
  D : Set ℓ'

--------------------------------------------------------------------------------
-- Syntax for ∀/∃

∀∈-syntax ∃∈-syntax : (A : Set ℓ) → (A → Prop' ι) → Prop' ι
∀∈-syntax = ∀˙
∃∈-syntax = ∃˙

∀-syntax ∃-syntax : (A → Prop' ι) → Prop' ι
∀-syntax = ∀˙ _
∃-syntax = ∃˙ _

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
P ∧ Q = ∀˙ _ (binary P Q) -- Conjunction
P ∨ Q = ∃˙ _ (binary P Q) -- Disjunction

-- Truth ⊤' and falsehood ⊥'
⊤' ⊥' : Prop' ι
⊤' = ∀˙ _ absurd -- Truth
⊥' = ∃˙ _ absurd -- Falsehood

--------------------------------------------------------------------------------
-- Set embedding

⌜_⌝ : Set ℓ → Prop' ι
⌜ A ⌝ = ∃˙ A (λ _ → ⊤')

--------------------------------------------------------------------------------
-- Exclusive / persistent save token

savex save□ : Prop< ι → Prop' ι
savex P^ = save ff P^
save□ P^ = save tt P^

--------------------------------------------------------------------------------
-- Iterated separating conjunction: [∗]

[∗] : List (Prop' ι) → Prop' ι
[∗] [] = ⊤'
[∗] (P ∷ Ps) = P ∗ [∗] Ps

-- [∗] with map

[∗]-map : (D → Prop' ι) → List D → Prop' ι
[∗]-map P˙ ds = [∗] (map P˙ ds)

[∗]-map-syntax : (D → Prop' ι) → List D → Prop' ι
[∗]-map-syntax = [∗]-map

infix 8 [∗]-map-syntax
syntax [∗]-map-syntax (λ d → P) ds = [∗ d ∈ ds ] P

--------------------------------------------------------------------------------
-- Basic Shog proposition

-- IsBasic P holds when P consists only of ∀, ∃ and ∗
data IsBasic : Prop' ∞ → Set (sucˡ ℓ) where
  ∀-IsBasic :  (∀ a → IsBasic (P˙ a))  →  IsBasic (∀˙ _ P˙)
  ∃-IsBasic :  (∀ a → IsBasic (P˙ a))  →  IsBasic (∃˙ _ P˙)
  ∗-IsBasic :  IsBasic P  →  IsBasic Q  →  IsBasic (P ∗ Q)

-- Basic : Type class wrapping IsBasic
record Basic (P : Prop' ∞) : Set (sucˡ ℓ) where
  field basic : IsBasic P
open Basic {{...}} public

abstract

  -- For ∀/∃

  -- -- They are not instances, because unfortunately
  -- -- Agda can't search a universally quantified instance (∀ a → ...)

  ∀-Basic :  (∀ a → Basic (P˙ a))  →  Basic (∀˙ _ P˙)
  ∀-Basic ∀Basic .basic =  ∀-IsBasic $ λ a → ∀Basic a .basic

  ∃-Basic :  (∀ a → Basic (P˙ a))  →  Basic (∃˙ _ P˙)
  ∃-Basic ∀Basic .basic =  ∃-IsBasic $ λ a → ∀Basic a .basic

  instance

    -- For ∧/∨/⊤'/⊥'

    ∧-Basic :  {{Basic P}}  →  {{Basic Q}}  →  Basic (P ∧ Q)
    ∧-Basic = ∀-Basic $ binary it it

    ∨-Basic :  {{Basic P}}  →  {{Basic Q}}  →  Basic (P ∨ Q)
    ∨-Basic =  ∃-Basic $ binary it it

    ⊤'-Basic :  Basic ⊤'
    ⊤'-Basic =  ∀-Basic absurd

    ⊥'-Basic :  Basic ⊥'
    ⊥'-Basic =  ∃-Basic absurd

    -- For ∗

    ∗-Basic :  {{Basic P}}  →  {{Basic Q}}  →  Basic (P ∗ Q)
    ∗-Basic .basic =  ∗-IsBasic basic basic

    -- For ⌜ ⌝

    ⌜⌝-Basic :  Basic ⌜ A ⌝
    ⌜⌝-Basic =  ∃-Basic $ λ _ → ⊤'-Basic
