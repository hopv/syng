--------------------------------------------------------------------------------
-- Proposition
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Logic.Prop (ℓ : Level) where

open import Base.Level using (^_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk)
open import Base.Func using (_$_; _∘_; it)
open import Base.Few using (binary; absurd)
open import Base.Bool using (Bool; tt; ff)
open import Base.List using (List; []; _∷_; map)

--------------------------------------------------------------------------------
-- Prop': Proposition

data  Prop' (ι : Size) :  Set (^ ℓ)

-- Prop˂: Prop' under Thunk
Prop˂ :  Size →  Set (^ ℓ)
Prop˂ ι =  Thunk Prop' ι

private variable
  ι :  Size
  X :  Set ℓ
  P˙ :  X → Prop' ∞
  P Q R S :  Prop' ∞
  ℓ' :  Level
  D :  Set ℓ'

infixr 5 _→'_ _-∗_
infixr 7 _∗_
infix 8 |=>_ □_

data  Prop' ι  where

  -- ∀˙, ∃˙: Universal/existential quantification over any type X in Set ℓ,
  --         which does not include Prop' ι itself (predicativity)
  ∀˙ ∃˙ :  (X → Prop' ι) →  Prop' ι
  -- →': Implication
  _→'_ :  Prop' ι →  Prop' ι →  Prop' ι

  -- ∗: Separating conjunction
  -- -∗: Magic wand
  _∗_ _-∗_ :  Prop' ι →  Prop' ι →  Prop' ι

  -- |=>: Update modality
  -- □: Persistence modality
  |=>_ □_ :  Prop' ι →  Prop' ι

  -- Saveˣ, Save□: Save token, exclusive and persistent
  Saveˣ Save□ :  Prop˂ ι →  Prop' ι

--------------------------------------------------------------------------------
-- Syntax for ∀/∃

∀∈-syntax ∃∈-syntax ∀-syntax ∃-syntax :  (X → Prop' ι) →  Prop' ι
∀∈-syntax =  ∀˙
∃∈-syntax =  ∃˙
∀-syntax =  ∀˙
∃-syntax =  ∃˙
infix 3 ∀∈-syntax ∃∈-syntax ∀-syntax ∃-syntax
syntax ∀∈-syntax {X = X} (λ x → P) =  ∀' x ∈ X , P
syntax ∃∈-syntax {X = X} (λ x → P) =  ∃ x ∈ X , P
syntax ∀-syntax (λ x → P) =  ∀' x , P
syntax ∃-syntax (λ x → P) =  ∃ x , P

--------------------------------------------------------------------------------
-- ∧: Conjunction
-- ∨: Disjunction

infixr 7 _∧_
infixr 6 _∨_

_∧_ _∨_ :  Prop' ι →  Prop' ι →  Prop' ι
P ∧ Q =  ∀˙ (binary P Q)
P ∨ Q =  ∃˙ (binary P Q)

--------------------------------------------------------------------------------
-- ⊤': Truth
-- ⊥': Falsehood

⊤' ⊥' :  Prop' ι
⊤' =  ∀˙ absurd
⊥' =  ∃˙ absurd

--------------------------------------------------------------------------------
-- ⌜ ⌝: Set embedding

⌜_⌝ :  Set ℓ →  Prop' ι
⌜ X ⌝ =  ∃ _ ∈ X , ⊤'

--------------------------------------------------------------------------------
-- [∗]: Iterated separating conjunction

infix 9 [∗]_
[∗]_ :  List (Prop' ι) →  Prop' ι
[∗] [] =  ⊤'
[∗] (P ∷ Ps) =  P ∗ [∗] Ps

-- [∗] with map

[∗]-map :  (D → Prop' ι) →  List D →  Prop' ι
[∗]-map P˙ ds =  [∗] map P˙ ds

-- Syntax for [∗]-map

[∗∈]-syntax :  (D → Prop' ι) →  List D →  Prop' ι
[∗∈]-syntax =  [∗]-map
infix 8 [∗∈]-syntax
syntax [∗∈]-syntax (λ d → P) ds =  [∗ d ∈ ds ] P

--------------------------------------------------------------------------------
-- Basic Shog proposition

-- IsBasic P: P consists only of ∀, ∃ and ∗
data  IsBasic :  Prop' ∞ →  Set (^ ℓ)  where
  ∀-IsBasic :  (∀ x → IsBasic (P˙ x)) →  IsBasic (∀˙ P˙)
  ∃-IsBasic :  (∀ x → IsBasic (P˙ x)) →  IsBasic (∃˙ P˙)
  ∗-IsBasic :  IsBasic P →  IsBasic Q →  IsBasic (P ∗ Q)
  □-IsBasic :  IsBasic P →  IsBasic (□ P)

-- Basic: Type class wrapping IsBasic
record  Basic (P : Prop' ∞) :  Set (^ ℓ)  where
  field  isBasic :  IsBasic P
open Basic {{...}} public

abstract

  -- For ∀/∃
  -- They are not instances, because unfortunately Agda can't search a
  -- universally quantified instance (∀ x → ...)

  ∀-Basic :  (∀ x → Basic (P˙ x)) →  Basic (∀˙ P˙)
  ∀-Basic ∀Basic .isBasic =  ∀-IsBasic $ λ x → ∀Basic x .isBasic

  ∃-Basic :  (∀ x → Basic (P˙ x)) →  Basic (∃˙ P˙)
  ∃-Basic ∀Basic .isBasic =  ∃-IsBasic $ λ x → ∀Basic x .isBasic

  instance

    -- For ∧/∨/⊤'/⊥'

    ∧-Basic :  {{Basic P}} →  {{Basic Q}} →  Basic (P ∧ Q)
    ∧-Basic =  ∀-Basic $ binary it it

    ∨-Basic :  {{Basic P}} →  {{Basic Q}} →  Basic (P ∨ Q)
    ∨-Basic =  ∃-Basic $ binary it it

    ⊤-Basic :  Basic ⊤'
    ⊤-Basic =  ∀-Basic absurd

    ⊥-Basic :  Basic ⊥'
    ⊥-Basic =  ∃-Basic absurd

    -- For ∗

    ∗-Basic :  {{Basic P}} →  {{Basic Q}} →  Basic (P ∗ Q)
    ∗-Basic .isBasic =  ∗-IsBasic isBasic isBasic

    -- For ⌜ ⌝

    ⌜⌝-Basic :  Basic ⌜ X ⌝
    ⌜⌝-Basic =  ∃-Basic $ λ _ → ⊤-Basic

    -- For ⌜ ⌝

    □-Basic :  {{Basic P}} →  Basic (□ P)
    □-Basic .isBasic =  □-IsBasic isBasic
