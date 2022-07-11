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

infixr 5 _→'_ _-∗_
infixr 7 _∗_
infix 8 |=>_ □_

private variable
  ι :  Size
  A :  Set ℓ
  P˙ :  A → Prop' ∞
  P Q R S :  Prop' ∞
  ℓ' :  Level
  D :  Set ℓ'

data  Prop' ι  where
  -- ∀˙, ∃˙: Universal/existential quantification
  ∀˙ ∃˙ :  (A → Prop' ι) →  Prop' ι
  -- →': Implication
  _→'_ :  Prop' ι →  Prop' ι →  Prop' ι
  -- ∗: Separating conjunction
  -- -∗: Magic wand
  _∗_ _-∗_ :  Prop' ι →  Prop' ι →  Prop' ι
  -- |=>: Update modality
  -- □: Persistence modality
  |=>_ □_ :  Prop' ι →  Prop' ι
  -- saveˣ, save□: Save token, exclusive and persistent
  saveˣ save□ :  Prop˂ ι →  Prop' ι

--------------------------------------------------------------------------------
-- Syntax for ∀/∃

∀∈-syntax ∃∈-syntax ∀-syntax ∃-syntax :  (A → Prop' ι) →  Prop' ι
∀∈-syntax =  ∀˙
∃∈-syntax =  ∃˙
∀-syntax =  ∀˙
∃-syntax =  ∃˙
infix 3 ∀∈-syntax ∃∈-syntax ∀-syntax ∃-syntax
syntax ∀∈-syntax {A = A} (λ x → P) =  ∀' x ∈ A , P
syntax ∃∈-syntax {A = A} (λ x → P) =  ∃ x ∈ A , P
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
⌜ A ⌝ =  ∃ _ ∈ A , ⊤'

--------------------------------------------------------------------------------
-- [∗]: Iterated separating conjunction

[∗] :  List (Prop' ι) →  Prop' ι
[∗] [] =  ⊤'
[∗] (P ∷ Ps) =  P ∗ [∗] Ps

-- [∗] with map

[∗]-map :  (D → Prop' ι) →  List D →  Prop' ι
[∗]-map P˙ ds =  [∗] (map P˙ ds)

-- Syntax for [∗]-map

[∗∈]-syntax :  (D → Prop' ι) →  List D →  Prop' ι
[∗∈]-syntax =  [∗]-map
infix 8 [∗∈]-syntax
syntax [∗∈]-syntax (λ d → P) ds =  [∗ d ∈ ds ] P

--------------------------------------------------------------------------------
-- Basic Shog proposition

-- IsBasic P: P consists only of ∀, ∃ and ∗
data  IsBasic :  Prop' ∞ →  Set (^ ℓ)  where
  ∀-IsBasic :  (∀ a → IsBasic (P˙ a)) →  IsBasic (∀˙ P˙)
  ∃-IsBasic :  (∀ a → IsBasic (P˙ a)) →  IsBasic (∃˙ P˙)
  ∗-IsBasic :  IsBasic P →  IsBasic Q →  IsBasic (P ∗ Q)
  □-IsBasic :  IsBasic P →  IsBasic (□ P)

-- Basic: Type class wrapping IsBasic
record  Basic (P : Prop' ∞) :  Set (^ ℓ)  where
  field  isBasic :  IsBasic P
open Basic {{...}} public

abstract

  -- For ∀/∃

  -- -- They are not instances, because unfortunately
  -- -- Agda can't search a universally quantified instance (∀ a → ...)

  ∀-Basic :  (∀ a → Basic (P˙ a)) →  Basic (∀˙ P˙)
  ∀-Basic ∀Basic .isBasic =  ∀-IsBasic $ λ a → ∀Basic a .isBasic

  ∃-Basic :  (∀ a → Basic (P˙ a)) →  Basic (∃˙ P˙)
  ∃-Basic ∀Basic .isBasic =  ∃-IsBasic $ λ a → ∀Basic a .isBasic

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

    ⌜⌝-Basic :  Basic ⌜ A ⌝
    ⌜⌝-Basic =  ∃-Basic $ λ _ → ⊤-Basic

    -- For ⌜ ⌝

    □-Basic :  {{Basic P}} →  Basic (□ P)
    □-Basic .isBasic =  □-IsBasic isBasic
