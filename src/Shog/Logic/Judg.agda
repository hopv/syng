------------------------------------------------------------------------
-- Judgment in Shog
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Logic.Judg where

open import Level using (Level; suc)
open import Size using (Size; ∞)
open import Codata.Thunk using (Thunk; force)
open import Function.Base using (_∘_)
open import Data.Bool using (Bool)
open import Data.List.Base using (List)

open import Shog.Logic.Prop

------------------------------------------------------------------------
-- Judgment: P ⊢[ i ]* Jr

-- Result of a judgment
data JudgRes ℓ : Set (suc ℓ) where
  -- Just a proposition
  pure : Propˢ ℓ ∞ → JudgRes ℓ
  -- Under the super update
  |=>> : Propˢ ℓ ∞ → JudgRes ℓ

private variable
  ℓ : Level
  P Q R : Propˢ ℓ ∞
  Jr : JudgRes ℓ
  A : Set ℓ
  Pᶠ Qᶠ : A → Propˢ ℓ ∞
  Pᵗ Qᵗ : Propᵗ ℓ ∞
  a : A
  F : A → Set ℓ
  b : Bool
  Pᵗs : List (Propᵗ ℓ ∞)

-- Declaring Judg
data Judg {ℓ} (i : Size) : Propˢ ℓ ∞ → JudgRes ℓ → Set (suc ℓ)

-- Notation

infix 2 _⊢[_]*_ _⊢[_]_ _⊢[<_]_ _⊢[_]=>>_

_⊢[_]*_ : Propˢ ℓ ∞ → Size → JudgRes ℓ → Set (suc ℓ)
P ⊢[ i ]* Jr = Judg i P Jr

_⊢[_]_ : Propˢ ℓ ∞ → Size → Propˢ ℓ ∞ → Set (suc ℓ)
P ⊢[ i ] Q = P ⊢[ i ]* pure Q

_⊢[<_]_ : Propˢ ℓ ∞ → Size → Propˢ ℓ ∞ → Set (suc ℓ)
P ⊢[< i ] Q = Thunk (P ⊢[_] Q) i

_⊢[_]=>>_ : Propˢ ℓ ∞ → Size → Propˢ ℓ ∞ → Set (suc ℓ)
P ⊢[ i ]=>> Q = P ⊢[ i ]* |=>> Q

infixr -1 _»_ _ᵘ»ᵘ_ -- the same fixity with _$_

-- Defining Judg
data Judg {ℓ} i where
  ----------------------------------------------------------------------
  -- Basic rules
  idˢ : P ⊢[ i ] P
  _»_ : P ⊢[ i ] Q → Q ⊢[ i ]* Jr → P ⊢[ i ]* Jr
  ----------------------------------------------------------------------
  -- On ∀/∃
  ∀-intro : (∀ a → P ⊢[ i ] Qᶠ a) → P ⊢[ i ] ∀^ A Qᶠ
  ∃-elim : (∀ a → Pᶠ a ⊢[ i ]* Jr) → ∃^ A Pᶠ ⊢[ i ]* Jr
  ∀-elim : ∀^ A Pᶠ ⊢[ i ] Pᶠ a
  ∃-intro : Pᶠ a ⊢[ i ] ∃^ A Pᶠ
  ∀∃⇒∃∀-⊤ : ∀ˢ a ∈ A , ∃ˢ _ ∈ F a , ⊤ˢ ⊢[ i ] ∃ˢ _ ∈ (∀ a → F a) , ⊤ˢ
  ----------------------------------------------------------------------
  -- On →
  →-intro : P ∧ˢ Q ⊢[ i ] R → Q ⊢[ i ] P →ˢ R
  →-elim : Q ⊢[ i ] P →ˢ R → P ∧ˢ Q ⊢[ i ] R
  ----------------------------------------------------------------------
  -- On ∗
  ⊤∗-elim : ⊤ˢ ∗ P ⊢[ i ] P
  ⊤∗-intro : P ⊢[ i ] ⊤ˢ ∗ P
  ∗-comm : P ∗ Q ⊢[ i ] Q ∗ P
  ∗-assoc₀ : (P ∗ Q) ∗ R ⊢[ i ] P ∗ (Q ∗ R)
  ∗-mono₀ : P ⊢[ i ] Q → P ∗ R ⊢[ i ] Q ∗ R
  ----------------------------------------------------------------------
  -- On -∗
  -∗-intro : P ∗ Q ⊢[ i ] R → Q ⊢[ i ] P -∗ R
  -∗-elim : Q ⊢[ i ] P -∗ R → P ∗ Q ⊢[ i ] R
  ----------------------------------------------------------------------
  -- On |=>
  |=>-mono : P ⊢[ i ] Q → |=> P ⊢[ i ] |=> Q
  |=>-intro : P ⊢[ i ] |=> P
  |=>-join : |=> (|=> P) ⊢[ i ] |=> P
  |=>-frame₀ : P ∗ |=> Q ⊢[ i ] |=> (P ∗ Q)
  |=>-∃-out : |=> (∃ˢ _ ∈ A , P) ⊢[ i ] ∃ˢ _ ∈ A , |=> P
  ----------------------------------------------------------------------
  -- On □
  □-mono : P ⊢[ i ] Q → □ P ⊢[ i ] □ Q
  □-elim : □ P ⊢[ i ] P
  □-dup : □ P ⊢[ i ] □ (□ P)
  □₀-∧⇒∗ : □ P ∧ˢ Q ⊢[ i ] □ P ∗ Q
  □-∀-in : ∀^ A (□ ∘ Pᶠ) ⊢[ i ] □ (∀^ A Pᶠ)
  □-∃-out : □ (∃^ A Pᶠ) ⊢[ i ] ∃^ A (□ ∘ Pᶠ)
  ----------------------------------------------------------------------
  -- On the super update
  ᵗ|=>⇒=>> : P ⊢[< i ] |=> Q → P ⊢[ i ]=>> Q
  _ᵘ»ᵘ_ : P ⊢[ i ]=>> Q → Q ⊢[ i ]=>> R → P ⊢[ i ]=>> R
  =>>-frame₀ : Q ⊢[ i ]=>> R → P ∗ Q ⊢[ i ]=>> P ∗ R
  ----------------------------------------------------------------------
  -- On the save token
  save-mono₁ : {{Basic R}} →
    R ∗ Pᵗ .force ⊢[< i ] Qᵗ .force → save b Pᵗ ⊢[ i ] save b Qᵗ
  save-□⇒x : save□ Pᵗ ⊢[ i ] savex Pᵗ
  save□-□ : save□ Pᵗ ⊢[ i ] □ (save□ Pᵗ)
  savex-alloc : Pᵗ .force ⊢[ i ]=>> savex Pᵗ
  save□-alloc-rec : [∗]-map save□ Pᵗs -∗ [∗]-map (λ Pᵗ → □ (Pᵗ .force)) Pᵗs
                      ⊢[ i ]=>> [∗]-map save□ Pᵗs

------------------------------------------------------------------------
-- Persistence: Pers P

record Pers {ℓ} (P : Propˢ ℓ ∞) : Set (suc ℓ) where
  field pers : ∀ {i} → P ⊢[ i ] □ P
open Pers {{...}} public
