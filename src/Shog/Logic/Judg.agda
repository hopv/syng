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

infix 2 _⊢[_]*_ _⊢[_]_ _⊢[<_]_ _⊢[_]=>>_

-- General judgment
_⊢[_]*_ : Propˢ ℓ ∞ → Size → JudgRes ℓ → Set (suc ℓ)
P ⊢[ i ]* Jr = Judg i P Jr

-- Sequent
_⊢[_]_ : Propˢ ℓ ∞ → Size → Propˢ ℓ ∞ → Set (suc ℓ)
P ⊢[ i ] Q = P ⊢[ i ]* pure Q

-- Sequent under thunk
_⊢[<_]_ : Propˢ ℓ ∞ → Size → Propˢ ℓ ∞ → Set (suc ℓ)
P ⊢[< i ] Q = Thunk (P ⊢[_] Q) i

-- Super update
_⊢[_]=>>_ : Propˢ ℓ ∞ → Size → Propˢ ℓ ∞ → Set (suc ℓ)
P ⊢[ i ]=>> Q = P ⊢[ i ]* |=>> Q

infixr -1 _»_ _ᵘ»ᵘ_ -- the same fixity with _$_

-- Defining Judg
data Judg {ℓ} i where
  ----------------------------------------------------------------------
  -- The sequent is reflexive
  idˢ : P ⊢[ i ] P
  -- The left-hand side of a judgment can be modified with a sequent
  _»_ : P ⊢[ i ] Q → Q ⊢[ i ]* Jr → P ⊢[ i ]* Jr
  ----------------------------------------------------------------------
  -- Introducing ∀ / Eliminating ∃
  ∀-intro : (∀ a → P ⊢[ i ] Qᶠ a) → P ⊢[ i ] ∀^ A Qᶠ
  ∃-elim : (∀ a → Pᶠ a ⊢[ i ]* Jr) → ∃^ A Pᶠ ⊢[ i ]* Jr
  -- Eliminating ∀ / Introducing ∃
  ∀-elim : ∀^ A Pᶠ ⊢[ i ] Pᶠ a
  ∃-intro : Pᶠ a ⊢[ i ] ∃^ A Pᶠ
  -- Unnesting ∀ˢ ... , ∃ˢ ... , ⊤ into ∃ˢ _ ∈ (∀ ...) , ⊤
  ∀∃⇒∃∀-⊤ : ∀ˢ a ∈ A , ∃ˢ _ ∈ F a , ⊤ ⊢[ i ] ∃ˢ _ ∈ (∀ a → F a) , ⊤
  ----------------------------------------------------------------------
  -- → is the right adjoint of ∧
  →-intro : P ∧ Q ⊢[ i ] R → Q ⊢[ i ] P →ˢ R
  →-elim : Q ⊢[ i ] P →ˢ R → P ∧ Q ⊢[ i ] R
  ----------------------------------------------------------------------
  -- ∗ is unital w.r.t. ⊤, commutative, associative, and monotone
  ⊤∗-elim : ⊤ ∗ P ⊢[ i ] P
  ⊤∗-intro : P ⊢[ i ] ⊤ ∗ P
  ∗-comm : P ∗ Q ⊢[ i ] Q ∗ P
  ∗-assoc₀ : (P ∗ Q) ∗ R ⊢[ i ] P ∗ (Q ∗ R)
  ∗-mono₀ : P ⊢[ i ] Q → P ∗ R ⊢[ i ] Q ∗ R
  ----------------------------------------------------------------------
  -- -∗ is the right adjoint of ∗
  -∗-intro : P ∗ Q ⊢[ i ] R → Q ⊢[ i ] P -∗ R
  -∗-elim : Q ⊢[ i ] P -∗ R → P ∗ Q ⊢[ i ] R
  ----------------------------------------------------------------------
  -- |=> is monadic: monotone, increasing, and idempotent
  |=>-mono : P ⊢[ i ] Q → |=> P ⊢[ i ] |=> Q
  |=>-intro : P ⊢[ i ] |=> P
  |=>-join : |=> (|=> P) ⊢[ i ] |=> P
  -- ∗ can get inside |=>
  |=>-frame₀ : P ∗ |=> Q ⊢[ i ] |=> (P ∗ Q)
  -- ∃ˢ _ , can get outside |=>
  |=>-∃-out : |=> (∃ˢ _ ∈ A , P) ⊢[ i ] ∃ˢ _ ∈ A , |=> P
  ----------------------------------------------------------------------
  -- □ is comonadic: monotone, decreasing, and idempotent
  □-mono : P ⊢[ i ] Q → □ P ⊢[ i ] □ Q
  □-elim : □ P ⊢[ i ] P
  □-dup : □ P ⊢[ i ] □ (□ P)
  -- ∧ can turn into ∗ when one argument is under □
  □₀-∧⇒∗ : □ P ∧ Q ⊢[ i ] □ P ∗ Q
  -- ∀ can get inside □
  □-∀-in : ∀^ A (□ ∘ Pᶠ) ⊢[ i ] □ (∀^ A Pᶠ)
  -- ∃ can get outside □
  □-∃-out : □ (∃^ A Pᶠ) ⊢[ i ] ∃^ A (□ ∘ Pᶠ)
  ----------------------------------------------------------------------
  -- A thunk sequent under |=> can be lifted to a super update =>>
  ᵗ|=>⇒=>> : P ⊢[< i ] |=> Q → P ⊢[ i ]=>> Q
  -- The super update =>> is transitive
  _ᵘ»ᵘ_ : P ⊢[ i ]=>> Q → Q ⊢[ i ]=>> R → P ⊢[ i ]=>> R
  -- The super update =>> can frame
  =>>-frame₀ : Q ⊢[ i ]=>> R → P ∗ Q ⊢[ i ]=>> P ∗ R
  ----------------------------------------------------------------------
  -- The save token can be modified with a thunk sequent
  save-mono₁ : {{Basic R}} →
    R ∗ Pᵗ .force ⊢[< i ] Qᵗ .force → R ∗ save b Pᵗ ⊢[ i ] save b Qᵗ
  -- save□ weakens into savex
  save-□⇒x : save□ Pᵗ ⊢[ i ] savex Pᵗ
  -- save□ is persistent
  save□-□ : save□ Pᵗ ⊢[ i ] □ (save□ Pᵗ)
  -- An exclusive save token savex Pᵗ is obtained by allocating Pᵗ
  savex-alloc : Pᵗ .force ⊢[ i ]=>> savex Pᵗ
  -- Persistent save tokens save□ Pᵗ, ... can be obtained
  -- by allocating □ Pᵗ, ... minus the tokens save□ Pᵗ, ... themselves
  save□-alloc-rec : [∗]-map save□ Pᵗs -∗ [∗]-map (λ Pᵗ → □ (Pᵗ .force)) Pᵗs
                      ⊢[ i ]=>> [∗]-map save□ Pᵗs

------------------------------------------------------------------------
-- Persistence: Pers P

record Pers {ℓ} (P : Propˢ ℓ ∞) : Set (suc ℓ) where
  -- P can turn into □ P
  field pers : ∀ {i} → P ⊢[ i ] □ P
open Pers {{...}} public
