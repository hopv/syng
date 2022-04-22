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
-- Judgment: P ⊢[ ι ]* Jr

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
  Pᶺ Qᶺ : Propˢ< ℓ ∞
  a : A
  F : A → Set ℓ
  b : Bool
  Pᶺs : List (Propˢ< ℓ ∞)

-- Declaring Judg
data Judg {ℓ} (ι : Size) : Propˢ ℓ ∞ → JudgRes ℓ → Set (suc ℓ)

infix 2 _⊢[_]*_ _⊢[_]_ _⊢[<_]_ _⊢[_]=>>_

-- General judgment
_⊢[_]*_ : Propˢ ℓ ∞ → Size → JudgRes ℓ → Set (suc ℓ)
P ⊢[ ι ]* Jr = Judg ι P Jr

-- Sequent
_⊢[_]_ : Propˢ ℓ ∞ → Size → Propˢ ℓ ∞ → Set (suc ℓ)
P ⊢[ ι ] Q = P ⊢[ ι ]* pure Q

-- Sequent under thunk
_⊢[<_]_ : Propˢ ℓ ∞ → Size → Propˢ ℓ ∞ → Set (suc ℓ)
P ⊢[< ι ] Q = Thunk (P ⊢[_] Q) ι

-- Super update
_⊢[_]=>>_ : Propˢ ℓ ∞ → Size → Propˢ ℓ ∞ → Set (suc ℓ)
P ⊢[ ι ]=>> Q = P ⊢[ ι ]* |=>> Q

infixr -1 _»_ _ᵘ»ᵘ_ -- the same fixity with _$_

-- Defining Judg
data Judg {ℓ} ι where
  ----------------------------------------------------------------------
  -- The sequent is reflexive
  idˢ : P ⊢[ ι ] P
  -- The left-hand side of a judgment can be modified with a sequent
  _»_ : P ⊢[ ι ] Q → Q ⊢[ ι ]* Jr → P ⊢[ ι ]* Jr
  ----------------------------------------------------------------------
  -- Introducing ∀ / Eliminating ∃
  ∀-intro : (∀ a → P ⊢[ ι ] Qᶠ a) → P ⊢[ ι ] ∀^ A Qᶠ
  ∃-elim : (∀ a → Pᶠ a ⊢[ ι ]* Jr) → ∃^ A Pᶠ ⊢[ ι ]* Jr
  -- Eliminating ∀ / Introducing ∃
  ∀-elim : ∀^ A Pᶠ ⊢[ ι ] Pᶠ a
  ∃-intro : Pᶠ a ⊢[ ι ] ∃^ A Pᶠ
  -- Unnesting ∀ˢ ... , ∃ˢ ... , ⊤ into ∃ˢ _ ∈ (∀ ...) , ⊤
  ∀∃⇒∃∀-⊤ : ∀ˢ a ∈ A , ∃ˢ _ ∈ F a , ⊤ ⊢[ ι ] ∃ˢ _ ∈ (∀ a → F a) , ⊤
  ----------------------------------------------------------------------
  -- → is the right adjoint of ∧
  →-intro : P ∧ Q ⊢[ ι ] R → Q ⊢[ ι ] P →ˢ R
  →-elim : Q ⊢[ ι ] P →ˢ R → P ∧ Q ⊢[ ι ] R
  ----------------------------------------------------------------------
  -- ∗ is unital w.r.t. ⊤, commutative, associative, and monotone
  ⊤∗-elim : ⊤ ∗ P ⊢[ ι ] P
  ⊤∗-intro : P ⊢[ ι ] ⊤ ∗ P
  ∗-comm : P ∗ Q ⊢[ ι ] Q ∗ P
  ∗-assoc₀ : (P ∗ Q) ∗ R ⊢[ ι ] P ∗ (Q ∗ R)
  ∗-mono₀ : P ⊢[ ι ] Q → P ∗ R ⊢[ ι ] Q ∗ R
  ----------------------------------------------------------------------
  -- -∗ is the right adjoint of ∗
  -∗-intro : P ∗ Q ⊢[ ι ] R → Q ⊢[ ι ] P -∗ R
  -∗-elim : Q ⊢[ ι ] P -∗ R → P ∗ Q ⊢[ ι ] R
  ----------------------------------------------------------------------
  -- |=> is monadic: monotone, increasing, and idempotent
  |=>-mono : P ⊢[ ι ] Q → |=> P ⊢[ ι ] |=> Q
  |=>-intro : P ⊢[ ι ] |=> P
  |=>-join : |=> (|=> P) ⊢[ ι ] |=> P
  -- ∗ can get inside |=>
  |=>-frame₀ : P ∗ |=> Q ⊢[ ι ] |=> (P ∗ Q)
  -- ∃ˢ _ , can get outside |=>
  |=>-∃-out : |=> (∃ˢ _ ∈ A , P) ⊢[ ι ] ∃ˢ _ ∈ A , |=> P
  ----------------------------------------------------------------------
  -- □ is comonadic: monotone, decreasing, and idempotent
  □-mono : P ⊢[ ι ] Q → □ P ⊢[ ι ] □ Q
  □-elim : □ P ⊢[ ι ] P
  □-dup : □ P ⊢[ ι ] □ (□ P)
  -- ∧ can turn into ∗ when one argument is under □
  □₀-∧⇒∗ : □ P ∧ Q ⊢[ ι ] □ P ∗ Q
  -- ∀ can get inside □
  □-∀-in : ∀^ A (□ ∘ Pᶠ) ⊢[ ι ] □ (∀^ A Pᶠ)
  -- ∃ can get outside □
  □-∃-out : □ (∃^ A Pᶠ) ⊢[ ι ] ∃^ A (□ ∘ Pᶠ)
  ----------------------------------------------------------------------
  -- A thunk sequent under |=> can be lifted to a super update =>>
  ᶺ|=>⇒=>> : P ⊢[< ι ] |=> Q → P ⊢[ ι ]=>> Q
  -- The super update =>> is transitive
  _ᵘ»ᵘ_ : P ⊢[ ι ]=>> Q → Q ⊢[ ι ]=>> R → P ⊢[ ι ]=>> R
  -- The super update =>> can frame
  =>>-frame₀ : Q ⊢[ ι ]=>> R → P ∗ Q ⊢[ ι ]=>> P ∗ R
  ----------------------------------------------------------------------
  -- The save token can be modified with a thunk sequent
  save-mono₁ : {{Basic R}} →
    R ∗ Pᶺ .force ⊢[< ι ] Qᶺ .force → R ∗ save b Pᶺ ⊢[ ι ] save b Qᶺ
  -- save□ weakens into savex
  save-□⇒x : save□ Pᶺ ⊢[ ι ] savex Pᶺ
  -- save□ is persistent
  save□-□ : save□ Pᶺ ⊢[ ι ] □ (save□ Pᶺ)
  -- An exclusive save token savex Pᶺ is obtained by allocating Pᶺ
  savex-alloc : Pᶺ .force ⊢[ ι ]=>> savex Pᶺ
  -- Persistent save tokens save□ Pᶺ, ... can be obtained
  -- by allocating □ Pᶺ, ... minus the tokens save□ Pᶺ, ... themselves
  save□-alloc-rec : [∗]-map save□ Pᶺs -∗ [∗]-map (λ Pᶺ → □ (Pᶺ .force)) Pᶺs
                      ⊢[ ι ]=>> [∗]-map save□ Pᶺs

------------------------------------------------------------------------
-- Persistence: Pers P

record Pers {ℓ} (P : Propˢ ℓ ∞) : Set (suc ℓ) where
  -- P can turn into □ P
  field pers : ∀ {ι} → P ⊢[ ι ] □ P
open Pers {{...}} public
