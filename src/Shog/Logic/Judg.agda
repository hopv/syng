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
  Pf Qf : A → Propˢ ℓ ∞
  Pt Qt : PropTh ℓ ∞
  a : A
  F : A → Set ℓ
  b : Bool
  Pts : List (PropTh ℓ ∞)

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

infixr -1 _»_ _[=>>]»[=>>]_ -- the same fixity with _$_

-- Defining Judg
data Judg {ℓ} i where
  ----------------------------------------------------------------------
  -- Basic rules
  idˢ : P ⊢[ i ] P
  _»_ : P ⊢[ i ] Q → Q ⊢[ i ]* Jr → P ⊢[ i ]* Jr
  ----------------------------------------------------------------------
  -- On ∀/∃
  ∀-intro : (∀ a → P ⊢[ i ] Qf a) → P ⊢[ i ] ∀^ A Qf
  ∃-elim : (∀ a → Pf a ⊢[ i ]* Jr) → ∃^ A Pf ⊢[ i ]* Jr
  ∀-elim : ∀^ A Pf ⊢[ i ] Pf a
  ∃-intro : Pf a ⊢[ i ] ∃^ A Pf
  ∀∃⇒∃∀-⊤ : ∀ {A : Set ℓ} {F : A → Set ℓ} →
    ∀ˢ a ∈ A , ∃ˢ _ ∈ F a , ⊤ˢ ⊢[ i ] ∃ˢ _ ∈ (∀ a → F a) , ⊤ˢ
  ----------------------------------------------------------------------
  -- On →
  →-intro : P ∧ˢ Q ⊢[ i ] R → Q ⊢[ i ] P →ˢ R
  →-elim : Q ⊢[ i ] P →ˢ R → P ∧ˢ Q ⊢[ i ] R
  ----------------------------------------------------------------------
  -- On ∗
  ∗⊤-elim : P ∗ ⊤ˢ ⊢[ i ] P
  ∗⊤-intro : P ⊢[ i ] P ∗ ⊤ˢ
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
  □-∀-in : ∀^ A (□ ∘ Pf) ⊢[ i ] □ (∀^ A Pf)
  □-∃-out : □ (∃^ A Pf) ⊢[ i ] ∃^ A (□ ∘ Pf)
  ----------------------------------------------------------------------
  -- On the super update
  <'|=>⇒=>> : P ⊢[< i ] |=> Q → P ⊢[ i ]=>> Q
  _[=>>]»[=>>]_ : P ⊢[ i ]=>> Q → Q ⊢[ i ]=>> R → P ⊢[ i ]=>> R
  =>>-frame₀ : Q ⊢[ i ]=>> R → P ∗ Q ⊢[ i ]=>> P ∗ R
  ----------------------------------------------------------------------
  -- On the save token
  save-mono₁ : {{Basic R}} →
    R ∗ Pt .force ⊢[< i ] Qt .force → save b Pt ⊢[ i ] save b Qt
  save-□⇒x : save□ Pt ⊢[ i ] savex Pt
  save□-□ : save□ Pt ⊢[ i ] □ (save□ Pt)
  savex-alloc : Pt .force ⊢[ i ]=>> savex Pt
  save□-alloc-rec : [∗]-map save□ Pts -∗ [∗]-map (λ Pt → □ (Pt .force)) Pts
      ⊢[ i ]=>> [∗]-map save□ Pts

------------------------------------------------------------------------
-- Persistence: Pers P

record Pers {ℓ} (P : Propˢ ℓ ∞) : Set (suc ℓ) where
  field pers : ∀ {i} → P ⊢[ i ] □ P
open Pers {{...}} public
