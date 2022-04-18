------------------------------------------------------------------------
-- Judgment in Shog
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Logic.Judg where

open import Level using (Level; suc)
open import Size using (Size; ∞)
open import Codata.Sized.Thunk using (Thunk; force)
open import Function.Base using (_∘_)
open import Data.List.Base using (List)

open import Shog.Logic.Prop

private variable
  ℓ : Level

------------------------------------------------------------------------
-- Judgment: P ⊢[ i ]* Jr

-- Result of a judgment
data JudgRes ℓ : Set (suc ℓ) where
  -- Just a proposition
  pure : Propₛ ℓ ∞ → JudgRes ℓ
  -- Under the super update
  |=>> : Propₛ ℓ ∞ → JudgRes ℓ

-- Declaring Judg
data Judg {ℓ} (i : Size) : Propₛ ℓ ∞ → JudgRes ℓ → Set (suc ℓ)

-- Notation

infix 2 _⊢[_]*_ _⊢[_]_ _⊢[<_]_ _⊢[_]=>>_

_⊢[_]*_ : Propₛ ℓ ∞ → Size → JudgRes ℓ → Set (suc ℓ)
P ⊢[ i ]* Jr = Judg i P Jr

_⊢[_]_ : Propₛ ℓ ∞ → Size → Propₛ ℓ ∞ → Set (suc ℓ)
P ⊢[ i ] Q = P ⊢[ i ]* pure Q

_⊢[<_]_ : Propₛ ℓ ∞ → Size → Propₛ ℓ ∞ → Set (suc ℓ)
P ⊢[< i ] Q = Thunk (P ⊢[_] Q) i

_⊢[_]=>>_ : Propₛ ℓ ∞ → Size → Propₛ ℓ ∞ → Set (suc ℓ)
P ⊢[ i ]=>> Q = P ⊢[ i ]* |=>> Q

infixr -1 _»_ _[=>>]»[=>>]_ -- the same fixity with _$_

-- Defining Judg
data Judg {ℓ} i where
  ----------------------------------------------------------------------
  -- Basic rules
  idₛ : ∀ {P} → P ⊢[ i ] P
  _»_ : ∀ {P Q Jr} → P ⊢[ i ] Q → Q ⊢[ i ]* Jr → P ⊢[ i ]* Jr
  ----------------------------------------------------------------------
  -- On ∀/∃
  ∀-intro : ∀ {A P Qf} → (∀ a → P ⊢[ i ] Qf a) → P ⊢[ i ] ∀^ A Qf
  ∃-elim : ∀ {A Pf Jr} → (∀ a → Pf a ⊢[ i ]* Jr) → ∃^ A Pf ⊢[ i ]* Jr
  ∀-elim : ∀ {A Pf a} → ∀^ A Pf ⊢[ i ] Pf a
  ∃-intro : ∀ {A Pf a} → Pf a ⊢[ i ] ∃^ A Pf
  ∀∃⇒∃∀-⊤ : ∀ {A : Set ℓ} {F : A → Set ℓ} →
    ∀ₛ a ∈ A , ∃ₛ _ ∈ F a , ⊤ₛ ⊢[ i ] ∃ₛ _ ∈ (∀ a → F a) , ⊤ₛ
  ----------------------------------------------------------------------
  -- On →
  →-intro : ∀ {P Q R} → P ∧ₛ Q ⊢[ i ] R → Q ⊢[ i ] P →ₛ R
  →-elim : ∀ {P Q R} → Q ⊢[ i ] P →ₛ R → P ∧ₛ Q ⊢[ i ] R
  ----------------------------------------------------------------------
  -- On ∗
  ∗⊤-elim : ∀ {P} → P ∗ ⊤ₛ ⊢[ i ] P
  ∗⊤-intro : ∀ {P} → P ⊢[ i ] P ∗ ⊤ₛ
  ∗-comm : ∀ {P Q} → P ∗ Q ⊢[ i ] Q ∗ P
  ∗-assoc₀ : ∀ {P Q R} → (P ∗ Q) ∗ R ⊢[ i ] P ∗ (Q ∗ R)
  ∗-mono₀ : ∀ {P Q R} → P ⊢[ i ] Q → P ∗ R ⊢[ i ] Q ∗ R
  ----------------------------------------------------------------------
  -- On -∗
  -∗-intro : ∀ {P Q R} → P ∗ Q ⊢[ i ] R → Q ⊢[ i ] P -∗ R
  -∗-elim : ∀ {P Q R} → Q ⊢[ i ] P -∗ R → P ∗ Q ⊢[ i ] R
  ----------------------------------------------------------------------
  -- On |=>
  |=>-mono : ∀ {P Q} → P ⊢[ i ] Q → |=> P ⊢[ i ] |=> Q
  |=>-intro : ∀ {P} → P ⊢[ i ] |=> P
  |=>-join : ∀ {P} → |=> (|=> P) ⊢[ i ] |=> P
  |=>-frame₀ : ∀ {P Q} → P ∗ |=> Q ⊢[ i ] |=> (P ∗ Q)
  |=>-∃-out : ∀ {A P} → |=> (∃ₛ _ ∈ A , P) ⊢[ i ] ∃ₛ _ ∈ A , |=> P
  ----------------------------------------------------------------------
  -- On □
  □-mono : ∀ {P Q} → P ⊢[ i ] Q → □ P ⊢[ i ] □ Q
  □-elim : ∀ {P} → □ P ⊢[ i ] P
  □-dup : ∀ {P} → □ P ⊢[ i ] □ (□ P)
  □₀-∧⇒∗ : ∀ {P Q} → □ P ∧ₛ Q ⊢[ i ] □ P ∗ Q
  □-∀-in : ∀ {A Pf} → ∀^ A (□ ∘ Pf) ⊢[ i ] □ (∀^ A Pf)
  □-∃-out : ∀ {A Pf} → □ (∃^ A Pf) ⊢[ i ] ∃^ A (□ ∘ Pf)
  ----------------------------------------------------------------------
  -- On the super update
  <'|=>⇒=>> : ∀ {P Q} → P ⊢[< i ] |=> Q → P ⊢[ i ]=>> Q
  _[=>>]»[=>>]_ : ∀ {P Q R} → P ⊢[ i ]=>> Q → Q ⊢[ i ]=>> R → P ⊢[ i ]=>> R
  =>>-frame₀ : ∀ {P Q R} → Q ⊢[ i ]=>> R → P ∗ Q ⊢[ i ]=>> P ∗ R
  ----------------------------------------------------------------------
  -- On the save token
  save-mono₁ : ∀ {Pt Qt b} →
    Pt .force ⊢[< i ] Qt .force → save b Pt ⊢[ i ] save b Qt
  save-□⇒x : ∀ {Pt} → save□ Pt ⊢[ i ] savex Pt
  save□-□ : ∀ {Pt} → save□ Pt ⊢[ i ] □ (save□ Pt)
  savex-alloc : ∀ {Pt} → Pt .force ⊢[ i ]=>> savex Pt
  save□-alloc-rec : ∀ {Pts} →
    [∗]-map save□ Pts -∗ [∗]-map (λ Pt → □ (Pt .force)) Pts
      ⊢[ i ]=>> [∗]-map save□ Pts

------------------------------------------------------------------------
-- Persistence: Pers P

record Pers {ℓ} (P : Propₛ ℓ ∞) : Set (suc ℓ) where
  field pers : ∀ {i} → P ⊢[ i ] □ P
open Pers {{...}} public
