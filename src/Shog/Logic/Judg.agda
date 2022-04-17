------------------------------------------------------------------------
-- Judgments in Shog
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Logic.Judg where

open import Level using (Level; suc)
open import Size using (Size; ∞)
open import Codata.Sized.Thunk using (Thunk; force)
open import Data.Bool.Base using (Bool; true; false)
open import Function.Base using (_∘_)

open import Shog.Util
open import Shog.Logic.Prop

private variable
  ℓ : Level

------------------------------------------------------------------------
-- Judgments

data Sequent {ℓ} (i : Size) : Propₛ ℓ ∞ → Propₛ ℓ ∞ → Set (suc ℓ)

------------------------------------------------------------------------
-- Sequent: P ⊢[ i ] Q

infix 2 _⊢[_]_ _⊢[<_]_

_⊢[_]_ : Propₛ ℓ ∞ → Size → Propₛ ℓ ∞ → Set (suc ℓ)
P ⊢[ i ] Q = Sequent i P Q

_⊢[<_]_ : Propₛ ℓ ∞ → Size → Propₛ ℓ ∞ → Set (suc ℓ)
P ⊢[< i ] Q = Thunk (P ⊢[_] Q) i

-- To make it compatible with $
infixr -1 _»_

data Sequent {ℓ} i where
  reflₛ : ∀ {P} → P ⊢[ i ] P
  _»_ : ∀ {P Q R} → P ⊢[ i ] Q → Q ⊢[ i ] R → P ⊢[ i ] R
  ∀-intro : ∀ {A P Qf} → (∀ a → P ⊢[ i ] Qf a) → P ⊢[ i ] ∀^ A Qf
  ∃-elim : ∀ {A Pf Q} → (∀ a → Pf a ⊢[ i ] Q) → ∃^ A Pf ⊢[ i ] Q
  ∀-elim : ∀ {A Pf a} → ∀^ A Pf ⊢[ i ] Pf a
  ∃-intro : ∀ {A Pf a} → Pf a ⊢[ i ] ∃^ A Pf
  ∀∃⇒∃∀-⊤ : ∀ {A : Set ℓ} {F : A → Set ℓ} →
    ∀ₛ a ∈ A , ∃ₛ _ ∈ F a , ⊤ₛ ⊢[ i ] ∃ₛ _ ∈ (∀ a → F a) , ⊤ₛ
  →-intro : ∀ {P Q R} → P ∧ₛ Q ⊢[ i ] R → Q ⊢[ i ] P →ₛ R
  →-elim : ∀ {P Q R} → Q ⊢[ i ] P →ₛ R → P ∧ₛ Q ⊢[ i ] R
  ∗⊤-elim : ∀ {P} → P ∗ ⊤ₛ ⊢[ i ] P
  ∗⊤-intro : ∀ {P} → P ⊢[ i ] P ∗ ⊤ₛ
  ∗-comm : ∀ {P Q} → P ∗ Q ⊢[ i ] Q ∗ P
  ∗-assoc₀ : ∀ {P Q R} → (P ∗ Q) ∗ R ⊢[ i ] P ∗ (Q ∗ R)
  ∗-mono₀ : ∀ {P Q R} → P ⊢[ i ] Q → P ∗ R ⊢[ i ] Q ∗ R
  -∗-intro : ∀ {P Q R} → P ∗ Q ⊢[ i ] R → Q ⊢[ i ] P -∗ R
  -∗-elim : ∀ {P Q R} → Q ⊢[ i ] P -∗ R → P ∗ Q ⊢[ i ] R
  □-mono : ∀ {P Q} → P ⊢[ i ] Q → □ P ⊢[ i ] □ Q
  □-elim : ∀ {P} → □ P ⊢[ i ] P
  □-dup : ∀ {P} → □ P ⊢[ i ] □ (□ P)
  □₀-∧⇒∗ : ∀ {P Q} → □ P ∧ₛ Q ⊢[ i ] □ P ∗ Q
  □-∀-in : ∀ {A Pf} → ∀^ A (□ ∘ Pf) ⊢[ i ] □ (∀^ A Pf)
  □-∃-out : ∀ {A Pf} → □ (∃^ A Pf) ⊢[ i ] ∃^ A (□ ∘ Pf)
  |=>-mono : ∀ {P Q} → P ⊢[ i ] Q → |=> P ⊢[ i ] |=> Q
  |=>-intro : ∀ {P} → P ⊢[ i ] |=> P
  |=>-join : ∀ {P} → |=> (|=> P) ⊢[ i ] |=> P
  |=>-∗-in : ∀ {P Q} → P ∗ |=> Q ⊢[ i ] |=> (P ∗ Q)
  |=>-∃-out : ∀ {A P} → |=> (∃ₛ _ ∈ A , P) ⊢[ i ] ∃ₛ _ ∈ A , |=> P
  save-mono₁ : ∀ {Pt Qt b} →
    Pt .force ⊢[< i ] Qt .force → save b Pt ⊢[ i ] save b Qt
  save-true⇒false : ∀ {Pt} → save true Pt ⊢[ i ] save false Pt
  □-intro-save : ∀ {Pt} → save true Pt ⊢[ i ] □ (save true Pt)
