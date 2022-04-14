{-# OPTIONS --sized-types #-}

module Shog.Logic.Judg where

open import Size
open import Level
open import Codata.Sized.Thunk
open import Data.Bool.Base
open import Function.Base

open import Shog.Util
open import Shog.Logic.Prop

data Sequent {ℓ} (i : Size) : Propₛ ℓ ∞ → Propₛ ℓ ∞ → Set (suc ℓ)

infix 2 Sequent
syntax Sequent i P Q = P ⊢[ i ] Q

ThunkSequent : ∀ {ℓ} → Size → Propₛ ℓ ∞ → Propₛ ℓ ∞ → Set (suc ℓ)
ThunkSequent i P Q = Thunk[ j < i ] (Sequent j P Q)
infix 2 ThunkSequent
syntax ThunkSequent i P Q = P ⊢[< i ] Q

data Sequent {ℓ} i where
  reflₛ : ∀ {P} → P ⊢[ i ] P
  transₛ : ∀ {P Q R} → P ⊢[ i ] Q → Q ⊢[ i ] R → P ⊢[ i ] R
  ∀ₛ-intro : ∀ {A P Qf} → (∀ x → P ⊢[ i ] Qf x) → P ⊢[ i ] ∀! A Qf
  ∃ₛ-elim : ∀ {A Pf Q} → (∀ x → Pf x ⊢[ i ] Q) → ∃! A Pf ⊢[ i ] Q
  ∀ₛ-elim : ∀ {A Pf x} → ∀! A Pf ⊢[ i ] Pf x
  ∃ₛ-intro : ∀ {A Pf x} → Pf x ⊢[ i ] ∃! A Pf
  →ₛ-intro : ∀ {P Q R} → P ∧ₛ Q ⊢[ i ] R → P ⊢[ i ] Q →ₛ R
  →ₛ-elim : ∀ {P Q R} → P ⊢[ i ] Q →ₛ R → P ∧ₛ Q ⊢[ i ] R
  ⌈⌉-intro : ∀ {φ P Q} → φ → ⌈ φ ⌉ ∧ₛ P ⊢[ i ] Q → P ⊢[ i ] Q
  ⌈⌉-elim : ∀ {φ P Q} → (φ → P ⊢[ i ] Q) → ⌈ φ ⌉ ∧ₛ P ⊢[ i ] Q
  ∗-unit₀ : ∀ {P} → P ∗ ⊤ₛ ⊢[ i ] P
  ∗-unit₁ : ∀ {P} → P ⊢[ i ] P ∗ ⊤ₛ
  ∗-comm : ∀ {P Q} → P ∗ Q ⊢[ i ] Q ∗ P
  ∗-assoc₀ : ∀ {P Q R} → (P ∗ Q) ∗ R ⊢[ i ] P ∗ (Q ∗ R)
  ∗-mono : ∀ {P Q P' Q'} → P ⊢[ i ] Q → P' ⊢[ i ] Q' → P ∗ P' ⊢[ i ] Q ∗ Q'
  -∗-intro : ∀ {P Q R} → P ∗ Q ⊢[ i ] R → P ⊢[ i ] Q -∗ R
  -∗-elim : ∀ {P Q R} → P ⊢[ i ] Q -∗ R → P ∗ Q ⊢[ i ] R
  □-mono : ∀ {P Q} → P ⊢[ i ] Q → □ P ⊢[ i ] □ Q
  □-elim : ∀ {P} → □ P ⊢[ i ] P
  □-∧⇒∗ : ∀ {P Q} → □ P ∧ₛ Q ⊢[ i ] □ P ∗ Q
  □-dup : ∀ {P} → □ P ⊢[ i ] □ (□ P)
  □-∀-in : ∀ {A Pf} → ∀! A (□ ∘ Pf) ⊢[ i ] □ (∀! A Pf)
  □-∃-out : ∀ {A Pf} → □ (∃! A Pf) ⊢[ i ] ∃! A (□ ∘ Pf)
  □-intro-⌈⌉ : ∀ {φ} → ⌈ φ ⌉ ⊢[ i ] □ ⌈ φ ⌉
  |=>-mono : ∀ {P Q} → P ⊢[ i ] Q → |=> P ⊢[ i ] |=> Q
  |=>-intro : ∀ {P} → P ⊢[ i ] |=> P
  |=>-join : ∀ {P} → |=> (|=> P) ⊢[ i ] |=> P
  |=>-frame : ∀ {P Q} → P ∗ |=> Q ⊢[ i ] |=> (P ∗ Q)
  |=>-pure : ∀ {φ P} → |=> (⌈ φ ⌉ ∧ₛ P) ⊢[ i ] |=> ⌈ φ ⌉ ∧ₛ |=> P
  save-mod-p : ∀ {Pt Qt b} →
                 Pt .force ⊢[< i ] Qt .force → save b Pt ⊢[ i ] save b Qt
  save-mod-b : ∀ {Pt} → save true Pt ⊢[ i ] save false Pt

infixr 10 transₛ
syntax transₛ H₀ H₁ = H₀ |>ₛ H₁

private variable
  ℓ : Level
  i : Size
  P Q R : Propₛ ℓ ∞
  A : Set ℓ
  Pf : A → Propₛ ℓ ∞

∧ₛ-intro : P ⊢[ i ] Q → P ⊢[ i ] R → P ⊢[ i ] Q ∧ₛ R
∧ₛ-intro H₀ H₁ = ∀ₛ-intro (binary H₀ H₁)

∨ₛ-elim : P ⊢[ i ] R → Q ⊢[ i ] R → P ∨ₛ Q ⊢[ i ] R
∨ₛ-elim H₀ H₁ = ∃ₛ-elim (binary H₀ H₁)

⊤ₛ-intro : P ⊢[ i ] ⊤ₛ
⊤ₛ-intro = ∀ₛ-intro nullary

⊥ₛ-elim : ⊥ₛ ⊢[ i ] P
⊥ₛ-elim = ∃ₛ-elim nullary

∧ₛ-elim₀ : P ∧ₛ Q ⊢[ i ] P
∧ₛ-elim₀ = ∀ₛ-elim

∧ₛ-elim₁ : P ∧ₛ Q ⊢[ i ] Q
∧ₛ-elim₁ = ∀ₛ-elim

∨ₛ-intro₀ : P ⊢[ i ] P ∨ₛ Q
∨ₛ-intro₀ = ∃ₛ-intro

∨ₛ-intro₁ : Q ⊢[ i ] P ∨ₛ Q
∨ₛ-intro₁ = ∃ₛ-intro

∗-elim₀ : P ∗ Q ⊢[ i ] P
∗-elim₀ = ∗-mono reflₛ ⊤ₛ-intro |>ₛ ∗-unit₀

∗-elim₁ : P ∗ Q ⊢[ i ] Q
∗-elim₁ = ∗-comm |>ₛ ∗-elim₀

∗-assoc₁ : P ∗ (Q ∗ R) ⊢[ i ] (P ∗ Q) ∗ R
∗-assoc₁ = ∗-comm |>ₛ ∗-mono ∗-comm reflₛ |>ₛ
           ∗-assoc₀ |>ₛ ∗-comm |>ₛ ∗-mono ∗-comm reflₛ

□-intro : □ P ⊢[ i ] Q → □ P ⊢[ i ] □ Q
□-intro H = □-dup |>ₛ □-mono H

□-∀-out : □ (∀! A Pf) ⊢[ i ] ∀! A (□ ∘ Pf)
□-∀-out = ∀ₛ-intro (λ _ → □-mono ∀ₛ-elim)

□-∃-in : ∃! A (□ ∘ Pf) ⊢[ i ] □ (∃! A Pf)
□-∃-in = ∃ₛ-elim (λ _ → □-mono ∃ₛ-intro)

|=>-elim : P ⊢[ i ] |=> Q → |=> P ⊢[ i ] |=> Q
|=>-elim H = |=>-mono H |>ₛ |=>-join
