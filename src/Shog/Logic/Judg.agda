{-# OPTIONS --sized-types #-}

module Shog.Logic.Judg where

open import Size
open import Level
open import Codata.Sized.Thunk

open import Shog.Util
open import Shog.Logic.Prop

infix 2 Sequent
syntax Sequent i P Q = P ⊢[ i ] Q

data Sequent {ℓ} (i : Size) : SProp ℓ ∞ → SProp ℓ ∞ → Set (suc ℓ) where
  reflₛ : ∀ {P} → P ⊢[ i ] P
  transₛ : ∀ {P Q R} → P ⊢[ i ] Q → Q ⊢[ i ] R → P ⊢[ i ] R
  ∀ₛ-intro : ∀ {A P Qf} → (∀ x → P ⊢[ i ] Qf x) → P ⊢[ i ] ∀! A Qf
  ∃ₛ-elim : ∀ {A Pf Q} → (∀ x → Pf x ⊢[ i ] Q) → ∃! A Pf ⊢[ i ] Q
  ∀ₛ-elim : ∀{A Pf x} → ∀! A Pf ⊢[ i ] Pf x
  ∃ₛ-intro : ∀{A Pf x} → Pf x ⊢[ i ] ∃! A Pf

private variable
  ℓ : Level
  P Q R : SProp ℓ ∞
  i : Size

-- rules on ∧/∨/⊤/⊥, derived from rules on ∀/∃

∧ₛ-intro : P ⊢[ i ] Q → P ⊢[ i ] R → P ⊢[ i ] Q ∧ₛ R
∧ₛ-intro H₀ H₁ = ∀ₛ-intro (binary-dep H₀ H₁)

∨ₛ-elim : P ⊢[ i ] R → Q ⊢[ i ] R → P ∨ₛ Q ⊢[ i ] R
∨ₛ-elim H₀ H₁ = ∃ₛ-elim (binary-dep H₀ H₁)

⊤ₛ-intro : P ⊢[ i ] ⊤ₛ
⊤ₛ-intro = ∀ₛ-intro nullary-dep

⊥ₛ-elim : ⊥ₛ ⊢[ i ] P
⊥ₛ-elim = ∃ₛ-elim nullary-dep

∧ₛ-elim₀ : P ∧ₛ Q ⊢[ i ] P
∧ₛ-elim₀ = ∀ₛ-elim

∧ₛ-elim₁ : P ∧ₛ Q ⊢[ i ] Q
∧ₛ-elim₁ = ∀ₛ-elim

∨ₛ-intro₀ : P ⊢[ i ] P ∨ₛ Q
∨ₛ-intro₀ = ∃ₛ-intro

∨ₛ-intro₁ : Q ⊢[ i ] P ∨ₛ Q
∨ₛ-intro₁ = ∃ₛ-intro
