{-# OPTIONS --sized-types #-}

module Shog.Logic.Judg where

open import Size
open import Level
open import Data.Empty
open import Data.Bool
open import Codata.Sized.Thunk
open import Shog.Logic.Prop

infix 2 Sequent
syntax Sequent i P Q = P ⊢[ i ] Q

data Sequent {ℓ} (i : Size) : SProp ℓ ∞ → SProp ℓ ∞ → Set (suc ℓ) where
  refl : ∀ {P} → P ⊢[ i ] P
  trans : ∀ {P Q R} → P ⊢[ i ] Q → Q ⊢[ i ] R → P ⊢[ i ] R
  `∀-intro : ∀ {A P Qf} → (∀ x → P ⊢[ i ] Qf x) → P ⊢[ i ] `∀! A Qf
  `∃-elim : ∀ {A Pf Q} → (∀ x → Pf x ⊢[ i ] Q) → `∃! A Pf ⊢[ i ] Q
  `∀-elim : ∀{A Pf x} → `∀! A Pf ⊢[ i ] Pf x
  `∃-intro : ∀{A Pf x} → Pf x ⊢[ i ] `∃! A Pf

private variable
  ℓ : Level
  P Q R : SProp ℓ ∞
  i : Size

-- rules on `∧/`∨/`⊤/`⊥, derived from rules on `∀/`∃

`∧-intro : P ⊢[ i ] Q → P ⊢[ i ] R → P ⊢[ i ] Q `∧ R
`∧-intro H₀ H₁ = `∀-intro (λ { trueU → H₀; falseU → H₁ })

`∨-elim : P ⊢[ i ] R → Q ⊢[ i ] R → P `∨ Q ⊢[ i ] R
`∨-elim H₀ H₁ = `∃-elim (λ { trueU → H₀; falseU → H₁ })

`⊤-intro : P ⊢[ i ] `⊤
`⊤-intro = `∀-intro (λ ())

`⊥-elim : `⊥ ⊢[ i ] P
`⊥-elim = `∃-elim (λ ())

`∧-elim₀ : P `∧ Q ⊢[ i ] P
`∧-elim₀ = `∀-elim

`∧-elim₁ : P `∧ Q ⊢[ i ] Q
`∧-elim₁ = `∀-elim

`∨-intro₀ : P ⊢[ i ] P `∨ Q
`∨-intro₀ = `∃-intro

`∨-intro₁ : Q ⊢[ i ] P `∨ Q
`∨-intro₁ = `∃-intro
