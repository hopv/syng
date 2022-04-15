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
  ∀-intro : ∀ {A P Qf} → (∀ x → P ⊢[ i ] Qf x) → P ⊢[ i ] ∀! A Qf
  ∃-elim : ∀ {A Pf Q} → (∀ x → Pf x ⊢[ i ] Q) → ∃! A Pf ⊢[ i ] Q
  ∀-elim : ∀ {A Pf x} → ∀! A Pf ⊢[ i ] Pf x
  ∃-intro : ∀ {A Pf x} → Pf x ⊢[ i ] ∃! A Pf
  →-intro : ∀ {P Q R} → P ∧ₛ Q ⊢[ i ] R → Q ⊢[ i ] P →ₛ R
  →-elim : ∀ {P Q R} → Q ⊢[ i ] P →ₛ R → P ∧ₛ Q ⊢[ i ] R
  ⌜⌝-intro : ∀ {φ P Q} → φ → ⌜ φ ⌝ ∧ₛ P ⊢[ i ] Q → P ⊢[ i ] Q
  ⌜⌝-elim : ∀ {φ P Q} → (φ → P ⊢[ i ] Q) → ⌜ φ ⌝ ∧ₛ P ⊢[ i ] Q
  ∗-unit₀ : ∀ {P} → P ∗ ⊤ₛ ⊢[ i ] P
  ∗-unit₁ : ∀ {P} → P ⊢[ i ] P ∗ ⊤ₛ
  ∗-comm : ∀ {P Q} → P ∗ Q ⊢[ i ] Q ∗ P
  ∗-assoc₀ : ∀ {P Q R} → (P ∗ Q) ∗ R ⊢[ i ] P ∗ (Q ∗ R)
  ∗-mono₀ : ∀ {P Q R} → P ⊢[ i ] Q → P ∗ R ⊢[ i ] Q ∗ R
  -∗-intro : ∀ {P Q R} → P ∗ Q ⊢[ i ] R → Q ⊢[ i ] P -∗ R
  -∗-elim : ∀ {P Q R} → Q ⊢[ i ] P -∗ R → P ∗ Q ⊢[ i ] R
  □-mono : ∀ {P Q} → P ⊢[ i ] Q → □ P ⊢[ i ] □ Q
  □-elim : ∀ {P} → □ P ⊢[ i ] P
  □-dup : ∀ {P} → □ P ⊢[ i ] □ (□ P)
  □₀-∧⇒∗ : ∀ {P Q} → □ P ∧ₛ Q ⊢[ i ] □ P ∗ Q
  □-∀-in : ∀ {A Pf} → ∀! A (□ ∘ Pf) ⊢[ i ] □ (∀! A Pf)
  □-∃-out : ∀ {A Pf} → □ (∃! A Pf) ⊢[ i ] ∃! A (□ ∘ Pf)
  □-intro-⌜⌝ : ∀ {φ} → ⌜ φ ⌝ ⊢[ i ] □ ⌜ φ ⌝
  |=>-mono : ∀ {P Q} → P ⊢[ i ] Q → |=> P ⊢[ i ] |=> Q
  |=>-intro : ∀ {P} → P ⊢[ i ] |=> P
  |=>-join : ∀ {P} → |=> (|=> P) ⊢[ i ] |=> P
  |=>-∗-in : ∀ {P Q} → P ∗ |=> Q ⊢[ i ] |=> (P ∗ Q)
  |=>-⌜⌝-out : ∀ {φ P} → |=> (⌜ φ ⌝ ∧ₛ P) ⊢[ i ] |=> ⌜ φ ⌝ ∧ₛ |=> P
  save-mod-p : ∀ {Pt Qt b} →
                 Pt .force ⊢[< i ] Qt .force → save b Pt ⊢[ i ] save b Qt
  save-mod-b : ∀ {Pt} → save true Pt ⊢[ i ] save false Pt

infixr 0 transₛ
syntax transₛ H₀ H₁ = H₀ »ₛ H₁

-- derived rules

private variable
  ℓ : Level
  i : Size
  P Q R P' Q' : Propₛ ℓ ∞
  A : Set ℓ
  Pf Qf : A → Propₛ ℓ ∞

---- ∀/∃

∧-intro : P ⊢[ i ] Q → P ⊢[ i ] R → P ⊢[ i ] Q ∧ₛ R
∧-intro H₀ H₁ = ∀-intro $ binary H₀ H₁

∨-elim : P ⊢[ i ] R → Q ⊢[ i ] R → P ∨ₛ Q ⊢[ i ] R
∨-elim H₀ H₁ = ∃-elim $ binary H₀ H₁

⊤-intro : P ⊢[ i ] ⊤ₛ
⊤-intro = ∀-intro nullary

⊥-elim : ⊥ₛ ⊢[ i ] P
⊥-elim = ∃-elim nullary

∧-elim₀ : P ∧ₛ Q ⊢[ i ] P
∧-elim₀ = ∀-elim

∧-elim₁ : P ∧ₛ Q ⊢[ i ] Q
∧-elim₁ = ∀-elim

∨-intro₀ : P ⊢[ i ] P ∨ₛ Q
∨-intro₀ = ∃-intro

∨-intro₁ : Q ⊢[ i ] P ∨ₛ Q
∨-intro₁ = ∃-intro

---- ∗

∗-mono₁ : P ⊢[ i ] Q → R ∗ P ⊢[ i ] R ∗ Q
∗-mono₁ H = ∗-comm »ₛ ∗-mono₀ H »ₛ ∗-comm

∗-mono : P ⊢[ i ] Q → P' ⊢[ i ] Q' → P ∗ P' ⊢[ i ] Q ∗ Q'
∗-mono H₀ H₁ = ∗-mono₀ H₀ »ₛ ∗-mono₁ H₁

∗-elim₀ : P ∗ Q ⊢[ i ] P
∗-elim₀ = ∗-mono₁ ⊤-intro »ₛ ∗-unit₀

∗-elim₁ : P ∗ Q ⊢[ i ] Q
∗-elim₁ = ∗-comm »ₛ ∗-elim₀

∗-assoc₁ : P ∗ (Q ∗ R) ⊢[ i ] (P ∗ Q) ∗ R
∗-assoc₁ = ∗-comm »ₛ ∗-mono₀ ∗-comm »ₛ ∗-assoc₀ »ₛ ∗-comm »ₛ ∗-mono₀ ∗-comm

∗-∃-out : P ∗ ∃!' Qf ⊢[ i ] ∃ₛ x , P ∗ Qf x
∗-∃-out = -∗-elim $ ∃-elim λ _ → -∗-intro ∃-intro

∗⇒∧ : P ∗ Q ⊢[ i ] P ∧ₛ Q
∗⇒∧ = ∧-intro ∗-elim₀ ∗-elim₁

→ₛ⇒-∗ : P →ₛ Q ⊢[ i ] P -∗ Q
→ₛ⇒-∗ = -∗-intro $ ∗⇒∧ »ₛ →-elim reflₛ

---- □

□-intro : □ P ⊢[ i ] Q → □ P ⊢[ i ] □ Q
□-intro H = □-dup »ₛ □-mono H

□-∀-out : □ (∀! _ Pf) ⊢[ i ] ∀! _ (□ ∘ Pf)
□-∀-out = ∀-intro $ λ _ → □-mono ∀-elim

□-∃-in : ∃! A (□ ∘ Pf) ⊢[ i ] □ (∃! A Pf)
□-∃-in = ∃-elim $ λ _ → □-mono ∃-intro

□-∧-out : □ (P ∧ₛ Q) ⊢[ i ] □ P ∧ₛ □ Q
□-∧-out = ∧-intro (□-mono ∧-elim₀) (□-mono ∧-elim₁)

□-∨-in : □ P ∨ₛ □ Q ⊢[ i ] □ (P ∨ₛ Q)
□-∨-in = ∨-elim (□-mono ∨-intro₀) (□-mono ∨-intro₁)

□-⊥-elim : □ ⊥ₛ ⊢[ i ] P
□-⊥-elim = □-elim »ₛ ⊥-elim

------ with □₀-∧⇒∗

□₁-∧⇒∗ : P ∧ₛ □ Q ⊢[ i ] P ∗ □ Q
□₁-∧⇒∗ = ∧-intro ∧-elim₁ ∧-elim₀ »ₛ □₀-∧⇒∗ »ₛ ∗-comm

retain-□ : P ⊢[ i ] □ Q → P ⊢[ i ] □ Q ∗ P
retain-□ H = ∧-intro H reflₛ »ₛ □₀-∧⇒∗

dup-□ : □ P ⊢[ i ] □ P ∗ □ P
dup-□ = retain-□ reflₛ

□--∗⇒→ : □ P -∗ Q ⊢[ i ] □ P →ₛ Q
□--∗⇒→ = →-intro $ □₀-∧⇒∗ »ₛ -∗-elim reflₛ

in□--∗⇒→ : □ (P -∗ Q) ⊢[ i ] □ (P →ₛ Q)
in□--∗⇒→ = □-intro $ →-intro $ □₁-∧⇒∗ »ₛ -∗-elim □-elim

□-∗-out : □ (P ∗ Q) ⊢[ i ] □ P ∗ □ Q
□-∗-out = □-mono ∗⇒∧ »ₛ □-∧-out »ₛ □₀-∧⇒∗

------ with □-∀-in/□-∃-out

□-∧-in : □ P ∧ₛ □ Q ⊢[ i ] □ (P ∧ₛ Q)
□-∧-in = ∀-intro (binary ∧-elim₀ ∧-elim₁) »ₛ □-∀-in

□-∨-out : □ (P ∨ₛ Q) ⊢[ i ] □ P ∨ₛ □ Q
□-∨-out = □-∃-out »ₛ ∃-elim (binary ∨-intro₀ ∨-intro₁)

□-⊤-intro : P ⊢[ i ] □ ⊤ₛ
□-⊤-intro = ∀-intro nullary »ₛ □-∀-in

in□-∧⇒∗ : □ (P ∧ₛ Q) ⊢[ i ] □ (P ∗ Q)
in□-∧⇒∗ = □-intro $ dup-□ »ₛ ∗-mono (□-elim »ₛ ∧-elim₀) (□-elim »ₛ ∧-elim₁)

□-∗-in : □ P ∗ □ Q ⊢[ i ] □ (P ∗ Q)
□-∗-in = ∗⇒∧ »ₛ □-∧-in »ₛ in□-∧⇒∗

|=>-elim : P ⊢[ i ] |=> Q → |=> P ⊢[ i ] |=> Q
|=>-elim H = |=>-mono H »ₛ |=>-join
