------------------------------------------------------------------------
-- Judgments in Shog
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Sequent: P ⊢[ i ] Q

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

----------------------------------------------------------------------
-- Derived rules

private variable
  ℓ : Level
  i : Size
  P Q R P' Q' : Propₛ ℓ ∞
  A φ : Set ℓ
  Pf Qf : A → Propₛ ℓ ∞

-- On ∀ₛ/∃ₛ/∧ₛ/∨ₛ/⊤ₛ/⊥ₛ

∧-intro : P ⊢[ i ] Q → P ⊢[ i ] R → P ⊢[ i ] Q ∧ₛ R
∧-intro P⊢Q P⊢R = ∀-intro $ binary P⊢Q P⊢R

∨-elim : P ⊢[ i ] R → Q ⊢[ i ] R → P ∨ₛ Q ⊢[ i ] R
∨-elim P⊢Q Q⊢R = ∃-elim $ binary P⊢Q Q⊢R

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

∀-mono : (∀ x → Pf x ⊢[ i ] Qf x) → ∀!' Pf ⊢[ i ] ∀!' Qf
∀-mono Pf⊢Qf = ∀-intro $ λ x → ∀-elim »ₛ Pf⊢Qf x

∃-mono : (∀ x → Pf x ⊢[ i ] Qf x) → ∃!' Pf ⊢[ i ] ∃!' Qf
∃-mono Pf⊢Qf = ∃-elim $ λ x → Pf⊢Qf x »ₛ ∃-intro

∧-mono : P ⊢[ i ] Q → P' ⊢[ i ] Q' → P ∧ₛ P' ⊢[ i ] Q ∧ₛ Q'
∧-mono P⊢Q P'⊢Q' = ∧-intro (∧-elim₀ »ₛ P⊢Q) (∧-elim₁ »ₛ P'⊢Q')

∨-mono : P ⊢[ i ] Q → P' ⊢[ i ] Q' → P ∨ₛ P' ⊢[ i ] Q ∨ₛ Q'
∨-mono P⊢Q P'⊢Q' = ∨-elim (P⊢Q »ₛ ∨-intro₀) (P'⊢Q' »ₛ ∨-intro₁)

∧-mono₀ : P ⊢[ i ] Q → P ∧ₛ R ⊢[ i ] Q ∧ₛ R
∧-mono₀ P⊢Q = ∧-mono P⊢Q reflₛ

∧-mono₁ : P ⊢[ i ] Q → R ∧ₛ P ⊢[ i ] R ∧ₛ Q
∧-mono₁ P⊢Q = ∧-mono reflₛ P⊢Q

∨-mono₀ : P ⊢[ i ] Q → P ∨ₛ R ⊢[ i ] Q ∨ₛ R
∨-mono₀ P⊢Q = ∨-mono P⊢Q reflₛ

∨-mono₁ : P ⊢[ i ] Q → R ∨ₛ P ⊢[ i ] R ∨ₛ Q
∨-mono₁ P⊢Q = ∨-mono reflₛ P⊢Q

∧-comm : P ∧ₛ Q ⊢[ i ] Q ∧ₛ P
∧-comm = ∧-intro ∧-elim₁ ∧-elim₀

∨-comm : P ∨ₛ Q ⊢[ i ] Q ∨ₛ P
∨-comm = ∨-elim ∨-intro₁ ∨-intro₀

∧-assoc₀ : (P ∧ₛ Q) ∧ₛ R ⊢[ i ] P ∧ₛ (Q ∧ₛ R)
∧-assoc₀ = ∧-intro (∧-elim₀ »ₛ ∧-elim₀) $
            ∧-intro (∧-elim₀ »ₛ ∧-elim₁) ∧-elim₁

∧-assoc₁ : P ∧ₛ (Q ∧ₛ R) ⊢[ i ] (P ∧ₛ Q) ∧ₛ R
∧-assoc₁ = ∧-intro (∧-intro ∧-elim₀ $ ∧-elim₁ »ₛ ∧-elim₀) $
            ∧-elim₁ »ₛ ∧-elim₁

∨-assoc₀ : (P ∨ₛ Q) ∨ₛ R ⊢[ i ] P ∨ₛ (Q ∨ₛ R)
∨-assoc₀ = ∨-elim (∨-elim ∨-intro₀ $ ∨-intro₀ »ₛ ∨-intro₁) $
            ∨-intro₁ »ₛ ∨-intro₁

∨-assoc₁ : P ∨ₛ (Q ∨ₛ R) ⊢[ i ] (P ∨ₛ Q) ∨ₛ R
∨-assoc₁ = ∨-elim (∨-intro₀ »ₛ ∨-intro₀) $
            ∨-elim (∨-intro₁ »ₛ ∨-intro₀) $ ∨-intro₁

-- On →ₛ

→-apply : P ∧ₛ (P →ₛ Q) ⊢[ i ] Q
→-apply = →-elim reflₛ

→-mono : Q ⊢[ i ] P → P' ⊢[ i ] Q' → P →ₛ P' ⊢[ i ] Q →ₛ Q'
→-mono Q⊢P P'⊢Q' = →-intro $ ∧-mono₀ Q⊢P »ₛ →-apply »ₛ P'⊢Q'

→-mono₀ : Q ⊢[ i ] P → P →ₛ R ⊢[ i ] Q →ₛ R
→-mono₀ Q⊢P = →-mono Q⊢P reflₛ

→-mono₁ : P ⊢[ i ] Q → R →ₛ P ⊢[ i ] R →ₛ Q
→-mono₁ P⊢Q = →-mono reflₛ P⊢Q

-- On ∗

∗-mono₁ : P ⊢[ i ] Q → R ∗ P ⊢[ i ] R ∗ Q
∗-mono₁ P⊢Q = ∗-comm »ₛ ∗-mono₀ P⊢Q »ₛ ∗-comm

∗-mono : P ⊢[ i ] Q → P' ⊢[ i ] Q' → P ∗ P' ⊢[ i ] Q ∗ Q'
∗-mono P⊢Q P'⊢Q' = ∗-mono₀ P⊢Q »ₛ ∗-mono₁ P'⊢Q'

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

→⇒-∗ : P →ₛ Q ⊢[ i ] P -∗ Q
→⇒-∗ = -∗-intro $ ∗⇒∧ »ₛ →-elim reflₛ

-- On -∗

-∗-apply : P ∗ (P -∗ Q) ⊢[ i ] Q
-∗-apply = -∗-elim reflₛ

-∗-mono : Q ⊢[ i ] P → P' ⊢[ i ] Q' → P -∗ P' ⊢[ i ] Q -∗ Q'
-∗-mono Q⊢P P'⊢Q' = -∗-intro $ ∗-mono₀ Q⊢P »ₛ -∗-apply »ₛ P'⊢Q'

-∗-mono₀ : Q ⊢[ i ] P → P -∗ R ⊢[ i ] Q -∗ R
-∗-mono₀ Q⊢P = -∗-mono Q⊢P reflₛ

-∗-mono₁ : P ⊢[ i ] Q → R -∗ P ⊢[ i ] R -∗ Q
-∗-mono₁ P⊢Q = -∗-mono reflₛ P⊢Q

-- On □

□-intro : □ P ⊢[ i ] Q → □ P ⊢[ i ] □ Q
□-intro □P⊢Q = □-dup »ₛ □-mono □P⊢Q

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

-- -- with □₀-∧⇒∗

□₁-∧⇒∗ : P ∧ₛ □ Q ⊢[ i ] P ∗ □ Q
□₁-∧⇒∗ = ∧-comm »ₛ □₀-∧⇒∗ »ₛ ∗-comm

retain-□ : P ⊢[ i ] □ Q → P ⊢[ i ] □ Q ∗ P
retain-□ P⊢Q = ∧-intro P⊢Q reflₛ »ₛ □₀-∧⇒∗

dup-□ : □ P ⊢[ i ] □ P ∗ □ P
dup-□ = retain-□ reflₛ

□-∗-out : □ (P ∗ Q) ⊢[ i ] □ P ∗ □ Q
□-∗-out = □-mono ∗⇒∧ »ₛ □-∧-out »ₛ □₀-∧⇒∗

in□-∧⇒∗ : □ (P ∧ₛ Q) ⊢[ i ] □ (P ∗ Q)
in□-∧⇒∗ = □-intro $ dup-□ »ₛ ∗-mono (□-elim »ₛ ∧-elim₀) (□-elim »ₛ ∧-elim₁)

-∗⇒□→ : P -∗ Q ⊢[ i ] □ P →ₛ Q
-∗⇒□→ = →-intro $ □₀-∧⇒∗ »ₛ ∗-mono₀ □-elim »ₛ -∗-apply

in□--∗⇒→ : □ (P -∗ Q) ⊢[ i ] □ (P →ₛ Q)
in□--∗⇒→ = □-intro $ →-intro $ □₁-∧⇒∗ »ₛ -∗-elim □-elim

-- -- with □-∀-in/□-∃-out

□-∧-in : □ P ∧ₛ □ Q ⊢[ i ] □ (P ∧ₛ Q)
□-∧-in = ∀-intro (binary ∧-elim₀ ∧-elim₁) »ₛ □-∀-in

□-∨-out : □ (P ∨ₛ Q) ⊢[ i ] □ P ∨ₛ □ Q
□-∨-out = □-∃-out »ₛ ∃-elim (binary ∨-intro₀ ∨-intro₁)

□-⊤-intro : P ⊢[ i ] □ ⊤ₛ
□-⊤-intro = ∀-intro nullary »ₛ □-∀-in

□-∗-in : □ P ∗ □ Q ⊢[ i ] □ (P ∗ Q)
□-∗-in = ∗⇒∧ »ₛ □-∧-in »ₛ in□-∧⇒∗

|=>-elim : P ⊢[ i ] |=> Q → |=> P ⊢[ i ] |=> Q
|=>-elim P⊢|=>Q = |=>-mono P⊢|=>Q »ₛ |=>-join

------------------------------------------------------------------------
-- Persistence: Pers P

record Pers {ℓ} (P : Propₛ ℓ ∞) : Set (suc ℓ) where
  field pers : ∀ {i} → P ⊢[ i ] □ P
open Pers {{...}} public

-- Finding Pers

-- -- Unfortunately, a universally quantified instance (∀ x → ...)
-- -- can't be searched by Agda

∀-Pers : (∀ x → Pers (Pf x)) → Pers (∀! _ Pf)
∀-Pers ∀Pers .pers = ∀-mono (λ x → ∀Pers x .pers) »ₛ □-∀-in

∃-Pers : (∀ x → Pers (Pf x)) → Pers (∃! _ Pf)
∃-Pers ∀Pers .pers = ∃-mono (λ x → ∀Pers x .pers) »ₛ □-∃-in

-- -- Instances

instance

  ∧-Pers : {{Pers P}} → {{Pers Q}} → Pers (P ∧ₛ Q)
  ∧-Pers = ∀-Pers (binary it it)

  ∨-Pers : {{Pers P}} → {{Pers Q}} → Pers (P ∨ₛ Q)
  ∨-Pers = ∃-Pers (binary it it)

  ⊤-Pers : Pers {ℓ} ⊤ₛ
  ⊤-Pers .pers = □-⊤-intro

  ⊥-Pers : Pers {ℓ} ⊥ₛ
  ⊥-Pers .pers = ⊥-elim

  ∗-Pers : {{Pers P}} → {{Pers Q}} → Pers (P ∗ Q)
  ∗-Pers .pers = ∗⇒∧ »ₛ pers »ₛ in□-∧⇒∗

  ⌜⌝-Pers : Pers ⌜ φ ⌝
  ⌜⌝-Pers .pers = □-intro-⌜⌝

-- Using Pers

Pers₀-∧⇒∗ : {{Pers P}} → P ∧ₛ Q ⊢[ i ] P ∗ Q
Pers₀-∧⇒∗ = ∧-mono₀ pers »ₛ □₀-∧⇒∗ »ₛ ∗-mono₀ □-elim

Pers₁-∧⇒∗ : {{Pers Q}} → P ∧ₛ Q ⊢[ i ] P ∗ Q
Pers₁-∧⇒∗ = ∧-comm »ₛ Pers₀-∧⇒∗ »ₛ ∗-comm

retain-Pers : {{Pers Q}} → P ⊢[ i ] Q → P ⊢[ i ] Q ∗ P
retain-Pers P⊢Q = retain-□ (P⊢Q »ₛ pers) »ₛ ∗-mono₀ □-elim

dup-Pers : {{Pers P}} → P ⊢[ i ] P ∗ P
dup-Pers = retain-Pers reflₛ

Pers--∗⇒→ : {{Pers P}} → P -∗ Q ⊢[ i ] P →ₛ Q
Pers--∗⇒→ = -∗⇒□→ »ₛ →-mono₀ pers
