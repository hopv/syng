------------------------------------------------------------------------
-- Shog proof rules on core connectives
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Logic.Core where

open import Level using (Level; suc)
open import Size using (Size; ∞)
open import Codata.Thunk using (Thunk; force)
open import Function.Base using (_$_; _∘_; it)

open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥) renaming (⊥-elim to ⊥-elim')

open import Shog.Util using (zero₂; one₂; binary; nullary)
open import Shog.Logic.Prop public using (
  Propˢ; ∀^; ∃^; ∀^'; ∃^'; _∧ˢ_; _∨ˢ_; ⊤ˢ; ⊥ˢ; ⌜_⌝; _→ˢ_; _∗_; _-∗_; |=>; □)
open import Shog.Logic.Judg public using (
  JudgRes; _⊢[_]*_; _⊢[_]_; Pers; pers;
  idˢ; _»_; ∀-intro; ∃-elim; ∀-elim; ∃-intro; ∀∃⇒∃∀-⊤; →-intro; →-elim;
  ⊤∗-elim; ⊤∗-intro; ∗-comm; ∗-assoc₀; ∗-mono₀; -∗-intro; -∗-elim;
  □-mono; □-elim; □-dup; □₀-∧⇒∗; □-∀-in; □-∃-out;
  |=>-mono; |=>-intro; |=>-join; |=>-frame₀; |=>-∃-out)

private variable
  ℓ : Level
  i : Size
  P Q R S : Propˢ ℓ ∞
  Jr : JudgRes ℓ
  A B : Set ℓ
  F : A → Set ℓ
  Pᶠ Qᶠ : A → Propˢ ℓ ∞

------------------------------------------------------------------------
-- On ∀ˢ/∃ˢ/∧ˢ/∨ˢ/⊤ˢ/⊥ˢ

∧-intro : P ⊢[ i ] Q → P ⊢[ i ] R → P ⊢[ i ] Q ∧ˢ R
∧-intro P⊢Q P⊢R = ∀-intro $ binary P⊢Q P⊢R

∨-elim : P ⊢[ i ]* Jr → Q ⊢[ i ]* Jr → P ∨ˢ Q ⊢[ i ]* Jr
∨-elim P⊢*Jr Q⊢*Jr = ∃-elim $ binary P⊢*Jr Q⊢*Jr

⊤-intro : P ⊢[ i ] ⊤ˢ
⊤-intro = ∀-intro nullary

⊥-elim : ⊥ˢ ⊢[ i ]* Jr
⊥-elim = ∃-elim nullary

∧-elim₀ : P ∧ˢ Q ⊢[ i ] P
∧-elim₀ = ∀-elim {a = zero₂}

∧-elim₁ : P ∧ˢ Q ⊢[ i ] Q
∧-elim₁ = ∀-elim {a = one₂}

∨-intro₀ : P ⊢[ i ] P ∨ˢ Q
∨-intro₀ = ∃-intro {a = zero₂}

∨-intro₁ : Q ⊢[ i ] P ∨ˢ Q
∨-intro₁ = ∃-intro {a = one₂}

∀-mono : (∀ a → Pᶠ a ⊢[ i ] Qᶠ a) → ∀^' Pᶠ ⊢[ i ] ∀^' Qᶠ
∀-mono Pᶠ⊢Qᶠ = ∀-intro $ λ a → ∀-elim » Pᶠ⊢Qᶠ a

∃-mono : (∀ a → Pᶠ a ⊢[ i ] Qᶠ a) → ∃^' Pᶠ ⊢[ i ] ∃^' Qᶠ
∃-mono Pᶠ⊢Qᶠ = ∃-elim $ λ a → Pᶠ⊢Qᶠ a » ∃-intro

∧-mono : P ⊢[ i ] Q → R ⊢[ i ] S → P ∧ˢ R ⊢[ i ] Q ∧ˢ S
∧-mono P⊢Q R⊢S = ∧-intro (∧-elim₀ » P⊢Q) (∧-elim₁ » R⊢S)

∨-mono : P ⊢[ i ] Q → R ⊢[ i ] S → P ∨ˢ R ⊢[ i ] Q ∨ˢ S
∨-mono P⊢Q R⊢S = ∨-elim (P⊢Q » ∨-intro₀) (R⊢S » ∨-intro₁)

∧-mono₀ : P ⊢[ i ] Q → P ∧ˢ R ⊢[ i ] Q ∧ˢ R
∧-mono₀ P⊢Q = ∧-mono P⊢Q idˢ

∧-mono₁ : P ⊢[ i ] Q → R ∧ˢ P ⊢[ i ] R ∧ˢ Q
∧-mono₁ P⊢Q = ∧-mono idˢ P⊢Q

∨-mono₀ : P ⊢[ i ] Q → P ∨ˢ R ⊢[ i ] Q ∨ˢ R
∨-mono₀ P⊢Q = ∨-mono P⊢Q idˢ

∨-mono₁ : P ⊢[ i ] Q → R ∨ˢ P ⊢[ i ] R ∨ˢ Q
∨-mono₁ P⊢Q = ∨-mono idˢ P⊢Q

∧-comm : P ∧ˢ Q ⊢[ i ] Q ∧ˢ P
∧-comm = ∧-intro ∧-elim₁ ∧-elim₀

∨-comm : P ∨ˢ Q ⊢[ i ] Q ∨ˢ P
∨-comm = ∨-elim ∨-intro₁ ∨-intro₀

∧-assoc₀ : (P ∧ˢ Q) ∧ˢ R ⊢[ i ] P ∧ˢ (Q ∧ˢ R)
∧-assoc₀ = ∧-intro (∧-elim₀ » ∧-elim₀) $
            ∧-intro (∧-elim₀ » ∧-elim₁) ∧-elim₁

∧-assoc₁ : P ∧ˢ (Q ∧ˢ R) ⊢[ i ] (P ∧ˢ Q) ∧ˢ R
∧-assoc₁ = ∧-intro (∧-intro ∧-elim₀ $ ∧-elim₁ » ∧-elim₀) $
            ∧-elim₁ » ∧-elim₁

∨-assoc₀ : (P ∨ˢ Q) ∨ˢ R ⊢[ i ] P ∨ˢ (Q ∨ˢ R)
∨-assoc₀ = ∨-elim (∨-elim ∨-intro₀ $ ∨-intro₀ » ∨-intro₁) $
            ∨-intro₁ » ∨-intro₁

∨-assoc₁ : P ∨ˢ (Q ∨ˢ R) ⊢[ i ] (P ∨ˢ Q) ∨ˢ R
∨-assoc₁ = ∨-elim (∨-intro₀ » ∨-intro₀) $
            ∨-elim (∨-intro₁ » ∨-intro₀) $ ∨-intro₁

∧⊤-intro : P ⊢[ i ] P ∧ˢ ⊤ˢ
∧⊤-intro = ∧-intro idˢ ⊤-intro

⊤∧-intro : P ⊢[ i ] ⊤ˢ ∧ˢ P
⊤∧-intro = ∧-intro ⊤-intro idˢ

∨⊥-elim : P ∨ˢ ⊥ˢ ⊢[ i ] P
∨⊥-elim = ∨-elim idˢ ⊥-elim

⊥∨-elim : ⊥ˢ ∨ˢ P ⊢[ i ] P
⊥∨-elim = ∨-elim ⊥-elim idˢ

------------------------------------------------------------------------
-- On →ˢ

→-apply : P ∧ˢ (P →ˢ Q) ⊢[ i ] Q
→-apply = →-elim idˢ

→-mono : Q ⊢[ i ] P → R ⊢[ i ] S → P →ˢ R ⊢[ i ] Q →ˢ S
→-mono Q⊢P R⊢S = →-intro $ ∧-mono₀ Q⊢P » →-apply » R⊢S

→-mono₀ : Q ⊢[ i ] P → P →ˢ R ⊢[ i ] Q →ˢ R
→-mono₀ Q⊢P = →-mono Q⊢P idˢ

→-mono₁ : P ⊢[ i ] Q → R →ˢ P ⊢[ i ] R →ˢ Q
→-mono₁ P⊢Q = →-mono idˢ P⊢Q

------------------------------------------------------------------------
-- On ⌜⌝

⌜⌝-intro : A → P ⊢[ i ] ⌜ A ⌝
⌜⌝-intro a = ⊤-intro » ∃-intro {a = a}

⌜⌝-elim : (A → ⊤ˢ ⊢[ i ]* Jr) → ⌜ A ⌝ ⊢[ i ]* Jr
⌜⌝-elim A→⊤⊢P = ∃-elim $ λ a → A→⊤⊢P a

⌜⌝-∀-in : ∀ {A : Set ℓ} {F : A → Set ℓ} →
  ∀ˢ a ∈ A , ⌜ F a ⌝ ⊢[ i ] ⌜ (∀ a → F a) ⌝
⌜⌝-∀-in = ∀∃⇒∃∀-⊤

⌜⌝-mono : (A → B) → ⌜ A ⌝ ⊢[ i ] ⌜ B ⌝
⌜⌝-mono f = ⌜⌝-elim $ λ a → ⌜⌝-intro $ f a

⌜⌝∧-intro : A → P ⊢[ i ] ⌜ A ⌝ ∧ˢ P
⌜⌝∧-intro a = ∧-intro (⌜⌝-intro a) idˢ

⌜⌝∧-elim : (A → P ⊢[ i ] Q) → ⌜ A ⌝ ∧ˢ P ⊢[ i ] Q
⌜⌝∧-elim A→P⊢Q = ∧-comm » →-elim $ ⌜⌝-elim $
  λ a → →-intro $ ∧-elim₀ » A→P⊢Q a

⌜⌝→⇒∀ : ⌜ A ⌝ →ˢ P ⊢[ i ] ∀ˢ _ ∈ A , P
⌜⌝→⇒∀ = ∀-intro $ λ a → ⌜⌝∧-intro a » →-apply

∀⇒⌜⌝→ : ∀ˢ _ ∈ A , P ⊢[ i ] ⌜ A ⌝ →ˢ P
∀⇒⌜⌝→ = →-intro $ ⌜⌝∧-elim $ λ a → ∀-elim {a = a}

⌜⌝∧⇒∃ : ⌜ A ⌝ ∧ˢ P ⊢[ i ] ∃ˢ _ ∈ A , P
⌜⌝∧⇒∃ = ⌜⌝∧-elim $ λ a → idˢ » ∃-intro {a = a}

∃⇒⌜⌝∧ : ∃ˢ _ ∈ A , P ⊢[ i ] ⌜ A ⌝ ∧ˢ P
∃⇒⌜⌝∧ = ∃-elim $ λ a → ⌜⌝∧-intro a

-- -- Commutativity between ∀/∃/∧/∨/⊤/⊥/→

⌜⌝-∀-out : ⌜ (∀ a → F a) ⌝ ⊢[ i ] ∀ˢ a , ⌜ F a ⌝
⌜⌝-∀-out = ∀-intro $ λ a → ⌜⌝-elim $ λ f → ⌜⌝-intro $ f a

⌜⌝-∃-in : ∃ˢ a , ⌜ F a ⌝ ⊢[ i ] ⌜ ∃[ a ] F a ⌝
⌜⌝-∃-in = ∃-elim $ λ a → ⌜⌝-mono $ λ fa → a , fa

⌜⌝-∃-out : ⌜ ∃[ a ] F a ⌝ ⊢[ i ] ∃ˢ a , ⌜ F a ⌝
⌜⌝-∃-out = ⌜⌝-elim $ λ (_ , fa) → ⌜⌝-intro fa » ∃-intro

⌜⌝-∧-in : ⌜ A ⌝ ∧ˢ ⌜ B ⌝ ⊢[ i ] ⌜ A × B ⌝
⌜⌝-∧-in = ⌜⌝∧-elim $ λ a → ⌜⌝-mono $ λ b → (a , b)

⌜⌝-∧-out : ⌜ A × B ⌝ ⊢[ i ] ⌜ A ⌝ ∧ˢ ⌜ B ⌝
⌜⌝-∧-out = ⌜⌝-elim $ λ (a , b) → ∧-intro (⌜⌝-intro a) (⌜⌝-intro b)

⌜⌝-∨-in : ⌜ A ⌝ ∨ˢ ⌜ B ⌝ ⊢[ i ] ⌜ A ⊎ B ⌝
⌜⌝-∨-in = ∨-elim (⌜⌝-mono inj₁) (⌜⌝-mono inj₂)

⌜⌝-∨-out : ⌜ A ⊎ B ⌝ ⊢[ i ] ⌜ A ⌝ ∨ˢ ⌜ B ⌝
⌜⌝-∨-out = ⌜⌝-elim
  [ (λ a → ⌜⌝-intro a » ∨-intro₀) , (λ b → ⌜⌝-intro b » ∨-intro₁) ]

⌜⊤⌝-intro : P ⊢[ i ] ⌜ ⊤ ⌝
⌜⊤⌝-intro = ⌜⌝-intro tt

⌜⊥⌝-elim : ⌜ ⊥ ⌝ ⊢[ i ] P
⌜⊥⌝-elim = ⌜⌝-elim ⊥-elim'

⌜⌝-→-in : ⌜ A ⌝ →ˢ ⌜ B ⌝ ⊢[ i ] ⌜ (A → B) ⌝
⌜⌝-→-in = ⌜⌝→⇒∀ » ⌜⌝-∀-in

⌜⌝-→-out : ⌜ (A → B) ⌝ ⊢[ i ] ⌜ A ⌝ →ˢ ⌜ B ⌝
⌜⌝-→-out = →-intro $ ⌜⌝∧-elim $ λ a → ⌜⌝-mono $ λ f → f a

------------------------------------------------------------------------
-- On ∗

∗-mono₁ : P ⊢[ i ] Q → R ∗ P ⊢[ i ] R ∗ Q
∗-mono₁ P⊢Q = ∗-comm » ∗-mono₀ P⊢Q » ∗-comm

∗-mono : P ⊢[ i ] Q → R ⊢[ i ] S → P ∗ R ⊢[ i ] Q ∗ S
∗-mono P⊢Q R⊢S = ∗-mono₀ P⊢Q » ∗-mono₁ R⊢S

∗-elim₁ : P ∗ Q ⊢[ i ] Q
∗-elim₁ = ∗-mono₀ ⊤-intro » ⊤∗-elim

∗-elim₀ : P ∗ Q ⊢[ i ] P
∗-elim₀ = ∗-comm » ∗-elim₁

∗⊤-intro : P ⊢[ i ] P ∗ ⊤ˢ
∗⊤-intro = ⊤∗-intro » ∗-comm

∗-assoc₁ : P ∗ (Q ∗ R) ⊢[ i ] (P ∗ Q) ∗ R
∗-assoc₁ = ∗-comm » ∗-mono₀ ∗-comm » ∗-assoc₀ » ∗-comm » ∗-mono₀ ∗-comm

∗-∃-out : P ∗ ∃^' Qᶠ ⊢[ i ] ∃ˢ a , P ∗ Qᶠ a
∗-∃-out = -∗-elim $ ∃-elim λ _ → -∗-intro ∃-intro

∗⇒∧ : P ∗ Q ⊢[ i ] P ∧ˢ Q
∗⇒∧ = ∧-intro ∗-elim₀ ∗-elim₁

→⇒-∗ : P →ˢ Q ⊢[ i ] P -∗ Q
→⇒-∗ = -∗-intro $ ∗⇒∧ » →-elim idˢ

------------------------------------------------------------------------
-- On -∗

-∗-const : Q ⊢[ i ] P -∗ Q
-∗-const = -∗-intro ∗-elim₁

-∗-apply : P ∗ (P -∗ Q) ⊢[ i ] Q
-∗-apply = -∗-elim idˢ

-∗-mono : Q ⊢[ i ] P → R ⊢[ i ] S → P -∗ R ⊢[ i ] Q -∗ S
-∗-mono Q⊢P R⊢S = -∗-intro $ ∗-mono₀ Q⊢P » -∗-apply » R⊢S

-∗-mono₀ : Q ⊢[ i ] P → P -∗ R ⊢[ i ] Q -∗ R
-∗-mono₀ Q⊢P = -∗-mono Q⊢P idˢ

-∗-mono₁ : P ⊢[ i ] Q → R -∗ P ⊢[ i ] R -∗ Q
-∗-mono₁ P⊢Q = -∗-mono idˢ P⊢Q

------------------------------------------------------------------------
-- On |=>

|=>-elim : P ⊢[ i ] |=> Q → |=> P ⊢[ i ] |=> Q
|=>-elim P⊢|=>Q = |=>-mono P⊢|=>Q » |=>-join

|=>-⌜⌝∧-out : |=> (⌜ A ⌝ ∧ˢ P) ⊢[ i ] ⌜ A ⌝ ∧ˢ |=> P
|=>-⌜⌝∧-out = |=>-mono ⌜⌝∧⇒∃ » |=>-∃-out » ∃⇒⌜⌝∧

|=>-frame₁ : |=> P ∗ Q ⊢[ i ] |=> (P ∗ Q)
|=>-frame₁ = ∗-comm » |=>-frame₀ » |=>-mono ∗-comm

|=>-merge : |=> P ∗ |=> Q ⊢[ i ] |=> (P ∗ Q)
|=>-merge = |=>-frame₀ » |=>-mono |=>-frame₁ » |=>-join

------------------------------------------------------------------------
-- On □

□-intro : □ P ⊢[ i ] Q → □ P ⊢[ i ] □ Q
□-intro □P⊢Q = □-dup » □-mono □P⊢Q

□-∀-out : □ (∀^ _ Pᶠ) ⊢[ i ] ∀^ _ (□ ∘ Pᶠ)
□-∀-out = ∀-intro $ λ _ → □-mono ∀-elim

□-∃-in : ∃^ A (□ ∘ Pᶠ) ⊢[ i ] □ (∃^ A Pᶠ)
□-∃-in = ∃-elim $ λ _ → □-mono ∃-intro

□-∧-out : □ (P ∧ˢ Q) ⊢[ i ] □ P ∧ˢ □ Q
□-∧-out = ∧-intro (□-mono ∧-elim₀) (□-mono ∧-elim₁)

□-∨-in : □ P ∨ˢ □ Q ⊢[ i ] □ (P ∨ˢ Q)
□-∨-in = ∨-elim (□-mono ∨-intro₀) (□-mono ∨-intro₁)

□-⊥-elim : □ ⊥ˢ ⊢[ i ] P
□-⊥-elim = □-elim » ⊥-elim

-- -- with □₀-∧⇒∗

□₁-∧⇒∗ : P ∧ˢ □ Q ⊢[ i ] P ∗ □ Q
□₁-∧⇒∗ = ∧-comm » □₀-∧⇒∗ » ∗-comm

retain-□ : P ⊢[ i ] □ Q → P ⊢[ i ] □ Q ∗ P
retain-□ P⊢Q = ∧-intro P⊢Q idˢ » □₀-∧⇒∗

dup-□ : □ P ⊢[ i ] □ P ∗ □ P
dup-□ = retain-□ idˢ

□-∗-out : □ (P ∗ Q) ⊢[ i ] □ P ∗ □ Q
□-∗-out = □-mono ∗⇒∧ » □-∧-out » □₀-∧⇒∗

in□-∧⇒∗ : □ (P ∧ˢ Q) ⊢[ i ] □ (P ∗ Q)
in□-∧⇒∗ = □-intro $ dup-□ » ∗-mono (□-elim » ∧-elim₀) (□-elim » ∧-elim₁)

-∗⇒□→ : P -∗ Q ⊢[ i ] □ P →ˢ Q
-∗⇒□→ = →-intro $ □₀-∧⇒∗ » ∗-mono₀ □-elim » -∗-apply

in□--∗⇒→ : □ (P -∗ Q) ⊢[ i ] □ (P →ˢ Q)
in□--∗⇒→ = □-intro $ →-intro $ □₁-∧⇒∗ » -∗-elim □-elim

-- -- with □-∀-in/□-∃-out

□-∧-in : □ P ∧ˢ □ Q ⊢[ i ] □ (P ∧ˢ Q)
□-∧-in = ∀-intro (binary ∧-elim₀ ∧-elim₁) » □-∀-in

□-∨-out : □ (P ∨ˢ Q) ⊢[ i ] □ P ∨ˢ □ Q
□-∨-out = □-∃-out » ∃-elim (binary ∨-intro₀ ∨-intro₁)

□-⊤-intro : P ⊢[ i ] □ ⊤ˢ
□-⊤-intro = ∀-intro nullary » □-∀-in

□-∗-in : □ P ∗ □ Q ⊢[ i ] □ (P ∗ Q)
□-∗-in = ∗⇒∧ » □-∧-in » in□-∧⇒∗

------------------------------------------------------------------------
-- On persistence Pers P

-- Finding Pers

-- ∀-Pers and ∃-Pers are not instances, because unfortunately
-- Agda can't search a universally quantified instance (∀ a → ...)

∀-Pers : (∀ a → Pers (Pᶠ a)) → Pers (∀^ _ Pᶠ)
∀-Pers ∀Pers .pers = ∀-mono (λ a → ∀Pers a .pers) » □-∀-in

∃-Pers : (∀ a → Pers (Pᶠ a)) → Pers (∃^ _ Pᶠ)
∃-Pers ∀Pers .pers = ∃-mono (λ a → ∀Pers a .pers) » □-∃-in

instance

  ∧-Pers : {{Pers P}} → {{Pers Q}} → Pers (P ∧ˢ Q)
  ∧-Pers = ∀-Pers $ binary it it

  ∨-Pers : {{Pers P}} → {{Pers Q}} → Pers (P ∨ˢ Q)
  ∨-Pers = ∃-Pers $ binary it it

  ⊤-Pers : Pers {ℓ} ⊤ˢ
  ⊤-Pers = ∀-Pers nullary

  ⊥-Pers : Pers {ℓ} ⊥ˢ
  ⊥-Pers = ∃-Pers nullary

  ∗-Pers : {{Pers P}} → {{Pers Q}} → Pers (P ∗ Q)
  ∗-Pers .pers = ∗⇒∧ » pers » in□-∧⇒∗

  ⌜⌝-Pers : Pers ⌜ A ⌝
  ⌜⌝-Pers = ∃-Pers $ λ _ → ⊤-Pers

  □-Pers : Pers (□ P)
  □-Pers .pers = □-dup

-- Using Pers

Pers₀-∧⇒∗ : {{Pers P}} → P ∧ˢ Q ⊢[ i ] P ∗ Q
Pers₀-∧⇒∗ = ∧-mono₀ pers » □₀-∧⇒∗ » ∗-mono₀ □-elim

Pers₁-∧⇒∗ : {{Pers Q}} → P ∧ˢ Q ⊢[ i ] P ∗ Q
Pers₁-∧⇒∗ = ∧-comm » Pers₀-∧⇒∗ » ∗-comm

retain-Pers : {{Pers Q}} → P ⊢[ i ] Q → P ⊢[ i ] Q ∗ P
retain-Pers P⊢Q = retain-□ (P⊢Q » pers) » ∗-mono₀ □-elim

dup-Pers : {{Pers P}} → P ⊢[ i ] P ∗ P
dup-Pers = retain-Pers idˢ

Pers--∗⇒→ : {{Pers P}} → P -∗ Q ⊢[ i ] P →ˢ Q
Pers--∗⇒→ = -∗⇒□→ » →-mono₀ pers

-- -- More on ⌜⌝

⌜⌝∗-intro : A → P ⊢[ i ] ⌜ A ⌝ ∗ P
⌜⌝∗-intro a = ⌜⌝∧-intro a » Pers₀-∧⇒∗

⌜⌝∗-elim : (A → P ⊢[ i ] Q) → ⌜ A ⌝ ∗ P ⊢[ i ] Q
⌜⌝∗-elim A→P⊢Q = ∗⇒∧ » ⌜⌝∧-elim A→P⊢Q

|=>-⌜⌝∗-out : |=> (⌜ A ⌝ ∗ P) ⊢[ i ] ⌜ A ⌝ ∗ |=> P
|=>-⌜⌝∗-out = |=>-mono ∗⇒∧ » |=>-⌜⌝∧-out » Pers₀-∧⇒∗
