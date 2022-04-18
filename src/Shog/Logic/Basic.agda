------------------------------------------------------------------------
-- Shog proof rules on basic connectives
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Logic.Basic where

open import Level using (Level; suc)
open import Size using (Size; ∞)
open import Codata.Sized.Thunk using (Thunk; force)
open import Function.Base using (_$_; _∘_; it)

open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥) renaming (⊥-elim to ⊥-elim')

open import Shog.Util using (zero₂; one₂; binary; nullary)
open import Shog.Logic.Prop public using (
  Propₛ; ∀^; ∃^; ∀^'; ∃^'; _∧ₛ_; _∨ₛ_; ⊤ₛ; ⊥ₛ; ⌜_⌝; _→ₛ_; _∗_; _-∗_; |=>; □)
open import Shog.Logic.Judg public using (
  JudgRes; _⊢[_]*_; _⊢[_]_; Pers; pers;
  idₛ; _»_; ∀-intro; ∃-elim; ∀-elim; ∃-intro; ∀∃⇒∃∀-⊤; →-intro; →-elim;
  ∗⊤-elim; ∗⊤-intro; ∗-comm; ∗-assoc₀; ∗-mono₀; -∗-intro; -∗-elim;
  □-mono; □-elim; □-dup; □₀-∧⇒∗; □-∀-in; □-∃-out;
  |=>-mono; |=>-intro; |=>-join; |=>-frame₀; |=>-∃-out)

private variable
  ℓ : Level
  i : Size
  P Q R S : Propₛ ℓ ∞
  Jr : JudgRes ℓ
  A B : Set ℓ
  F : A → Set ℓ
  Pf Qf : A → Propₛ ℓ ∞

------------------------------------------------------------------------
-- On ∀ₛ/∃ₛ/∧ₛ/∨ₛ/⊤ₛ/⊥ₛ

∧-intro : P ⊢[ i ] Q → P ⊢[ i ] R → P ⊢[ i ] Q ∧ₛ R
∧-intro P⊢Q P⊢R = ∀-intro $ binary P⊢Q P⊢R

∨-elim : P ⊢[ i ]* Jr → Q ⊢[ i ]* Jr → P ∨ₛ Q ⊢[ i ]* Jr
∨-elim P⊢*Jr Q⊢*Jr = ∃-elim $ binary P⊢*Jr Q⊢*Jr

⊤-intro : P ⊢[ i ] ⊤ₛ
⊤-intro = ∀-intro nullary

⊥-elim : ⊥ₛ ⊢[ i ]* Jr
⊥-elim = ∃-elim nullary

∧-elim₀ : P ∧ₛ Q ⊢[ i ] P
∧-elim₀ = ∀-elim {a = zero₂}

∧-elim₁ : P ∧ₛ Q ⊢[ i ] Q
∧-elim₁ = ∀-elim {a = one₂}

∨-intro₀ : P ⊢[ i ] P ∨ₛ Q
∨-intro₀ = ∃-intro {a = zero₂}

∨-intro₁ : Q ⊢[ i ] P ∨ₛ Q
∨-intro₁ = ∃-intro {a = one₂}

∀-mono : (∀ a → Pf a ⊢[ i ] Qf a) → ∀^' Pf ⊢[ i ] ∀^' Qf
∀-mono Pf⊢Qf = ∀-intro $ λ a → ∀-elim » Pf⊢Qf a

∃-mono : (∀ a → Pf a ⊢[ i ] Qf a) → ∃^' Pf ⊢[ i ] ∃^' Qf
∃-mono Pf⊢Qf = ∃-elim $ λ a → Pf⊢Qf a » ∃-intro

∧-mono : P ⊢[ i ] Q → R ⊢[ i ] S → P ∧ₛ R ⊢[ i ] Q ∧ₛ S
∧-mono P⊢Q R⊢S = ∧-intro (∧-elim₀ » P⊢Q) (∧-elim₁ » R⊢S)

∨-mono : P ⊢[ i ] Q → R ⊢[ i ] S → P ∨ₛ R ⊢[ i ] Q ∨ₛ S
∨-mono P⊢Q R⊢S = ∨-elim (P⊢Q » ∨-intro₀) (R⊢S » ∨-intro₁)

∧-mono₀ : P ⊢[ i ] Q → P ∧ₛ R ⊢[ i ] Q ∧ₛ R
∧-mono₀ P⊢Q = ∧-mono P⊢Q idₛ

∧-mono₁ : P ⊢[ i ] Q → R ∧ₛ P ⊢[ i ] R ∧ₛ Q
∧-mono₁ P⊢Q = ∧-mono idₛ P⊢Q

∨-mono₀ : P ⊢[ i ] Q → P ∨ₛ R ⊢[ i ] Q ∨ₛ R
∨-mono₀ P⊢Q = ∨-mono P⊢Q idₛ

∨-mono₁ : P ⊢[ i ] Q → R ∨ₛ P ⊢[ i ] R ∨ₛ Q
∨-mono₁ P⊢Q = ∨-mono idₛ P⊢Q

∧-comm : P ∧ₛ Q ⊢[ i ] Q ∧ₛ P
∧-comm = ∧-intro ∧-elim₁ ∧-elim₀

∨-comm : P ∨ₛ Q ⊢[ i ] Q ∨ₛ P
∨-comm = ∨-elim ∨-intro₁ ∨-intro₀

∧-assoc₀ : (P ∧ₛ Q) ∧ₛ R ⊢[ i ] P ∧ₛ (Q ∧ₛ R)
∧-assoc₀ = ∧-intro (∧-elim₀ » ∧-elim₀) $
            ∧-intro (∧-elim₀ » ∧-elim₁) ∧-elim₁

∧-assoc₁ : P ∧ₛ (Q ∧ₛ R) ⊢[ i ] (P ∧ₛ Q) ∧ₛ R
∧-assoc₁ = ∧-intro (∧-intro ∧-elim₀ $ ∧-elim₁ » ∧-elim₀) $
            ∧-elim₁ » ∧-elim₁

∨-assoc₀ : (P ∨ₛ Q) ∨ₛ R ⊢[ i ] P ∨ₛ (Q ∨ₛ R)
∨-assoc₀ = ∨-elim (∨-elim ∨-intro₀ $ ∨-intro₀ » ∨-intro₁) $
            ∨-intro₁ » ∨-intro₁

∨-assoc₁ : P ∨ₛ (Q ∨ₛ R) ⊢[ i ] (P ∨ₛ Q) ∨ₛ R
∨-assoc₁ = ∨-elim (∨-intro₀ » ∨-intro₀) $
            ∨-elim (∨-intro₁ » ∨-intro₀) $ ∨-intro₁

∧⊤-intro : P ⊢[ i ] P ∧ₛ ⊤ₛ
∧⊤-intro = ∧-intro idₛ ⊤-intro

⊤∧-intro : P ⊢[ i ] ⊤ₛ ∧ₛ P
⊤∧-intro = ∧-intro ⊤-intro idₛ

∨⊥-elim : P ∨ₛ ⊥ₛ ⊢[ i ] P
∨⊥-elim = ∨-elim idₛ ⊥-elim

⊥∨-elim : ⊥ₛ ∨ₛ P ⊢[ i ] P
⊥∨-elim = ∨-elim ⊥-elim idₛ

------------------------------------------------------------------------
-- On →ₛ

→-apply : P ∧ₛ (P →ₛ Q) ⊢[ i ] Q
→-apply = →-elim idₛ

→-mono : Q ⊢[ i ] P → R ⊢[ i ] S → P →ₛ R ⊢[ i ] Q →ₛ S
→-mono Q⊢P R⊢S = →-intro $ ∧-mono₀ Q⊢P » →-apply » R⊢S

→-mono₀ : Q ⊢[ i ] P → P →ₛ R ⊢[ i ] Q →ₛ R
→-mono₀ Q⊢P = →-mono Q⊢P idₛ

→-mono₁ : P ⊢[ i ] Q → R →ₛ P ⊢[ i ] R →ₛ Q
→-mono₁ P⊢Q = →-mono idₛ P⊢Q

------------------------------------------------------------------------
-- On ⌜⌝

⌜⌝-intro : A → P ⊢[ i ] ⌜ A ⌝
⌜⌝-intro a = ⊤-intro » ∃-intro {a = a}

⌜⌝-elim : (A → ⊤ₛ ⊢[ i ]* Jr) → ⌜ A ⌝ ⊢[ i ]* Jr
⌜⌝-elim A→⊤⊢P = ∃-elim $ λ a → A→⊤⊢P a

⌜⌝-∀-in : ∀ {A : Set ℓ} {F : A → Set ℓ} →
  ∀ₛ a ∈ A , ⌜ F a ⌝ ⊢[ i ] ⌜ (∀ a → F a) ⌝
⌜⌝-∀-in = ∀∃⇒∃∀-⊤

⌜⌝-mono : (A → B) → ⌜ A ⌝ ⊢[ i ] ⌜ B ⌝
⌜⌝-mono f = ⌜⌝-elim $ λ a → ⌜⌝-intro $ f a

⌜⌝∧-intro : A → P ⊢[ i ] ⌜ A ⌝ ∧ₛ P
⌜⌝∧-intro a = ∧-intro (⌜⌝-intro a) idₛ

⌜⌝∧-elim : (A → P ⊢[ i ] Q) → ⌜ A ⌝ ∧ₛ P ⊢[ i ] Q
⌜⌝∧-elim A→P⊢Q = ∧-comm » →-elim $ ⌜⌝-elim $
  λ a → →-intro $ ∧-elim₀ » A→P⊢Q a

⌜⌝→⇒∀ : ⌜ A ⌝ →ₛ P ⊢[ i ] ∀ₛ _ ∈ A , P
⌜⌝→⇒∀ = ∀-intro $ λ a → ⌜⌝∧-intro a » →-apply

∀⇒⌜⌝→ : ∀ₛ _ ∈ A , P ⊢[ i ] ⌜ A ⌝ →ₛ P
∀⇒⌜⌝→ = →-intro $ ⌜⌝∧-elim $ λ a → ∀-elim {a = a}

⌜⌝∧⇒∃ : ⌜ A ⌝ ∧ₛ P ⊢[ i ] ∃ₛ _ ∈ A , P
⌜⌝∧⇒∃ = ⌜⌝∧-elim $ λ a → idₛ » ∃-intro {a = a}

∃⇒⌜⌝∧ : ∃ₛ _ ∈ A , P ⊢[ i ] ⌜ A ⌝ ∧ₛ P
∃⇒⌜⌝∧ = ∃-elim $ λ a → ⌜⌝∧-intro a

-- -- Commutativity between ∀/∃/∧/∨/⊤/⊥/→

⌜⌝-∀-out : ⌜ (∀ a → F a) ⌝ ⊢[ i ] ∀ₛ a , ⌜ F a ⌝
⌜⌝-∀-out = ∀-intro $ λ a → ⌜⌝-elim $ λ f → ⌜⌝-intro $ f a

⌜⌝-∃-in : ∃ₛ a , ⌜ F a ⌝ ⊢[ i ] ⌜ ∃[ a ] F a ⌝
⌜⌝-∃-in = ∃-elim $ λ a → ⌜⌝-mono $ λ fa → a , fa

⌜⌝-∃-out : ⌜ ∃[ a ] F a ⌝ ⊢[ i ] ∃ₛ a , ⌜ F a ⌝
⌜⌝-∃-out = ⌜⌝-elim $ λ (_ , fa) → ⌜⌝-intro fa » ∃-intro

⌜⌝-∧-in : ⌜ A ⌝ ∧ₛ ⌜ B ⌝ ⊢[ i ] ⌜ A × B ⌝
⌜⌝-∧-in = ⌜⌝∧-elim $ λ a → ⌜⌝-mono $ λ b → (a , b)

⌜⌝-∧-out : ⌜ A × B ⌝ ⊢[ i ] ⌜ A ⌝ ∧ₛ ⌜ B ⌝
⌜⌝-∧-out = ⌜⌝-elim $ λ (a , b) → ∧-intro (⌜⌝-intro a) (⌜⌝-intro b)

⌜⌝-∨-in : ⌜ A ⌝ ∨ₛ ⌜ B ⌝ ⊢[ i ] ⌜ A ⊎ B ⌝
⌜⌝-∨-in = ∨-elim (⌜⌝-mono inj₁) (⌜⌝-mono inj₂)

⌜⌝-∨-out : ⌜ A ⊎ B ⌝ ⊢[ i ] ⌜ A ⌝ ∨ₛ ⌜ B ⌝
⌜⌝-∨-out = ⌜⌝-elim
  [ (λ a → ⌜⌝-intro a » ∨-intro₀) , (λ b → ⌜⌝-intro b » ∨-intro₁) ]

⌜⊤⌝-intro : P ⊢[ i ] ⌜ ⊤ ⌝
⌜⊤⌝-intro = ⌜⌝-intro tt

⌜⊥⌝-elim : ⌜ ⊥ ⌝ ⊢[ i ] P
⌜⊥⌝-elim = ⌜⌝-elim ⊥-elim'

⌜⌝-→-in : ⌜ A ⌝ →ₛ ⌜ B ⌝ ⊢[ i ] ⌜ (A → B) ⌝
⌜⌝-→-in = ⌜⌝→⇒∀ » ⌜⌝-∀-in

⌜⌝-→-out : ⌜ (A → B) ⌝ ⊢[ i ] ⌜ A ⌝ →ₛ ⌜ B ⌝
⌜⌝-→-out = →-intro $ ⌜⌝∧-elim $ λ a → ⌜⌝-mono $ λ f → f a

------------------------------------------------------------------------
-- On ∗

∗-mono₁ : P ⊢[ i ] Q → R ∗ P ⊢[ i ] R ∗ Q
∗-mono₁ P⊢Q = ∗-comm » ∗-mono₀ P⊢Q » ∗-comm

∗-mono : P ⊢[ i ] Q → R ⊢[ i ] S → P ∗ R ⊢[ i ] Q ∗ S
∗-mono P⊢Q R⊢S = ∗-mono₀ P⊢Q » ∗-mono₁ R⊢S

∗-elim₀ : P ∗ Q ⊢[ i ] P
∗-elim₀ = ∗-mono₁ ⊤-intro » ∗⊤-elim

∗-elim₁ : P ∗ Q ⊢[ i ] Q
∗-elim₁ = ∗-comm » ∗-elim₀

⊤∗-intro : P ⊢[ i ] ⊤ₛ ∗ P
⊤∗-intro = ∗⊤-intro » ∗-comm

∗-assoc₁ : P ∗ (Q ∗ R) ⊢[ i ] (P ∗ Q) ∗ R
∗-assoc₁ = ∗-comm » ∗-mono₀ ∗-comm » ∗-assoc₀ » ∗-comm » ∗-mono₀ ∗-comm

∗-∃-out : P ∗ ∃^' Qf ⊢[ i ] ∃ₛ a , P ∗ Qf a
∗-∃-out = -∗-elim $ ∃-elim λ _ → -∗-intro ∃-intro

∗⇒∧ : P ∗ Q ⊢[ i ] P ∧ₛ Q
∗⇒∧ = ∧-intro ∗-elim₀ ∗-elim₁

→⇒-∗ : P →ₛ Q ⊢[ i ] P -∗ Q
→⇒-∗ = -∗-intro $ ∗⇒∧ » →-elim idₛ

------------------------------------------------------------------------
-- On -∗

-∗-const : Q ⊢[ i ] P -∗ Q
-∗-const = -∗-intro ∗-elim₁

-∗-apply : P ∗ (P -∗ Q) ⊢[ i ] Q
-∗-apply = -∗-elim idₛ

-∗-mono : Q ⊢[ i ] P → R ⊢[ i ] S → P -∗ R ⊢[ i ] Q -∗ S
-∗-mono Q⊢P R⊢S = -∗-intro $ ∗-mono₀ Q⊢P » -∗-apply » R⊢S

-∗-mono₀ : Q ⊢[ i ] P → P -∗ R ⊢[ i ] Q -∗ R
-∗-mono₀ Q⊢P = -∗-mono Q⊢P idₛ

-∗-mono₁ : P ⊢[ i ] Q → R -∗ P ⊢[ i ] R -∗ Q
-∗-mono₁ P⊢Q = -∗-mono idₛ P⊢Q

------------------------------------------------------------------------
-- On |=>

|=>-elim : P ⊢[ i ] |=> Q → |=> P ⊢[ i ] |=> Q
|=>-elim P⊢|=>Q = |=>-mono P⊢|=>Q » |=>-join

|=>-⌜⌝∧-out : |=> (⌜ A ⌝ ∧ₛ P) ⊢[ i ] ⌜ A ⌝ ∧ₛ |=> P
|=>-⌜⌝∧-out = |=>-mono ⌜⌝∧⇒∃ » |=>-∃-out » ∃⇒⌜⌝∧

|=>-frame₁ : |=> P ∗ Q ⊢[ i ] |=> (P ∗ Q)
|=>-frame₁ = ∗-comm » |=>-frame₀ » |=>-mono ∗-comm

|=>-merge : |=> P ∗ |=> Q ⊢[ i ] |=> (P ∗ Q)
|=>-merge = |=>-frame₀ » |=>-mono |=>-frame₁ » |=>-join

------------------------------------------------------------------------
-- On □

□-intro : □ P ⊢[ i ] Q → □ P ⊢[ i ] □ Q
□-intro □P⊢Q = □-dup » □-mono □P⊢Q

□-∀-out : □ (∀^ _ Pf) ⊢[ i ] ∀^ _ (□ ∘ Pf)
□-∀-out = ∀-intro $ λ _ → □-mono ∀-elim

□-∃-in : ∃^ A (□ ∘ Pf) ⊢[ i ] □ (∃^ A Pf)
□-∃-in = ∃-elim $ λ _ → □-mono ∃-intro

□-∧-out : □ (P ∧ₛ Q) ⊢[ i ] □ P ∧ₛ □ Q
□-∧-out = ∧-intro (□-mono ∧-elim₀) (□-mono ∧-elim₁)

□-∨-in : □ P ∨ₛ □ Q ⊢[ i ] □ (P ∨ₛ Q)
□-∨-in = ∨-elim (□-mono ∨-intro₀) (□-mono ∨-intro₁)

□-⊥-elim : □ ⊥ₛ ⊢[ i ] P
□-⊥-elim = □-elim » ⊥-elim

-- -- with □₀-∧⇒∗

□₁-∧⇒∗ : P ∧ₛ □ Q ⊢[ i ] P ∗ □ Q
□₁-∧⇒∗ = ∧-comm » □₀-∧⇒∗ » ∗-comm

retain-□ : P ⊢[ i ] □ Q → P ⊢[ i ] □ Q ∗ P
retain-□ P⊢Q = ∧-intro P⊢Q idₛ » □₀-∧⇒∗

dup-□ : □ P ⊢[ i ] □ P ∗ □ P
dup-□ = retain-□ idₛ

□-∗-out : □ (P ∗ Q) ⊢[ i ] □ P ∗ □ Q
□-∗-out = □-mono ∗⇒∧ » □-∧-out » □₀-∧⇒∗

in□-∧⇒∗ : □ (P ∧ₛ Q) ⊢[ i ] □ (P ∗ Q)
in□-∧⇒∗ = □-intro $ dup-□ » ∗-mono (□-elim » ∧-elim₀) (□-elim » ∧-elim₁)

-∗⇒□→ : P -∗ Q ⊢[ i ] □ P →ₛ Q
-∗⇒□→ = →-intro $ □₀-∧⇒∗ » ∗-mono₀ □-elim » -∗-apply

in□--∗⇒→ : □ (P -∗ Q) ⊢[ i ] □ (P →ₛ Q)
in□--∗⇒→ = □-intro $ →-intro $ □₁-∧⇒∗ » -∗-elim □-elim

-- -- with □-∀-in/□-∃-out

□-∧-in : □ P ∧ₛ □ Q ⊢[ i ] □ (P ∧ₛ Q)
□-∧-in = ∀-intro (binary ∧-elim₀ ∧-elim₁) » □-∀-in

□-∨-out : □ (P ∨ₛ Q) ⊢[ i ] □ P ∨ₛ □ Q
□-∨-out = □-∃-out » ∃-elim (binary ∨-intro₀ ∨-intro₁)

□-⊤-intro : P ⊢[ i ] □ ⊤ₛ
□-⊤-intro = ∀-intro nullary » □-∀-in

□-∗-in : □ P ∗ □ Q ⊢[ i ] □ (P ∗ Q)
□-∗-in = ∗⇒∧ » □-∧-in » in□-∧⇒∗

------------------------------------------------------------------------
-- On persistence Pers P

-- Finding Pers

-- ∀-Pers and ∃-Pers are not instances, because unfortunately
-- Agda can't search a universally quantified instance (∀ a → ...)

∀-Pers : (∀ a → Pers (Pf a)) → Pers (∀^ _ Pf)
∀-Pers ∀Pers .pers = ∀-mono (λ a → ∀Pers a .pers) » □-∀-in

∃-Pers : (∀ a → Pers (Pf a)) → Pers (∃^ _ Pf)
∃-Pers ∀Pers .pers = ∃-mono (λ a → ∀Pers a .pers) » □-∃-in

instance

  ∧-Pers : {{Pers P}} → {{Pers Q}} → Pers (P ∧ₛ Q)
  ∧-Pers = ∀-Pers $ binary it it

  ∨-Pers : {{Pers P}} → {{Pers Q}} → Pers (P ∨ₛ Q)
  ∨-Pers = ∃-Pers $ binary it it

  ⊤-Pers : Pers {ℓ} ⊤ₛ
  ⊤-Pers .pers = □-⊤-intro

  ⊥-Pers : Pers {ℓ} ⊥ₛ
  ⊥-Pers .pers = ⊥-elim

  ∗-Pers : {{Pers P}} → {{Pers Q}} → Pers (P ∗ Q)
  ∗-Pers .pers = ∗⇒∧ » pers » in□-∧⇒∗

  ⌜⌝-Pers : Pers ⌜ A ⌝
  ⌜⌝-Pers = ∃-Pers $ λ _ → ⊤-Pers

  □-Pers : Pers (□ P)
  □-Pers .pers = □-dup

-- Using Pers

Pers₀-∧⇒∗ : {{Pers P}} → P ∧ₛ Q ⊢[ i ] P ∗ Q
Pers₀-∧⇒∗ = ∧-mono₀ pers » □₀-∧⇒∗ » ∗-mono₀ □-elim

Pers₁-∧⇒∗ : {{Pers Q}} → P ∧ₛ Q ⊢[ i ] P ∗ Q
Pers₁-∧⇒∗ = ∧-comm » Pers₀-∧⇒∗ » ∗-comm

retain-Pers : {{Pers Q}} → P ⊢[ i ] Q → P ⊢[ i ] Q ∗ P
retain-Pers P⊢Q = retain-□ (P⊢Q » pers) » ∗-mono₀ □-elim

dup-Pers : {{Pers P}} → P ⊢[ i ] P ∗ P
dup-Pers = retain-Pers idₛ

Pers--∗⇒→ : {{Pers P}} → P -∗ Q ⊢[ i ] P →ₛ Q
Pers--∗⇒→ = -∗⇒□→ » →-mono₀ pers

-- -- More on ⌜⌝

⌜⌝∗-intro : A → P ⊢[ i ] ⌜ A ⌝ ∗ P
⌜⌝∗-intro a = ⌜⌝∧-intro a » Pers₀-∧⇒∗

⌜⌝∗-elim : (A → P ⊢[ i ] Q) → ⌜ A ⌝ ∗ P ⊢[ i ] Q
⌜⌝∗-elim A→P⊢Q = ∗⇒∧ » ⌜⌝∧-elim A→P⊢Q

|=>-⌜⌝∗-out : |=> (⌜ A ⌝ ∗ P) ⊢[ i ] ⌜ A ⌝ ∗ |=> P
|=>-⌜⌝∗-out = |=>-mono ∗⇒∧ » |=>-⌜⌝∧-out » Pers₀-∧⇒∗
