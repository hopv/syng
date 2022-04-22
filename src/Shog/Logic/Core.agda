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
open import Data.Unit.Base using (tt) renaming (⊤ to ⊤')
open import Data.Empty renaming (⊥ to ⊥'; ⊥-elim to ⊥'-elim)

open import Shog.Util using (zero₂; one₂; binary; nullary)
open import Shog.Logic.Prop public using (
  Propˢ; ∀^; ∃^; ∀^'; ∃^'; ∀∈-syntax; ∃∈-syntax; ∀-syntax; ∃-syntax;
  _∧_; _∨_; ⊤; ⊥; ⌜_⌝; _→ˢ_; _∗_; _-∗_; |=>; □)
open import Shog.Logic.Judg public using (
  JudgRes; _⊢[_]*_; _⊢[_]_;
  idˢ; _»_; ∀-intro; ∃-elim; ∀-elim; ∃-intro; ∀∃⇒∃∀-⊤; →-intro; →-elim;
  ⊤∗-elim; ⊤∗-intro; ∗-comm; ∗-assoc₀; ∗-mono₀; -∗-intro; -∗-elim;
  □-mono; □-elim; □-dup; □₀-∧⇒∗; □-∀-in; □-∃-out;
  |=>-mono; |=>-intro; |=>-join; |=>-frame₀; |=>-∃-out)

private variable
  ℓ : Level
  ι : Size
  P Q R S : Propˢ ℓ ∞
  Jr : JudgRes ℓ
  A B : Set ℓ
  F : A → Set ℓ
  Pᶠ Qᶠ : A → Propˢ ℓ ∞

------------------------------------------------------------------------
-- On ∀/∃/∧/∨/⊤/⊥

-- Introducing ∧/⊤ / Eliminating ∨/⊥

∧-intro : P ⊢[ ι ] Q → P ⊢[ ι ] R → P ⊢[ ι ] Q ∧ R
∧-intro P⊢Q P⊢R = ∀-intro $ binary P⊢Q P⊢R

∨-elim : P ⊢[ ι ]* Jr → Q ⊢[ ι ]* Jr → P ∨ Q ⊢[ ι ]* Jr
∨-elim P⊢*Jr Q⊢*Jr = ∃-elim $ binary P⊢*Jr Q⊢*Jr

⊤-intro : P ⊢[ ι ] ⊤
⊤-intro = ∀-intro nullary

⊥-elim : ⊥ ⊢[ ι ]* Jr
⊥-elim = ∃-elim nullary

-- Eliminating ∧/⊤ / Introducing ∨/⊥

∧-elim₀ : P ∧ Q ⊢[ ι ] P
∧-elim₀ = ∀-elim {a = zero₂}

∧-elim₁ : P ∧ Q ⊢[ ι ] Q
∧-elim₁ = ∀-elim {a = one₂}

∨-intro₀ : P ⊢[ ι ] P ∨ Q
∨-intro₀ = ∃-intro {a = zero₂}

∨-intro₁ : Q ⊢[ ι ] P ∨ Q
∨-intro₁ = ∃-intro {a = one₂}

-- ∀/∃/∧/∨/⊤/⊥ is monotone

∀-mono : (∀ a → Pᶠ a ⊢[ ι ] Qᶠ a) → ∀^' Pᶠ ⊢[ ι ] ∀^' Qᶠ
∀-mono Pᶠ⊢Qᶠ = ∀-intro $ λ a → ∀-elim » Pᶠ⊢Qᶠ a

∃-mono : (∀ a → Pᶠ a ⊢[ ι ] Qᶠ a) → ∃^' Pᶠ ⊢[ ι ] ∃^' Qᶠ
∃-mono Pᶠ⊢Qᶠ = ∃-elim $ λ a → Pᶠ⊢Qᶠ a » ∃-intro

∧-mono : P ⊢[ ι ] Q → R ⊢[ ι ] S → P ∧ R ⊢[ ι ] Q ∧ S
∧-mono P⊢Q R⊢S = ∧-intro (∧-elim₀ » P⊢Q) (∧-elim₁ » R⊢S)

∨-mono : P ⊢[ ι ] Q → R ⊢[ ι ] S → P ∨ R ⊢[ ι ] Q ∨ S
∨-mono P⊢Q R⊢S = ∨-elim (P⊢Q » ∨-intro₀) (R⊢S » ∨-intro₁)

∧-mono₀ : P ⊢[ ι ] Q → P ∧ R ⊢[ ι ] Q ∧ R
∧-mono₀ P⊢Q = ∧-mono P⊢Q idˢ

∧-mono₁ : P ⊢[ ι ] Q → R ∧ P ⊢[ ι ] R ∧ Q
∧-mono₁ P⊢Q = ∧-mono idˢ P⊢Q

∨-mono₀ : P ⊢[ ι ] Q → P ∨ R ⊢[ ι ] Q ∨ R
∨-mono₀ P⊢Q = ∨-mono P⊢Q idˢ

∨-mono₁ : P ⊢[ ι ] Q → R ∨ P ⊢[ ι ] R ∨ Q
∨-mono₁ P⊢Q = ∨-mono idˢ P⊢Q

-- ∧/∨ is commutative

∧-comm : P ∧ Q ⊢[ ι ] Q ∧ P
∧-comm = ∧-intro ∧-elim₁ ∧-elim₀

∨-comm : P ∨ Q ⊢[ ι ] Q ∨ P
∨-comm = ∨-elim ∨-intro₁ ∨-intro₀

-- ∧/∨ is associative

∧-assoc₀ : (P ∧ Q) ∧ R ⊢[ ι ] P ∧ (Q ∧ R)
∧-assoc₀ = ∧-intro (∧-elim₀ » ∧-elim₀) $
            ∧-intro (∧-elim₀ » ∧-elim₁) ∧-elim₁

∧-assoc₁ : P ∧ (Q ∧ R) ⊢[ ι ] (P ∧ Q) ∧ R
∧-assoc₁ = ∧-intro (∧-intro ∧-elim₀ $ ∧-elim₁ » ∧-elim₀) $
            ∧-elim₁ » ∧-elim₁

∨-assoc₀ : (P ∨ Q) ∨ R ⊢[ ι ] P ∨ (Q ∨ R)
∨-assoc₀ = ∨-elim (∨-elim ∨-intro₀ $ ∨-intro₀ » ∨-intro₁) $
            ∨-intro₁ » ∨-intro₁

∨-assoc₁ : P ∨ (Q ∨ R) ⊢[ ι ] (P ∨ Q) ∨ R
∨-assoc₁ = ∨-elim (∨-intro₀ » ∨-intro₀) $
            ∨-elim (∨-intro₁ » ∨-intro₀) $ ∨-intro₁

-- ∧/∨ is unital w.r.t. ⊤/⊥

∧⊤-intro : P ⊢[ ι ] P ∧ ⊤
∧⊤-intro = ∧-intro idˢ ⊤-intro

⊤∧-intro : P ⊢[ ι ] ⊤ ∧ P
⊤∧-intro = ∧-intro ⊤-intro idˢ

∨⊥-elim : P ∨ ⊥ ⊢[ ι ] P
∨⊥-elim = ∨-elim idˢ ⊥-elim

⊥∨-elim : ⊥ ∨ P ⊢[ ι ] P
⊥∨-elim = ∨-elim ⊥-elim idˢ

------------------------------------------------------------------------
-- On →ˢ

-- Application on →ˢ

→-apply : P ∧ (P →ˢ Q) ⊢[ ι ] Q
→-apply = →-elim idˢ

-- →ˢ is monotone

→-mono : Q ⊢[ ι ] P → R ⊢[ ι ] S → P →ˢ R ⊢[ ι ] Q →ˢ S
→-mono Q⊢P R⊢S = →-intro $ ∧-mono₀ Q⊢P » →-apply » R⊢S

→-mono₀ : Q ⊢[ ι ] P → P →ˢ R ⊢[ ι ] Q →ˢ R
→-mono₀ Q⊢P = →-mono Q⊢P idˢ

→-mono₁ : P ⊢[ ι ] Q → R →ˢ P ⊢[ ι ] R →ˢ Q
→-mono₁ P⊢Q = →-mono idˢ P⊢Q

------------------------------------------------------------------------
-- On ⌜⌝

-- Introducing and eliminating ⌜⌝

⌜⌝-intro : A → P ⊢[ ι ] ⌜ A ⌝
⌜⌝-intro a = ⊤-intro » ∃-intro {a = a}

⌜⌝-elim : (A → ⊤ ⊢[ ι ]* Jr) → ⌜ A ⌝ ⊢[ ι ]* Jr
⌜⌝-elim A→⊤⊢P = ∃-elim $ λ a → A→⊤⊢P a

-- ⌜⌝ is monotone

⌜⌝-mono : (A → B) → ⌜ A ⌝ ⊢[ ι ] ⌜ B ⌝
⌜⌝-mono f = ⌜⌝-elim $ λ a → ⌜⌝-intro $ f a

-- Introducing and eliminating ⌜ ⌝ ∧

⌜⌝∧-intro : A → P ⊢[ ι ] ⌜ A ⌝ ∧ P
⌜⌝∧-intro a = ∧-intro (⌜⌝-intro a) idˢ

⌜⌝∧-elim : (A → P ⊢[ ι ] Q) → ⌜ A ⌝ ∧ P ⊢[ ι ] Q
⌜⌝∧-elim A→P⊢Q = ∧-comm » →-elim $ ⌜⌝-elim $
  λ a → →-intro $ ∧-elim₀ » A→P⊢Q a

-- ⌜ A ⌝ → is the same with ∀ˢ _ ∈ A ,

⌜⌝→⇒∀ : ⌜ A ⌝ →ˢ P ⊢[ ι ] ∀ˢ _ ∈ A , P
⌜⌝→⇒∀ = ∀-intro $ λ a → ⌜⌝∧-intro a » →-apply

∀⇒⌜⌝→ : ∀ˢ _ ∈ A , P ⊢[ ι ] ⌜ A ⌝ →ˢ P
∀⇒⌜⌝→ = →-intro $ ⌜⌝∧-elim $ λ a → ∀-elim {a = a}

-- ⌜ A ⌝ ∧ is the same with ∃ˢ _ ∈ A ,

⌜⌝∧⇒∃ : ⌜ A ⌝ ∧ P ⊢[ ι ] ∃ˢ _ ∈ A , P
⌜⌝∧⇒∃ = ⌜⌝∧-elim $ λ a → idˢ » ∃-intro {a = a}

∃⇒⌜⌝∧ : ∃ˢ _ ∈ A , P ⊢[ ι ] ⌜ A ⌝ ∧ P
∃⇒⌜⌝∧ = ∃-elim $ λ a → ⌜⌝∧-intro a

-- ⌜⌝ commutes with ∀/∃/∧/∨/⊤/⊥/→

⌜⌝-∀-in : ∀ {A : Set ℓ} {F : A → Set ℓ} →
  ∀ˢ a ∈ A , ⌜ F a ⌝ ⊢[ ι ] ⌜ (∀ a → F a) ⌝
⌜⌝-∀-in = ∀∃⇒∃∀-⊤

⌜⌝-∀-out : ⌜ (∀ a → F a) ⌝ ⊢[ ι ] ∀ˢ a , ⌜ F a ⌝
⌜⌝-∀-out = ∀-intro $ λ a → ⌜⌝-elim $ λ f → ⌜⌝-intro $ f a

⌜⌝-∃-in : ∃ˢ a , ⌜ F a ⌝ ⊢[ ι ] ⌜ ∃[ a ] F a ⌝
⌜⌝-∃-in = ∃-elim $ λ a → ⌜⌝-mono $ λ fa → a , fa

⌜⌝-∃-out : ⌜ ∃[ a ] F a ⌝ ⊢[ ι ] ∃ˢ a , ⌜ F a ⌝
⌜⌝-∃-out = ⌜⌝-elim $ λ (_ , fa) → ⌜⌝-intro fa » ∃-intro

⌜⌝-∧-in : ⌜ A ⌝ ∧ ⌜ B ⌝ ⊢[ ι ] ⌜ A × B ⌝
⌜⌝-∧-in = ⌜⌝∧-elim $ λ a → ⌜⌝-mono $ λ b → (a , b)

⌜⌝-∧-out : ⌜ A × B ⌝ ⊢[ ι ] ⌜ A ⌝ ∧ ⌜ B ⌝
⌜⌝-∧-out = ⌜⌝-elim $ λ (a , b) → ∧-intro (⌜⌝-intro a) (⌜⌝-intro b)

⌜⌝-∨-in : ⌜ A ⌝ ∨ ⌜ B ⌝ ⊢[ ι ] ⌜ A ⊎ B ⌝
⌜⌝-∨-in = ∨-elim (⌜⌝-mono inj₁) (⌜⌝-mono inj₂)

⌜⌝-∨-out : ⌜ A ⊎ B ⌝ ⊢[ ι ] ⌜ A ⌝ ∨ ⌜ B ⌝
⌜⌝-∨-out = ⌜⌝-elim
  [ (λ a → ⌜⌝-intro a » ∨-intro₀) , (λ b → ⌜⌝-intro b » ∨-intro₁) ]

⌜⊤⌝-intro : P ⊢[ ι ] ⌜ ⊤' ⌝
⌜⊤⌝-intro = ⌜⌝-intro tt

⌜⊥⌝-elim : ⌜ ⊥' ⌝ ⊢[ ι ] P
⌜⊥⌝-elim = ⌜⌝-elim ⊥'-elim

⌜⌝-→-in : ⌜ A ⌝ →ˢ ⌜ B ⌝ ⊢[ ι ] ⌜ (A → B) ⌝
⌜⌝-→-in = ⌜⌝→⇒∀ » ⌜⌝-∀-in

⌜⌝-→-out : ⌜ (A → B) ⌝ ⊢[ ι ] ⌜ A ⌝ →ˢ ⌜ B ⌝
⌜⌝-→-out = →-intro $ ⌜⌝∧-elim $ λ a → ⌜⌝-mono $ λ f → f a

------------------------------------------------------------------------
-- On ∗

-- ∗ is monotone

∗-mono₁ : P ⊢[ ι ] Q → R ∗ P ⊢[ ι ] R ∗ Q
∗-mono₁ P⊢Q = ∗-comm » ∗-mono₀ P⊢Q » ∗-comm

∗-mono : P ⊢[ ι ] Q → R ⊢[ ι ] S → P ∗ R ⊢[ ι ] Q ∗ S
∗-mono P⊢Q R⊢S = ∗-mono₀ P⊢Q » ∗-mono₁ R⊢S

-- Eliminating ∗

∗-elim₁ : P ∗ Q ⊢[ ι ] Q
∗-elim₁ = ∗-mono₀ ⊤-intro » ⊤∗-elim

∗-elim₀ : P ∗ Q ⊢[ ι ] P
∗-elim₀ = ∗-comm » ∗-elim₁

-- Introducing ∗ ⊤

∗⊤-intro : P ⊢[ ι ] P ∗ ⊤
∗⊤-intro = ⊤∗-intro » ∗-comm

-- ∗ is associative

∗-assoc₁ : P ∗ (Q ∗ R) ⊢[ ι ] (P ∗ Q) ∗ R
∗-assoc₁ = ∗-comm » ∗-mono₀ ∗-comm » ∗-assoc₀ » ∗-comm » ∗-mono₀ ∗-comm

-- ∃ can get outside ∗

∗-∃-out : P ∗ ∃^' Qᶠ ⊢[ ι ] ∃ˢ a , P ∗ Qᶠ a
∗-∃-out = -∗-elim $ ∃-elim λ _ → -∗-intro ∃-intro

-- ∗ can turn into ∧

∗⇒∧ : P ∗ Q ⊢[ ι ] P ∧ Q
∗⇒∧ = ∧-intro ∗-elim₀ ∗-elim₁

------------------------------------------------------------------------
-- On -∗

-- Introducing P -∗

-∗-const : Q ⊢[ ι ] P -∗ Q
-∗-const = -∗-intro ∗-elim₁

-- Application on -∗

-∗-apply : P ∗ (P -∗ Q) ⊢[ ι ] Q
-∗-apply = -∗-elim idˢ

-- -∗ is monotone

-∗-mono : Q ⊢[ ι ] P → R ⊢[ ι ] S → P -∗ R ⊢[ ι ] Q -∗ S
-∗-mono Q⊢P R⊢S = -∗-intro $ ∗-mono₀ Q⊢P » -∗-apply » R⊢S

-∗-mono₀ : Q ⊢[ ι ] P → P -∗ R ⊢[ ι ] Q -∗ R
-∗-mono₀ Q⊢P = -∗-mono Q⊢P idˢ

-∗-mono₁ : P ⊢[ ι ] Q → R -∗ P ⊢[ ι ] R -∗ Q
-∗-mono₁ P⊢Q = -∗-mono idˢ P⊢Q

-- →ˢ can turn into -∗

→⇒-∗ : P →ˢ Q ⊢[ ι ] P -∗ Q
→⇒-∗ = -∗-intro $ ∗⇒∧ » →-elim idˢ

------------------------------------------------------------------------
-- On |=>

-- Eliminating |=> from the antecedent

|=>-elim : P ⊢[ ι ] |=> Q → |=> P ⊢[ ι ] |=> Q
|=>-elim P⊢|=>Q = |=>-mono P⊢|=>Q » |=>-join

-- ⌜ ⌝ ∧ can get outside |=>

|=>-⌜⌝∧-out : |=> (⌜ A ⌝ ∧ P) ⊢[ ι ] ⌜ A ⌝ ∧ |=> P
|=>-⌜⌝∧-out = |=>-mono ⌜⌝∧⇒∃ » |=>-∃-out » ∃⇒⌜⌝∧

-- ∗ can get inside |=>

|=>-frame₁ : |=> P ∗ Q ⊢[ ι ] |=> (P ∗ Q)
|=>-frame₁ = ∗-comm » |=>-frame₀ » |=>-mono ∗-comm

-- Updates |=> can be merged

|=>-merge : |=> P ∗ |=> Q ⊢[ ι ] |=> (P ∗ Q)
|=>-merge = |=>-frame₀ » |=>-mono |=>-frame₁ » |=>-join

------------------------------------------------------------------------
-- On □

-- Introducing |=> to the succedent

□-intro : □ P ⊢[ ι ] Q → □ P ⊢[ ι ] □ Q
□-intro □P⊢Q = □-dup » □-mono □P⊢Q

-- ∀/∧ can get outside □ / ∃/∨ can get inside □

□-∀-out : □ (∀^ _ Pᶠ) ⊢[ ι ] ∀^ _ (□ ∘ Pᶠ)
□-∀-out = ∀-intro $ λ _ → □-mono ∀-elim

□-∃-in : ∃^ A (□ ∘ Pᶠ) ⊢[ ι ] □ (∃^ A Pᶠ)
□-∃-in = ∃-elim $ λ _ → □-mono ∃-intro

□-∧-out : □ (P ∧ Q) ⊢[ ι ] □ P ∧ □ Q
□-∧-out = ∧-intro (□-mono ∧-elim₀) (□-mono ∧-elim₁)

□-∨-in : □ P ∨ □ Q ⊢[ ι ] □ (P ∨ Q)
□-∨-in = ∨-elim (□-mono ∨-intro₀) (□-mono ∨-intro₁)

-- □ ⊥ can be eliminated

□-⊥-elim : □ ⊥ ⊢[ ι ] P
□-⊥-elim = □-elim » ⊥-elim

------------------------------------------------------------------------
-- On □, with □₀-∧⇒∗

-- ∧ can turn into ∗ when one argument is under □
□₁-∧⇒∗ : P ∧ □ Q ⊢[ ι ] P ∗ □ Q
□₁-∧⇒∗ = ∧-comm » □₀-∧⇒∗ » ∗-comm

-- The antecedent can be retained when the succedent is under □
retain-□ : P ⊢[ ι ] □ Q → P ⊢[ ι ] □ Q ∗ P
retain-□ P⊢Q = ∧-intro P⊢Q idˢ » □₀-∧⇒∗

-- A proposition under □ can be duplicated
dup-□ : □ P ⊢[ ι ] □ P ∗ □ P
dup-□ = retain-□ idˢ

-- ∗ can go outside □
□-∗-out : □ (P ∗ Q) ⊢[ ι ] □ P ∗ □ Q
□-∗-out = □-mono ∗⇒∧ » □-∧-out » □₀-∧⇒∗

-- Under □, ∧ can turn into ∗
in□-∧⇒∗ : □ (P ∧ Q) ⊢[ ι ] □ (P ∗ Q)
in□-∧⇒∗ = □-intro $ dup-□ » ∗-mono (□-elim » ∧-elim₀) (□-elim » ∧-elim₁)

-- P -∗ can turn into □ P →ˢ
-∗⇒□→ : P -∗ Q ⊢[ ι ] □ P →ˢ Q
-∗⇒□→ = →-intro $ □₀-∧⇒∗ » ∗-mono₀ □-elim » -∗-apply

-- Under □, -∗ can turn into →ˢ
in□--∗⇒→ : □ (P -∗ Q) ⊢[ ι ] □ (P →ˢ Q)
in□--∗⇒→ = □-intro $ →-intro $ □₁-∧⇒∗ » -∗-elim □-elim

------------------------------------------------------------------------
-- On □, with □-∀-in/□-∃-out

-- ∧ / ∨ can get inside / outside □

□-∧-in : □ P ∧ □ Q ⊢[ ι ] □ (P ∧ Q)
□-∧-in = ∀-intro (binary ∧-elim₀ ∧-elim₁) » □-∀-in

□-∨-out : □ (P ∨ Q) ⊢[ ι ] □ P ∨ □ Q
□-∨-out = □-∃-out » ∃-elim (binary ∨-intro₀ ∨-intro₁)

-- □ ⊤ can be introduced

□-⊤-intro : P ⊢[ ι ] □ ⊤
□-⊤-intro = ∀-intro nullary » □-∀-in

-- ∗ can get inside □

□-∗-in : □ P ∗ □ Q ⊢[ ι ] □ (P ∗ Q)
□-∗-in = ∗⇒∧ » □-∧-in » in□-∧⇒∗

------------------------------------------------------------------------
-- Pers P : Persistence of a proposition

record Pers {ℓ} (P : Propˢ ℓ ∞) : Set (suc ℓ) where
  -- P can turn into □ P
  field pers : ∀ {ι} → P ⊢[ ι ] □ P
open Pers {{...}} public

------------------------------------------------------------------------
-- Deriving Pers P

-- -- For ∀/∃

-- -- They are not instances, because unfortunately
-- -- Agda can't search a universally quantified instance (∀ a → ...)

∀-Pers : (∀ a → Pers (Pᶠ a)) → Pers (∀^ _ Pᶠ)
∀-Pers ∀Pers .pers = ∀-mono (λ a → ∀Pers a .pers) » □-∀-in

∃-Pers : (∀ a → Pers (Pᶠ a)) → Pers (∃^ _ Pᶠ)
∃-Pers ∀Pers .pers = ∃-mono (λ a → ∀Pers a .pers) » □-∃-in

instance

  -- For ∧/∨/⊤/⊥

  ∧-Pers : {{Pers P}} → {{Pers Q}} → Pers (P ∧ Q)
  ∧-Pers = ∀-Pers $ binary it it

  ∨-Pers : {{Pers P}} → {{Pers Q}} → Pers (P ∨ Q)
  ∨-Pers = ∃-Pers $ binary it it

  ⊤-Pers : Pers {ℓ} ⊤
  ⊤-Pers = ∀-Pers nullary

  ⊥-Pers : Pers {ℓ} ⊥
  ⊥-Pers = ∃-Pers nullary

  -- For ∗

  ∗-Pers : {{Pers P}} → {{Pers Q}} → Pers (P ∗ Q)
  ∗-Pers .pers = ∗⇒∧ » pers » in□-∧⇒∗

  -- For ⌜ ⌝

  ⌜⌝-Pers : Pers ⌜ A ⌝
  ⌜⌝-Pers = ∃-Pers $ λ _ → ⊤-Pers

  -- For □

  □-Pers : Pers (□ P)
  □-Pers .pers = □-dup

------------------------------------------------------------------------
-- Using Pers P

-- ∧ can turn into ∗ when one argument is persistent

Pers₀-∧⇒∗ : {{Pers P}} → P ∧ Q ⊢[ ι ] P ∗ Q
Pers₀-∧⇒∗ = ∧-mono₀ pers » □₀-∧⇒∗ » ∗-mono₀ □-elim

Pers₁-∧⇒∗ : {{Pers Q}} → P ∧ Q ⊢[ ι ] P ∗ Q
Pers₁-∧⇒∗ = ∧-comm » Pers₀-∧⇒∗ » ∗-comm

-- The antecedent can be retained when the succedent is persistent
retain-Pers : {{Pers Q}} → P ⊢[ ι ] Q → P ⊢[ ι ] Q ∗ P
retain-Pers P⊢Q = retain-□ (P⊢Q » pers) » ∗-mono₀ □-elim

-- A persistent proposition can be duplicated
dup-Pers : {{Pers P}} → P ⊢[ ι ] P ∗ P
dup-Pers = retain-Pers idˢ

-- -∗ can turn into → when the left-hand side is persistent
Pers--∗⇒→ : {{Pers P}} → P -∗ Q ⊢[ ι ] P →ˢ Q
Pers--∗⇒→ = -∗⇒□→ » →-mono₀ pers

-- Introducing and eliminating ⌜ ⌝ ∗

⌜⌝∗-intro : A → P ⊢[ ι ] ⌜ A ⌝ ∗ P
⌜⌝∗-intro a = ⌜⌝∧-intro a » Pers₀-∧⇒∗

⌜⌝∗-elim : (A → P ⊢[ ι ] Q) → ⌜ A ⌝ ∗ P ⊢[ ι ] Q
⌜⌝∗-elim A→P⊢Q = ∗⇒∧ » ⌜⌝∧-elim A→P⊢Q

-- ⌜ ⌝ ∗ can get outside |=>

|=>-⌜⌝∗-out : |=> (⌜ A ⌝ ∗ P) ⊢[ ι ] ⌜ A ⌝ ∗ |=> P
|=>-⌜⌝∗-out = |=>-mono ∗⇒∧ » |=>-⌜⌝∧-out » Pers₀-∧⇒∗
