--------------------------------------------------------------------------------
-- Proof rules on core connectives
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Logic.Core (ℓ : Level) where

open import Base.Level using (^ˡ_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk; !)
open import Base.Func using (_$_; _∘_; it)
open import Base.Prod using (_×_; _,_; Σ-syntax)
open import Base.Sum using (_⊎_; inj₀; inj₁; ⊎-case)
open import Base.Few using (⟨2⟩; 0₂; 1₂; ⊤; ⊥; binary; absurd)
open import Base.List using (List; []; _∷_; _++_)
open import Base.List.All2 using (All²; []ᴬ²; _∷ᴬ²_)

open import Shog.Logic.Prop ℓ using (Prop'; ∀˙; ∃˙; ∀∈-syntax; ∃∈-syntax;
  ∀-syntax; ∃-syntax; _∧_; _∨_; ⊤'; ⊥'; ⌜_⌝; _→'_; _∗_; _-∗_; |=>_; □_; [∗];
  IsBasic; ∀-IsBasic; ∃-IsBasic; ∗-IsBasic; □-IsBasic; Basic; isBasic)
open import Shog.Logic.Judg ℓ using (JudgRes; _⊢[_]*_; _⊢[_]_; Pers; Pers-⇒□)

-- Import and re-export the axiomatic rules
open import Shog.Logic.Judg.All ℓ public using (refl; _»_;
  ∀-intro; ∃-elim; ∀-elim; ∃-intro; choice; →-intro; →-elim;
  ⊤∗-elim; ⊤∗-intro; ∗-comm; ∗-assocˡ; ∗-monoˡ; -∗-intro; -∗-elim;
  |=>-mono; |=>-intro; |=>-join; |=>-frameˡ; |=>-∃-out;
  □-mono; □-elim; □-dup; □ˡ-∧⇒∗; □-∀-in; □-∃-out)

private variable
  ι :  Size
  P Q R S :  Prop' ∞
  Jr :  JudgRes
  A B :  Set ℓ
  F :  A → Set ℓ
  P˙ Q˙ :  A → Prop' ∞
  Ps Qs :  List (Prop' ∞)

abstract

  ------------------------------------------------------------------------------
  -- On ∀/∃/∧/∨/⊤'/⊥'

  -- Introducing ∧/⊤' / Eliminating ∨/⊥'

  ∧-intro :  P ⊢[ ι ] Q →  P ⊢[ ι ] R →  P ⊢[ ι ] Q ∧ R
  ∧-intro P⊢Q P⊢R =  ∀-intro $ binary P⊢Q P⊢R

  ∨-elim :  P ⊢[ ι ]* Jr →  Q ⊢[ ι ]* Jr →  P ∨ Q ⊢[ ι ]* Jr
  ∨-elim P⊢*Jr Q⊢*Jr =  ∃-elim $ binary P⊢*Jr Q⊢*Jr

  ⊤-intro :  P ⊢[ ι ] ⊤'
  ⊤-intro =  ∀-intro absurd

  ⊥-elim :  ⊥' ⊢[ ι ]* Jr
  ⊥-elim =  ∃-elim absurd

  -- Eliminating ∧/⊤' / Introducing ∨/⊥'

  ∧-elimˡ :  P ∧ Q ⊢[ ι ] P
  ∧-elimˡ =  ∀-elim

  ∧-elimʳ :  P ∧ Q ⊢[ ι ] Q
  ∧-elimʳ =  ∀-elim

  ∨-introˡ :  P ⊢[ ι ] P ∨ Q
  ∨-introˡ =  ∃-intro

  ∨-introʳ :  Q ⊢[ ι ] P ∨ Q
  ∨-introʳ =  ∃-intro

  -- ∀/∃/∧/∨ is monotone

  ∀-mono :  (∀ a →  P˙ a ⊢[ ι ] Q˙ a) →  ∀˙ _ P˙ ⊢[ ι ] ∀˙ _ Q˙
  ∀-mono P˙⊢Q˙ =  ∀-intro $ λ a →  ∀-elim » P˙⊢Q˙ a

  ∃-mono :  (∀ a →  P˙ a ⊢[ ι ] Q˙ a) →  ∃˙ _ P˙ ⊢[ ι ] ∃˙ _ Q˙
  ∃-mono P˙⊢Q˙ =  ∃-elim $ λ a →  P˙⊢Q˙ a » ∃-intro

  ∧-mono :  P ⊢[ ι ] Q →  R ⊢[ ι ] S →  P ∧ R ⊢[ ι ] Q ∧ S
  ∧-mono P⊢Q R⊢S =  ∧-intro (∧-elimˡ » P⊢Q) (∧-elimʳ » R⊢S)

  ∨-mono :  P ⊢[ ι ] Q →  R ⊢[ ι ] S →  P ∨ R ⊢[ ι ] Q ∨ S
  ∨-mono P⊢Q R⊢S =  ∨-elim (P⊢Q » ∨-introˡ) (R⊢S » ∨-introʳ)

  ∧-monoˡ :  P ⊢[ ι ] Q →  P ∧ R ⊢[ ι ] Q ∧ R
  ∧-monoˡ P⊢Q =  ∧-mono P⊢Q refl

  ∧-monoʳ :  P ⊢[ ι ] Q →  R ∧ P ⊢[ ι ] R ∧ Q
  ∧-monoʳ P⊢Q =  ∧-mono refl P⊢Q

  ∨-monoˡ :  P ⊢[ ι ] Q →  P ∨ R ⊢[ ι ] Q ∨ R
  ∨-monoˡ P⊢Q =  ∨-mono P⊢Q refl

  ∨-monoʳ :  P ⊢[ ι ] Q →  R ∨ P ⊢[ ι ] R ∨ Q
  ∨-monoʳ P⊢Q =  ∨-mono refl P⊢Q

  -- ∧/∨ is commutative

  ∧-comm :  P ∧ Q ⊢[ ι ] Q ∧ P
  ∧-comm =  ∧-intro ∧-elimʳ ∧-elimˡ

  ∨-comm :  P ∨ Q ⊢[ ι ] Q ∨ P
  ∨-comm =  ∨-elim ∨-introʳ ∨-introˡ

  -- ∧/∨ is associative

  ∧-assocˡ :  (P ∧ Q) ∧ R ⊢[ ι ] P ∧ (Q ∧ R)
  ∧-assocˡ =  ∧-intro (∧-elimˡ » ∧-elimˡ) $ ∧-intro (∧-elimˡ » ∧-elimʳ) ∧-elimʳ

  ∧-assocʳ :  P ∧ (Q ∧ R) ⊢[ ι ] (P ∧ Q) ∧ R
  ∧-assocʳ =  ∧-intro (∧-intro ∧-elimˡ $ ∧-elimʳ » ∧-elimˡ) $ ∧-elimʳ » ∧-elimʳ

  ∨-assocˡ :  (P ∨ Q) ∨ R ⊢[ ι ] P ∨ (Q ∨ R)
  ∨-assocˡ =
    ∨-elim (∨-elim ∨-introˡ $ ∨-introˡ » ∨-introʳ) $ ∨-introʳ » ∨-introʳ

  ∨-assocʳ :  P ∨ (Q ∨ R) ⊢[ ι ] (P ∨ Q) ∨ R
  ∨-assocʳ =
    ∨-elim (∨-introˡ » ∨-introˡ) $ ∨-elim (∨-introʳ » ∨-introˡ) $ ∨-introʳ

  -- ∧/∨ is unital w.r.t. ⊤'/⊥'

  ∧⊤-intro :  P ⊢[ ι ] P ∧ ⊤'
  ∧⊤-intro =  ∧-intro refl ⊤-intro

  ⊤∧-intro :  P ⊢[ ι ] ⊤' ∧ P
  ⊤∧-intro =  ∧-intro ⊤-intro refl

  ∨⊥-elim :  P ∨ ⊥' ⊢[ ι ] P
  ∨⊥-elim =  ∨-elim refl ⊥-elim

  ⊥∨-elim :  ⊥' ∨ P ⊢[ ι ] P
  ⊥∨-elim =  ∨-elim ⊥-elim refl

  ------------------------------------------------------------------------------
  -- On →'

  -- Application on →'

  →-apply :  P ∧ (P →' Q) ⊢[ ι ] Q
  →-apply =  →-elim refl

  -- →' is monotone

  →-mono :  Q ⊢[ ι ] P →  R ⊢[ ι ] S →  P →' R ⊢[ ι ] Q →' S
  →-mono Q⊢P R⊢S =  →-intro $ ∧-monoˡ Q⊢P » →-apply » R⊢S

  →-monoˡ :  Q ⊢[ ι ] P →  P →' R ⊢[ ι ] Q →' R
  →-monoˡ Q⊢P =  →-mono Q⊢P refl

  →-monoʳ :  P ⊢[ ι ] Q →  R →' P ⊢[ ι ] R →' Q
  →-monoʳ P⊢Q =  →-mono refl P⊢Q

  ------------------------------------------------------------------------------
  -- On ⌜⌝

  -- Introducing and eliminating ⌜⌝

  ⌜⌝-intro :  A →  P ⊢[ ι ] ⌜ A ⌝
  ⌜⌝-intro a =  ⊤-intro » ∃-intro {a =  a}

  ⌜⌝-elim :  (A →  ⊤' ⊢[ ι ]* Jr) →  ⌜ A ⌝ ⊢[ ι ]* Jr
  ⌜⌝-elim A→⊤⊢P =  ∃-elim $ λ a →  A→⊤⊢P a

  -- ⌜⌝ is monotone

  ⌜⌝-mono :  (A →  B) →  ⌜ A ⌝ ⊢[ ι ] ⌜ B ⌝
  ⌜⌝-mono f =  ⌜⌝-elim $ λ a →  ⌜⌝-intro $ f a

  -- Introducing and eliminating ⌜ ⌝ ∧

  ⌜⌝∧-intro :  A →  P ⊢[ ι ] ⌜ A ⌝ ∧ P
  ⌜⌝∧-intro a =  ∧-intro (⌜⌝-intro a) refl

  ⌜⌝∧-elim :  (A →  P ⊢[ ι ] Q) →  ⌜ A ⌝ ∧ P ⊢[ ι ] Q
  ⌜⌝∧-elim A→P⊢Q =  ∧-comm » →-elim $ ⌜⌝-elim $
    λ a →  →-intro $ ∧-elimˡ » A→P⊢Q a

  -- ⌜ A ⌝ →' is the same with ∀' _ ∈ A ,

  ⌜⌝→⇒∀ :  ⌜ A ⌝ →' P ⊢[ ι ] ∀' _ ∈ A , P
  ⌜⌝→⇒∀ =  ∀-intro $ λ a →  ⌜⌝∧-intro a » →-apply

  ∀⇒⌜⌝→ :  ∀' _ ∈ A , P ⊢[ ι ] ⌜ A ⌝ →' P
  ∀⇒⌜⌝→ =  →-intro $ ⌜⌝∧-elim $ λ a →  ∀-elim {a =  a}

  -- ⌜ A ⌝ ∧ is the same with ∃ _ ∈ A ,

  ⌜⌝∧⇒∃ :  ⌜ A ⌝ ∧ P ⊢[ ι ] ∃ _ ∈ A , P
  ⌜⌝∧⇒∃ =  ⌜⌝∧-elim $ λ a →  refl » ∃-intro {a =  a}

  ∃⇒⌜⌝∧ :  ∃ _ ∈ A , P ⊢[ ι ] ⌜ A ⌝ ∧ P
  ∃⇒⌜⌝∧ =  ∃-elim $ λ a →  ⌜⌝∧-intro a

  -- ⌜⌝ commutes with ∀/∃/∧/∨/⊤'/⊥'/→

  ⌜⌝-∀-in :  ∀' a , ⌜ F a ⌝ ⊢[ ι ] ⌜ (∀ a → F a) ⌝
  ⌜⌝-∀-in =  choice » ∃-mono $ λ _ → ⊤-intro

  ⌜⌝-∀-out :  ⌜ (∀ a →  F a) ⌝ ⊢[ ι ] ∀' a , ⌜ F a ⌝
  ⌜⌝-∀-out =  ∀-intro $ λ a →  ⌜⌝-elim $ λ f →  ⌜⌝-intro $ f a

  ⌜⌝-∃-in :  ∃ a , ⌜ F a ⌝ ⊢[ ι ] ⌜ Σ a , F a ⌝
  ⌜⌝-∃-in =  ∃-elim $ λ a →  ⌜⌝-mono $ λ fa →  a , fa

  ⌜⌝-∃-out :  ⌜ Σ a , F a ⌝ ⊢[ ι ] ∃ a , ⌜ F a ⌝
  ⌜⌝-∃-out =  ⌜⌝-elim $ λ (_ , fa) →  ⌜⌝-intro fa » ∃-intro

  ⌜⌝-∧-in :  ⌜ A ⌝ ∧ ⌜ B ⌝ ⊢[ ι ] ⌜ A × B ⌝
  ⌜⌝-∧-in =  ⌜⌝∧-elim $ λ a →  ⌜⌝-mono $ λ b →  (a , b)

  ⌜⌝-∧-out :  ⌜ A × B ⌝ ⊢[ ι ] ⌜ A ⌝ ∧ ⌜ B ⌝
  ⌜⌝-∧-out =  ⌜⌝-elim $ λ (a , b) →  ∧-intro (⌜⌝-intro a) (⌜⌝-intro b)

  ⌜⌝-∨-in :  ⌜ A ⌝ ∨ ⌜ B ⌝ ⊢[ ι ] ⌜ A ⊎ B ⌝
  ⌜⌝-∨-in =  ∨-elim (⌜⌝-mono inj₀) (⌜⌝-mono inj₁)

  ⌜⌝-∨-out :  ⌜ A ⊎ B ⌝ ⊢[ ι ] ⌜ A ⌝ ∨ ⌜ B ⌝
  ⌜⌝-∨-out =  ⌜⌝-elim $ ⊎-case
    (λ a → ⌜⌝-intro a » ∨-introˡ) (λ b → ⌜⌝-intro b » ∨-introʳ)

  ⌜⊤⌝-intro :  P ⊢[ ι ] ⌜ ⊤ ⌝
  ⌜⊤⌝-intro =  ⌜⌝-intro _

  ⌜⊥⌝-elim :  ⌜ ⊥ ⌝ ⊢[ ι ] P
  ⌜⊥⌝-elim =  ⌜⌝-elim absurd

  ⌜⌝-→-in :  ⌜ A ⌝ →' ⌜ B ⌝ ⊢[ ι ] ⌜ (A → B) ⌝
  ⌜⌝-→-in =  ⌜⌝→⇒∀ » ⌜⌝-∀-in

  ⌜⌝-→-out :  ⌜ (A → B) ⌝ ⊢[ ι ] ⌜ A ⌝ →' ⌜ B ⌝
  ⌜⌝-→-out =  →-intro $ ⌜⌝∧-elim $ λ a → ⌜⌝-mono $ λ f → f a

  ------------------------------------------------------------------------------
  -- On ∗

  -- ∗ is monotone

  ∗-monoʳ :  P ⊢[ ι ] Q →  R ∗ P ⊢[ ι ] R ∗ Q
  ∗-monoʳ P⊢Q =  ∗-comm » ∗-monoˡ P⊢Q » ∗-comm

  ∗-mono :  P ⊢[ ι ] Q →  R ⊢[ ι ] S →  P ∗ R ⊢[ ι ] Q ∗ S
  ∗-mono P⊢Q R⊢S =  ∗-monoˡ P⊢Q » ∗-monoʳ R⊢S

  -- Eliminating ∗

  ∗-elimʳ :  P ∗ Q ⊢[ ι ] Q
  ∗-elimʳ =  ∗-monoˡ ⊤-intro » ⊤∗-elim

  ∗-elimˡ :  P ∗ Q ⊢[ ι ] P
  ∗-elimˡ =  ∗-comm » ∗-elimʳ

  -- Introducing ∗ ⊤'

  ∗⊤-intro :  P ⊢[ ι ] P ∗ ⊤'
  ∗⊤-intro =  ⊤∗-intro » ∗-comm

  -- ∗ is associative

  ∗-assocʳ :  P ∗ (Q ∗ R) ⊢[ ι ] (P ∗ Q) ∗ R
  ∗-assocʳ =  ∗-comm » ∗-monoˡ ∗-comm » ∗-assocˡ » ∗-comm » ∗-monoˡ ∗-comm

  -- ∃ can get outside ∗

  ∗-∃-out :  P ∗ ∃˙ _ Q˙ ⊢[ ι ] ∃ a , P ∗ Q˙ a
  ∗-∃-out =  -∗-elim $ ∃-elim λ _ → -∗-intro ∃-intro

  -- ∗ can turn into ∧

  ∗⇒∧ :  P ∗ Q ⊢[ ι ] P ∧ Q
  ∗⇒∧ =  ∧-intro ∗-elimˡ ∗-elimʳ

  ------------------------------------------------------------------------------
  -- On -∗

  -- Introducing P -∗

  -∗-const :  Q ⊢[ ι ] P -∗ Q
  -∗-const =  -∗-intro ∗-elimʳ

  -- Application on -∗

  -∗-apply :  P ∗ (P -∗ Q) ⊢[ ι ] Q
  -∗-apply =  -∗-elim refl

  -- -∗ is monotone

  -∗-mono :  Q ⊢[ ι ] P →  R ⊢[ ι ] S →  P -∗ R ⊢[ ι ] Q -∗ S
  -∗-mono Q⊢P R⊢S =  -∗-intro $ ∗-monoˡ Q⊢P » -∗-apply » R⊢S

  -∗-monoˡ :  Q ⊢[ ι ] P →  P -∗ R ⊢[ ι ] Q -∗ R
  -∗-monoˡ Q⊢P =  -∗-mono Q⊢P refl

  -∗-monoʳ :  P ⊢[ ι ] Q →  R -∗ P ⊢[ ι ] R -∗ Q
  -∗-monoʳ P⊢Q =  -∗-mono refl P⊢Q

  -- →' can turn into -∗

  →⇒-∗ :  P →' Q ⊢[ ι ] P -∗ Q
  →⇒-∗ =  -∗-intro $ ∗⇒∧ » →-elim refl

  ------------------------------------------------------------------------------
  -- On |=>

  -- Eliminating |=> from the antecedent

  |=>-elim :  P ⊢[ ι ] |=> Q →  |=> P ⊢[ ι ] |=> Q
  |=>-elim P⊢|=>Q =  |=>-mono P⊢|=>Q » |=>-join

  -- ⌜ ⌝ ∧ can get outside |=>

  |=>-⌜⌝∧-out :  |=> (⌜ A ⌝ ∧ P) ⊢[ ι ] ⌜ A ⌝ ∧ |=> P
  |=>-⌜⌝∧-out =  |=>-mono ⌜⌝∧⇒∃ » |=>-∃-out » ∃⇒⌜⌝∧

  -- ∗ can get inside |=>

  |=>-frameʳ :  |=> P ∗ Q ⊢[ ι ] |=> (P ∗ Q)
  |=>-frameʳ =  ∗-comm » |=>-frameˡ » |=>-mono ∗-comm

  -- Updates |=> can be merged

  |=>-merge :  |=> P ∗ |=> Q ⊢[ ι ] |=> (P ∗ Q)
  |=>-merge =  |=>-frameˡ » |=>-mono |=>-frameʳ » |=>-join

  ------------------------------------------------------------------------------
  -- On □

  -- Introducing |=> to the succedent

  □-intro :  □ P ⊢[ ι ] Q →  □ P ⊢[ ι ] □ Q
  □-intro □P⊢Q =  □-dup » □-mono □P⊢Q

  -- ∀/∧ can get outside □ / ∃/∨ can get inside □

  □-∀-out :  □ ∀˙ _ P˙ ⊢[ ι ] ∀˙ _ (□_ ∘ P˙)
  □-∀-out =  ∀-intro $ λ _ → □-mono ∀-elim

  □-∃-in :  ∃˙ A (□_ ∘ P˙) ⊢[ ι ] □ ∃˙ A P˙
  □-∃-in =  ∃-elim $ λ _ → □-mono ∃-intro

  □-∧-out :  □ (P ∧ Q) ⊢[ ι ] □ P ∧ □ Q
  □-∧-out =  ∧-intro (□-mono ∧-elimˡ) (□-mono ∧-elimʳ)

  □-∨-in :  □ P ∨ □ Q ⊢[ ι ] □ (P ∨ Q)
  □-∨-in =  ∨-elim (□-mono ∨-introˡ) (□-mono ∨-introʳ)

  -- □ ⊥' can be eliminated

  □-⊥-elim :  □ ⊥' ⊢[ ι ] P
  □-⊥-elim =  □-elim » ⊥-elim

  ------------------------------------------------------------------------------
  -- On □, with □ˡ-∧⇒∗

  -- ∧ can turn into ∗ when one argument is under □
  □ʳ-∧⇒∗ :  P ∧ □ Q ⊢[ ι ] P ∗ □ Q
  □ʳ-∧⇒∗ =  ∧-comm » □ˡ-∧⇒∗ » ∗-comm

  -- The antecedent can be retained when the succedent is under □
  retain-□ :  P ⊢[ ι ] □ Q →  P ⊢[ ι ] □ Q ∗ P
  retain-□ P⊢Q =  ∧-intro P⊢Q refl » □ˡ-∧⇒∗

  -- A proposition under □ can be duplicated
  dup-□ :  □ P ⊢[ ι ] □ P ∗ □ P
  dup-□ =  retain-□ refl

  -- ∗ can go outside □
  □-∗-out :  □ (P ∗ Q) ⊢[ ι ] □ P ∗ □ Q
  □-∗-out =  □-mono ∗⇒∧ » □-∧-out » □ˡ-∧⇒∗

  -- Under □, ∧ can turn into ∗
  in□-∧⇒∗ :  □ (P ∧ Q) ⊢[ ι ] □ (P ∗ Q)
  in□-∧⇒∗ =  □-intro $ dup-□ » ∗-mono (□-elim » ∧-elimˡ) (□-elim » ∧-elimʳ)

  -- P -∗ can turn into □ P →'

  -∗Pers-⇒□→ :  P -∗ Q ⊢[ ι ] □ P →' Q
  -∗Pers-⇒□→ =  →-intro $ □ˡ-∧⇒∗ » ∗-monoˡ □-elim » -∗-apply

  -- Under □, -∗ can turn into →'
  in□--∗⇒→ :  □ (P -∗ Q) ⊢[ ι ] □ (P →' Q)
  in□--∗⇒→ =  □-intro $ →-intro $ □ʳ-∧⇒∗ » -∗-elim □-elim

  ------------------------------------------------------------------------------
  -- On □, with □-∀-in/□-∃-out

  -- ∧ / ∨ can get inside / outside □

  □-∧-in :  □ P ∧ □ Q ⊢[ ι ] □ (P ∧ Q)
  □-∧-in =  ∀-intro (binary ∧-elimˡ ∧-elimʳ) » □-∀-in

  □-∨-out :  □ (P ∨ Q) ⊢[ ι ] □ P ∨ □ Q
  □-∨-out =  □-∃-out » ∃-elim (binary ∨-introˡ ∨-introʳ)

  -- □ ⊤' can be introduced

  □-⊤-intro :  P ⊢[ ι ] □ ⊤'
  □-⊤-intro =  ∀-intro absurd » □-∀-in

  -- ∗ can get inside □

  □-∗-in :  □ P ∗ □ Q ⊢[ ι ] □ (P ∗ Q)
  □-∗-in =  ∗⇒∧ » □-∧-in » in□-∧⇒∗

  ------------------------------------------------------------------------------
  -- Deriving Pers P

  -- -- For ∀/∃

  -- -- They are not instances, because unfortunately
  -- -- Agda can't search a universally quantified instance (∀ a → ...)

  ∀-Pers :  (∀ a → Pers (P˙ a)) →  Pers (∀˙ _ P˙)
  ∀-Pers ∀Pers .Pers-⇒□ =  ∀-mono (λ a → ∀Pers a .Pers-⇒□) » □-∀-in

  ∃-Pers :  (∀ a → Pers (P˙ a)) →  Pers (∃˙ _ P˙)
  ∃-Pers ∀Pers .Pers-⇒□ =  ∃-mono (λ a → ∀Pers a .Pers-⇒□) » □-∃-in

  instance

    -- For ∧/∨/⊤'/⊥'

    ∧-Pers :  {{Pers P}} →  {{Pers Q}} →  Pers (P ∧ Q)
    ∧-Pers =  ∀-Pers $ binary it it

    ∨-Pers :  {{Pers P}} →  {{Pers Q}} →  Pers (P ∨ Q)
    ∨-Pers =  ∃-Pers $ binary it it

    ⊤-Pers :  Pers ⊤'
    ⊤-Pers =  ∀-Pers absurd

    ⊥-Pers :  Pers ⊥'
    ⊥-Pers =  ∃-Pers absurd

    -- For ∗

    ∗-Pers :  {{Pers P}} →  {{Pers Q}} →  Pers (P ∗ Q)
    ∗-Pers .Pers-⇒□ =  ∗⇒∧ » Pers-⇒□ » in□-∧⇒∗

    -- For ⌜ ⌝

    ⌜⌝-Pers :  Pers ⌜ A ⌝
    ⌜⌝-Pers =  ∃-Pers $ λ _ → ⊤-Pers

    -- For □

    □-Pers :  Pers (□ P)
    □-Pers .Pers-⇒□ =  □-dup

  IsBasic-Pers :  IsBasic P →  Pers P
  IsBasic-Pers (∀-IsBasic IsBaP˙) =  ∀-Pers (λ x → IsBasic-Pers $ IsBaP˙ x)
  IsBasic-Pers (∃-IsBasic IsBaP˙) =  ∃-Pers (λ x → IsBasic-Pers $ IsBaP˙ x)
  IsBasic-Pers (∗-IsBasic IsBaP IsBaQ) =
    ∗-Pers {{IsBasic-Pers IsBaP}} {{IsBasic-Pers IsBaQ}}
  IsBasic-Pers (□-IsBasic _) =  it

  Basic-Pers :  {{Basic P}} →  Pers P
  Basic-Pers =  IsBasic-Pers isBasic

  ------------------------------------------------------------------------------
  -- Using Pers P

  -- ∧ can turn into ∗ when one argument is persistent

  Persˡ-∧⇒∗ :  {{Pers P}} →  P ∧ Q ⊢[ ι ] P ∗ Q
  Persˡ-∧⇒∗ =  ∧-monoˡ Pers-⇒□ » □ˡ-∧⇒∗ » ∗-monoˡ □-elim

  Persʳ-∧⇒∗ :  {{Pers Q}} →  P ∧ Q ⊢[ ι ] P ∗ Q
  Persʳ-∧⇒∗ =  ∧-comm » Persˡ-∧⇒∗ » ∗-comm

  -- The antecedent can be retained when the succedent is persistent
  retain-Pers :  {{Pers Q}} →  P ⊢[ ι ] Q →  P ⊢[ ι ] Q ∗ P
  retain-Pers P⊢Q =  retain-□ (P⊢Q » Pers-⇒□) » ∗-monoˡ □-elim

  -- A persistent proposition can be duplicated
  dup-Pers :  {{Pers P}} →  P ⊢[ ι ] P ∗ P
  dup-Pers =  retain-Pers refl

  -- -∗ can turn into →' when the left-hand side is persistent
  Pers--∗⇒→ :  {{Pers P}} →  P -∗ Q ⊢[ ι ] P →' Q
  Pers--∗⇒→ =  -∗Pers-⇒□→ » →-monoˡ Pers-⇒□

  -- Introducing and eliminating ⌜ ⌝ ∗

  ⌜⌝∗-intro :  A →  P ⊢[ ι ] ⌜ A ⌝ ∗ P
  ⌜⌝∗-intro a =  ⌜⌝∧-intro a » Persˡ-∧⇒∗

  ⌜⌝∗-elim :  (A →  P ⊢[ ι ] Q) →  ⌜ A ⌝ ∗ P ⊢[ ι ] Q
  ⌜⌝∗-elim A→P⊢Q =  ∗⇒∧ » ⌜⌝∧-elim A→P⊢Q

  -- ⌜ ⌝ ∗ can get outside |=>

  |=>-⌜⌝∗-out :  |=> (⌜ A ⌝ ∗ P) ⊢[ ι ] ⌜ A ⌝ ∗ |=> P
  |=>-⌜⌝∗-out =  |=>-mono ∗⇒∧ » |=>-⌜⌝∧-out » Persˡ-∧⇒∗

  ------------------------------------------------------------------------------
  -- On [∗]

  -- [∗] is monotone

  [∗]-mono :  All² _⊢[ ι ]_ Ps Qs →  [∗] Ps ⊢[ ι ] [∗] Qs
  [∗]-mono []ᴬ² =  refl
  [∗]-mono (P⊢Q ∷ᴬ² Ps⊢Qs) =  ∗-mono P⊢Q ([∗]-mono Ps⊢Qs)

  -- ++ can get inside and outside [∗]

  [∗]-++-in :  [∗] Ps ∗ [∗] Qs ⊢[ ι ] [∗] (Ps ++ Qs)
  [∗]-++-in {[]} =  ∗-elimʳ
  [∗]-++-in {_ ∷ Ps'} =  ∗-assocˡ » ∗-monoʳ ([∗]-++-in {Ps'})

  [∗]-++-out :  [∗] (Ps ++ Qs) ⊢[ ι ] [∗] Ps ∗ [∗] Qs
  [∗]-++-out {[]} =  ⊤∗-intro
  [∗]-++-out {_ ∷ Ps'} =  ∗-monoʳ ([∗]-++-out {Ps'}) » ∗-assocʳ
