--------------------------------------------------------------------------------
-- Proof rules on core connectives
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Logic.Core (ℓ : Level) where

open import Base.Level using (^_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk; !)
open import Base.Func using (_$_; _∘_; it)
open import Base.Prod using (_×_; _,_; ∑-syntax)
open import Base.Sum using (_⊎_; inj₀; inj₁; ⊎-case)
open import Base.Few using (⟨2⟩; 0₂; 1₂; ⊤; ⊥; binary; absurd)
open import Base.List using (List; []; _∷_; _++_)
open import Base.List.All2 using (All²; []ᴬ²; _∷ᴬ²_)
open import Shog.Logic.Prop ℓ using (Prop'; ∀˙; ∃˙; ∀∈-syntax; ∃∈-syntax;
  ∀-syntax; ∃-syntax; _∧_; _∨_; ⊤'; ⊥'; ⌜_⌝; _→'_; _∗_; _-∗_; |=>_; □_; [∗]_;
  IsBasic; ∀-IsBasic; ∃-IsBasic; ∗-IsBasic; □-IsBasic; Basic; isBasic)

-- Import and re-export
open import Shog.Logic.Judg ℓ public using (
  JudgRes; Pure; _⊢[_]*_; _⊢[_]_; _⊢[<_]_; Pers; Pers-⇒□;
  ⊢-refl; _»_; ∀-intro; ∃-elim; ∀-elim; ∃-intro; choice; →-intro; →-elim;
  ⊤∗-elim; ⊤∗-intro; ∗-comm; ∗-assocˡ; ∗-monoˡ; -∗-intro; -∗-elim;
  |=>-mono; |=>-intro; |=>-join; |=>-frameˡ; |=>-∃-out;
  □-mono; □-elim; □-dup; □ˡ-∧⇒∗; □-∀-in; □-∃-out)

private variable
  ι :  Size
  P Q R S :  Prop' ∞
  Jr :  JudgRes
  X Y :  Set ℓ
  Y˙ :  X → Set ℓ
  P˙ Q˙ :  X → Prop' ∞
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

  ∀-mono :  (∀ x →  P˙ x ⊢[ ι ] Q˙ x) →  ∀˙ P˙ ⊢[ ι ] ∀˙ Q˙
  ∀-mono P˙⊢Q˙ =  ∀-intro $ λ x →  ∀-elim » P˙⊢Q˙ x

  ∃-mono :  (∀ x →  P˙ x ⊢[ ι ] Q˙ x) →  ∃˙ P˙ ⊢[ ι ] ∃˙ Q˙
  ∃-mono P˙⊢Q˙ =  ∃-elim $ λ x →  P˙⊢Q˙ x » ∃-intro

  ∧-mono :  P ⊢[ ι ] Q →  R ⊢[ ι ] S →  P ∧ R ⊢[ ι ] Q ∧ S
  ∧-mono P⊢Q R⊢S =  ∧-intro (∧-elimˡ » P⊢Q) (∧-elimʳ » R⊢S)

  ∨-mono :  P ⊢[ ι ] Q →  R ⊢[ ι ] S →  P ∨ R ⊢[ ι ] Q ∨ S
  ∨-mono P⊢Q R⊢S =  ∨-elim (P⊢Q » ∨-introˡ) (R⊢S » ∨-introʳ)

  ∧-monoˡ :  P ⊢[ ι ] Q →  P ∧ R ⊢[ ι ] Q ∧ R
  ∧-monoˡ P⊢Q =  ∧-mono P⊢Q ⊢-refl

  ∧-monoʳ :  P ⊢[ ι ] Q →  R ∧ P ⊢[ ι ] R ∧ Q
  ∧-monoʳ P⊢Q =  ∧-mono ⊢-refl P⊢Q

  ∨-monoˡ :  P ⊢[ ι ] Q →  P ∨ R ⊢[ ι ] Q ∨ R
  ∨-monoˡ P⊢Q =  ∨-mono P⊢Q ⊢-refl

  ∨-monoʳ :  P ⊢[ ι ] Q →  R ∨ P ⊢[ ι ] R ∨ Q
  ∨-monoʳ P⊢Q =  ∨-mono ⊢-refl P⊢Q

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
  ∧⊤-intro =  ∧-intro ⊢-refl ⊤-intro

  ⊤∧-intro :  P ⊢[ ι ] ⊤' ∧ P
  ⊤∧-intro =  ∧-intro ⊤-intro ⊢-refl

  ∨⊥-elim :  P ∨ ⊥' ⊢[ ι ] P
  ∨⊥-elim =  ∨-elim ⊢-refl ⊥-elim

  ⊥∨-elim :  ⊥' ∨ P ⊢[ ι ] P
  ⊥∨-elim =  ∨-elim ⊥-elim ⊢-refl

  ------------------------------------------------------------------------------
  -- On →'

  -- Application on →'

  →-apply :  P ∧ (P →' Q) ⊢[ ι ] Q
  →-apply =  →-elim ⊢-refl

  -- →' is monotone

  →-mono :  Q ⊢[ ι ] P →  R ⊢[ ι ] S →  P →' R ⊢[ ι ] Q →' S
  →-mono Q⊢P R⊢S =  →-intro $ ∧-monoˡ Q⊢P » →-apply » R⊢S

  →-monoˡ :  Q ⊢[ ι ] P →  P →' R ⊢[ ι ] Q →' R
  →-monoˡ Q⊢P =  →-mono Q⊢P ⊢-refl

  →-monoʳ :  P ⊢[ ι ] Q →  R →' P ⊢[ ι ] R →' Q
  →-monoʳ P⊢Q =  →-mono ⊢-refl P⊢Q

  ------------------------------------------------------------------------------
  -- On ⌜⌝

  -- Introducing and eliminating ⌜⌝

  ⌜⌝-intro :  X →  P ⊢[ ι ] ⌜ X ⌝
  ⌜⌝-intro x =  ⊤-intro » ∃-intro {x = x}

  ⌜⌝-elim :  (X →  ⊤' ⊢[ ι ]* Jr) →  ⌜ X ⌝ ⊢[ ι ]* Jr
  ⌜⌝-elim A→⊤⊢P =  ∃-elim $ λ x →  A→⊤⊢P x

  -- ⌜⌝ is monotone

  ⌜⌝-mono :  (X →  Y) →  ⌜ X ⌝ ⊢[ ι ] ⌜ Y ⌝
  ⌜⌝-mono f =  ⌜⌝-elim $ λ x →  ⌜⌝-intro $ f x

  -- Introducing and eliminating ⌜ ⌝ ∧

  ⌜⌝∧-intro :  X →  P ⊢[ ι ] ⌜ X ⌝ ∧ P
  ⌜⌝∧-intro x =  ∧-intro (⌜⌝-intro x) ⊢-refl

  ⌜⌝∧-elim :  (X →  P ⊢[ ι ] Q) →  ⌜ X ⌝ ∧ P ⊢[ ι ] Q
  ⌜⌝∧-elim A→P⊢Q =  ∧-comm » →-elim $ ⌜⌝-elim $
    λ x →  →-intro $ ∧-elimˡ » A→P⊢Q x

  -- ⌜ X ⌝ →' is the same with ∀' _ ∈ X ,

  ⌜⌝→⇒∀ :  ⌜ X ⌝ →' P ⊢[ ι ] ∀' _ ∈ X , P
  ⌜⌝→⇒∀ =  ∀-intro $ λ x →  ⌜⌝∧-intro x » →-apply

  ∀⇒⌜⌝→ :  ∀' _ ∈ X , P ⊢[ ι ] ⌜ X ⌝ →' P
  ∀⇒⌜⌝→ =  →-intro $ ⌜⌝∧-elim $ λ x →  ∀-elim {x = x}

  -- ⌜ X ⌝ ∧ is the same with ∃ _ ∈ X ,

  ⌜⌝∧⇒∃ :  ⌜ X ⌝ ∧ P ⊢[ ι ] ∃ _ ∈ X , P
  ⌜⌝∧⇒∃ =  ⌜⌝∧-elim $ λ x →  ⊢-refl » ∃-intro {x = x}

  ∃⇒⌜⌝∧ :  ∃ _ ∈ X , P ⊢[ ι ] ⌜ X ⌝ ∧ P
  ∃⇒⌜⌝∧ =  ∃-elim $ λ x →  ⌜⌝∧-intro x

  -- ⌜⌝ commutes with ∀/∃/∧/∨/⊤'/⊥'/→

  ⌜⌝-∀-in :  ∀' x , ⌜ Y˙ x ⌝ ⊢[ ι ] ⌜ (∀ x → Y˙ x) ⌝
  ⌜⌝-∀-in =  choice » ∃-mono $ λ _ → ⊤-intro

  ⌜⌝-∀-out :  ⌜ (∀ x → Y˙ x) ⌝ ⊢[ ι ] ∀' x , ⌜ Y˙ x ⌝
  ⌜⌝-∀-out =  ∀-intro $ λ x →  ⌜⌝-elim $ λ f →  ⌜⌝-intro $ f x

  ⌜⌝-∃-in :  ∃ x , ⌜ Y˙ x ⌝ ⊢[ ι ] ⌜ ∑ x , Y˙ x ⌝
  ⌜⌝-∃-in =  ∃-elim $ λ x →  ⌜⌝-mono $ λ fa →  x , fa

  ⌜⌝-∃-out :  ⌜ ∑ x , Y˙ x ⌝ ⊢[ ι ] ∃ x , ⌜ Y˙ x ⌝
  ⌜⌝-∃-out =  ⌜⌝-elim $ λ (_ , fa) →  ⌜⌝-intro fa » ∃-intro

  ⌜⌝-∧-in :  ⌜ X ⌝ ∧ ⌜ Y ⌝ ⊢[ ι ] ⌜ X × Y ⌝
  ⌜⌝-∧-in =  ⌜⌝∧-elim $ λ x →  ⌜⌝-mono $ λ y →  (x , y)

  ⌜⌝-∧-out :  ⌜ X × Y ⌝ ⊢[ ι ] ⌜ X ⌝ ∧ ⌜ Y ⌝
  ⌜⌝-∧-out =  ⌜⌝-elim $ λ (x , y) →  ∧-intro (⌜⌝-intro x) (⌜⌝-intro y)

  ⌜⌝-∨-in :  ⌜ X ⌝ ∨ ⌜ Y ⌝ ⊢[ ι ] ⌜ X ⊎ Y ⌝
  ⌜⌝-∨-in =  ∨-elim (⌜⌝-mono inj₀) (⌜⌝-mono inj₁)

  ⌜⌝-∨-out :  ⌜ X ⊎ Y ⌝ ⊢[ ι ] ⌜ X ⌝ ∨ ⌜ Y ⌝
  ⌜⌝-∨-out =  ⌜⌝-elim $ ⊎-case
    (λ x → ⌜⌝-intro x » ∨-introˡ) (λ y → ⌜⌝-intro y » ∨-introʳ)

  ⌜⊤⌝-intro :  P ⊢[ ι ] ⌜ ⊤ ⌝
  ⌜⊤⌝-intro =  ⌜⌝-intro _

  ⌜⊥⌝-elim :  ⌜ ⊥ ⌝ ⊢[ ι ]* Jr
  ⌜⊥⌝-elim =  ⌜⌝-elim absurd

  ⌜⌝-→-in :  ⌜ X ⌝ →' ⌜ Y ⌝ ⊢[ ι ] ⌜ (X → Y) ⌝
  ⌜⌝-→-in =  ⌜⌝→⇒∀ » ⌜⌝-∀-in

  ⌜⌝-→-out :  ⌜ (X → Y) ⌝ ⊢[ ι ] ⌜ X ⌝ →' ⌜ Y ⌝
  ⌜⌝-→-out =  →-intro $ ⌜⌝∧-elim $ λ x → ⌜⌝-mono $ λ f → f x

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

  ∗-∃-out :  P ∗ ∃˙ Q˙ ⊢[ ι ] ∃ x , P ∗ Q˙ x
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
  -∗-apply =  -∗-elim ⊢-refl

  -- -∗ is monotone

  -∗-mono :  Q ⊢[ ι ] P →  R ⊢[ ι ] S →  P -∗ R ⊢[ ι ] Q -∗ S
  -∗-mono Q⊢P R⊢S =  -∗-intro $ ∗-monoˡ Q⊢P » -∗-apply » R⊢S

  -∗-monoˡ :  Q ⊢[ ι ] P →  P -∗ R ⊢[ ι ] Q -∗ R
  -∗-monoˡ Q⊢P =  -∗-mono Q⊢P ⊢-refl

  -∗-monoʳ :  P ⊢[ ι ] Q →  R -∗ P ⊢[ ι ] R -∗ Q
  -∗-monoʳ P⊢Q =  -∗-mono ⊢-refl P⊢Q

  -- →' can turn into -∗

  →⇒-∗ :  P →' Q ⊢[ ι ] P -∗ Q
  →⇒-∗ =  -∗-intro $ ∗⇒∧ » →-elim ⊢-refl

  ------------------------------------------------------------------------------
  -- On |=>

  -- Eliminating |=> from the antecedent

  |=>-elim :  P ⊢[ ι ] |=> Q →  |=> P ⊢[ ι ] |=> Q
  |=>-elim P⊢|=>Q =  |=>-mono P⊢|=>Q » |=>-join

  -- ⌜ ⌝ ∧ can get outside |=>

  |=>-⌜⌝∧-out :  |=> (⌜ X ⌝ ∧ P) ⊢[ ι ] ⌜ X ⌝ ∧ |=> P
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

  □-∀-out :  □ ∀˙ P˙ ⊢[ ι ] ∀˙ (□_ ∘ P˙)
  □-∀-out =  ∀-intro $ λ _ → □-mono ∀-elim

  □-∃-in :  ∃˙ (□_ ∘ P˙) ⊢[ ι ] □ ∃˙ P˙
  □-∃-in =  ∃-elim $ λ _ → □-mono ∃-intro

  □-∧-out :  □ (P ∧ Q) ⊢[ ι ] □ P ∧ □ Q
  □-∧-out =  ∧-intro (□-mono ∧-elimˡ) (□-mono ∧-elimʳ)

  □-∨-in :  □ P ∨ □ Q ⊢[ ι ] □ (P ∨ Q)
  □-∨-in =  ∨-elim (□-mono ∨-introˡ) (□-mono ∨-introʳ)

  -- □ ⊥' can be eliminated

  □-⊥-elim :  □ ⊥' ⊢[ ι ]* Jr
  □-⊥-elim =  □-elim » ⊥-elim

  ------------------------------------------------------------------------------
  -- On □, with □ˡ-∧⇒∗

  -- ∧ can turn into ∗ when one argument is under □
  □ʳ-∧⇒∗ :  P ∧ □ Q ⊢[ ι ] P ∗ □ Q
  □ʳ-∧⇒∗ =  ∧-comm » □ˡ-∧⇒∗ » ∗-comm

  -- The antecedent can be retained when the succedent is under □
  retain-□ :  P ⊢[ ι ] □ Q →  P ⊢[ ι ] □ Q ∗ P
  retain-□ P⊢Q =  ∧-intro P⊢Q ⊢-refl » □ˡ-∧⇒∗

  -- A proposition under □ can be duplicated
  dup-□ :  □ P ⊢[ ι ] □ P ∗ □ P
  dup-□ =  retain-□ ⊢-refl

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

  -- For ∀/∃
  -- They are not instances, because unfortunately Agda can't search a
  -- universally quantified instance (∀ x → ...)

  ∀-Pers :  (∀ x → Pers (P˙ x)) →  Pers (∀˙ P˙)
  ∀-Pers ∀Pers .Pers-⇒□ =  ∀-mono (λ x → ∀Pers x .Pers-⇒□) » □-∀-in

  ∃-Pers :  (∀ x → Pers (P˙ x)) →  Pers (∃˙ P˙)
  ∃-Pers ∀Pers .Pers-⇒□ =  ∃-mono (λ x → ∀Pers x .Pers-⇒□) » □-∃-in

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

    ⌜⌝-Pers :  Pers ⌜ X ⌝
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
  dup-Pers =  retain-Pers ⊢-refl

  -- -∗ can turn into →' when the left-hand side is persistent
  Pers--∗⇒→ :  {{Pers P}} →  P -∗ Q ⊢[ ι ] P →' Q
  Pers--∗⇒→ =  -∗Pers-⇒□→ » →-monoˡ Pers-⇒□

  -- Introducing and eliminating ⌜ ⌝ ∗

  ⌜⌝∗-intro :  X →  P ⊢[ ι ] ⌜ X ⌝ ∗ P
  ⌜⌝∗-intro x =  ⌜⌝∧-intro x » Persˡ-∧⇒∗

  ⌜⌝∗-elim :  (X →  P ⊢[ ι ] Q) →  ⌜ X ⌝ ∗ P ⊢[ ι ] Q
  ⌜⌝∗-elim A→P⊢Q =  ∗⇒∧ » ⌜⌝∧-elim A→P⊢Q

  -- ⌜ ⌝ ∗ can get outside |=>

  |=>-⌜⌝∗-out :  |=> (⌜ X ⌝ ∗ P) ⊢[ ι ] ⌜ X ⌝ ∗ |=> P
  |=>-⌜⌝∗-out =  |=>-mono ∗⇒∧ » |=>-⌜⌝∧-out » Persˡ-∧⇒∗

  ------------------------------------------------------------------------------
  -- On [∗]

  -- [∗] is monotone

  [∗]-mono :  All² _⊢[ ι ]_ Ps Qs →  [∗] Ps ⊢[ ι ] [∗] Qs
  [∗]-mono []ᴬ² =  ⊢-refl
  [∗]-mono (P⊢Q ∷ᴬ² Ps⊢Qs) =  ∗-mono P⊢Q ([∗]-mono Ps⊢Qs)

  -- ++ can get inside and outside [∗]

  [∗]-++-in :  [∗] Ps ∗ [∗] Qs ⊢[ ι ] [∗] (Ps ++ Qs)
  [∗]-++-in {[]} =  ∗-elimʳ
  [∗]-++-in {_ ∷ Ps'} =  ∗-assocˡ » ∗-monoʳ ([∗]-++-in {Ps'})

  [∗]-++-out :  [∗] (Ps ++ Qs) ⊢[ ι ] [∗] Ps ∗ [∗] Qs
  [∗]-++-out {[]} =  ⊤∗-intro
  [∗]-++-out {_ ∷ Ps'} =  ∗-monoʳ ([∗]-++-out {Ps'}) » ∗-assocʳ
