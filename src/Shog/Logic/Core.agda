--------------------------------------------------------------------------------
-- Proof rules on core connectives
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Logic.Core where

open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk; !)
open import Base.Func using (_$_; _∘_; it)
open import Base.Prod using (_×_; _,_; ∑-syntax)
open import Base.Sum using (_⊎_; inj₀; inj₁; ⊎-case)
open import Base.Few using (⟨2⟩; 0₂; 1₂; ⊤; ⊥; binary; absurd)
open import Base.List using (List; []; _∷_; _++_)
open import Base.List.All2 using (All²; []ᴬ²; _∷ᴬ²_)
open import Shog.Logic.Prop using (Prop'; ∀˙; ∃˙; ∀∈-syntax; ∃∈-syntax;
  ∀-syntax; ∃-syntax; _∧_; _∨_; ⊤'; ⊥'; ⌜_⌝; _→'_; _∗_; _-∗_; |=>_; □_; [∗]_;
  IsBasic; ∀-IsBasic; ∃-IsBasic; ∗-IsBasic; □-IsBasic; Basic; isBasic)

-- Import and re-export
open import Shog.Logic.Judg public using (
  JudgRes; Pure; _⊢[_]*_; _⊢[_]_; _⊢[<_]_; Pers; Pers-⇒□;
  ⊢-refl; _»_; ∀-intro; ∃-elim; ∀-elim; ∃-intro; choice; →-intro; →-elim;
  ⊤∗-elim; ⊤∗-intro; ∗-comm; ∗-assocˡ; ∗-monoˡ; -∗-intro; -∗-elim;
  |=>-mono; |=>-intro; |=>-join; |=>-frameˡ; |=>-∃-out;
  □-mono; □-elim; □-dup; □ˡ-∧⇒∗; □-∀-in; □-∃-out)

private variable
  ι :  Size
  P P' Q Q' R R' S S' T T' U U' V V' :  Prop' ∞
  Jr :  JudgRes
  X Y :  Set₁
  Y˙ :  X → Set₁
  P˙ Q˙ :  X → Prop' ∞
  Ps Qs :  List (Prop' ∞)

abstract

  ------------------------------------------------------------------------------
  -- On ∀/∃/∧/∨/⊤'/⊥'

  -- Introduce ∧/⊤' & eliminate ∨/⊥'

  ∧-intro :  P ⊢[ ι ] Q →  P ⊢[ ι ] R →  P ⊢[ ι ] Q ∧ R
  ∧-intro P⊢Q P⊢R =  ∀-intro $ binary P⊢Q P⊢R

  ∨-elim :  P ⊢[ ι ]* Jr →  Q ⊢[ ι ]* Jr →  P ∨ Q ⊢[ ι ]* Jr
  ∨-elim P⊢*Jr Q⊢*Jr =  ∃-elim $ binary P⊢*Jr Q⊢*Jr

  ⊤-intro :  P ⊢[ ι ] ⊤'
  ⊤-intro =  ∀-intro absurd

  ⊥-elim :  ⊥' ⊢[ ι ]* Jr
  ⊥-elim =  ∃-elim absurd

  -- Eliminate ∧/⊤' & introduce ∨/⊥'

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

  -- Introduce & eliminate ⌜⌝

  ⌜⌝-intro :  X →  P ⊢[ ι ] ⌜ X ⌝
  ⌜⌝-intro x =  ⊤-intro » ∃-intro {x = x}

  ⌜⌝-elim :  (X →  ⊤' ⊢[ ι ]* Jr) →  ⌜ X ⌝ ⊢[ ι ]* Jr
  ⌜⌝-elim A→⊤⊢P =  ∃-elim $ λ x →  A→⊤⊢P x

  -- ⌜⌝ is monotone

  ⌜⌝-mono :  (X →  Y) →  ⌜ X ⌝ ⊢[ ι ] ⌜ Y ⌝
  ⌜⌝-mono f =  ⌜⌝-elim $ λ x →  ⌜⌝-intro $ f x

  -- Introduce & eliminate ⌜ ⌝ ∧

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

  -- Introduce ∗ ⊤'

  ∗⊤-intro :  P ⊢[ ι ] P ∗ ⊤'
  ∗⊤-intro =  ⊤∗-intro » ∗-comm

  -- ∗ is associative

  ∗-assocʳ :  P ∗ (Q ∗ R) ⊢[ ι ] (P ∗ Q) ∗ R
  ∗-assocʳ =  ∗-comm » ∗-monoˡ ∗-comm » ∗-assocˡ » ∗-comm » ∗-monoˡ ∗-comm

  -- ∗ can turn into ∧

  ∗⇒∧ :  P ∗ Q ⊢[ ι ] P ∧ Q
  ∗⇒∧ =  ∧-intro ∗-elimˡ ∗-elimʳ

  -- ∃ can get outside ∗

  ∗-∃-out :  P ∗ ∃˙ Q˙ ⊢[ ι ] ∃ x , P ∗ Q˙ x
  ∗-∃-out =  -∗-elim $ ∃-elim λ _ → -∗-intro ∃-intro

  -- Eliminate ∃/∨/⊥' with ∗

  ∃∗-elim :  (∀ x → P˙ x ∗ Q ⊢[ ι ]* Jr) →  ∃˙ P˙ ∗ Q ⊢[ ι ]* Jr
  ∃∗-elim →P˙∗⊢ =  ∗-comm » ∗-∃-out » ∃-elim $ λ x → ∗-comm » →P˙∗⊢ x

  ∨∗-elim :  P ∗ Q ⊢[ ι ]* Jr →  P' ∗ Q ⊢[ ι ]* Jr →  (P ∨ P') ∗ Q ⊢[ ι ]* Jr
  ∨∗-elim P∗⊢ P'∗⊢ =  ∃∗-elim (binary P∗⊢ P'∗⊢)

  ⊥∗-elim :  ⊥' ∗ P ⊢[ ι ]* Jr
  ⊥∗-elim =  ∗-elimˡ » ⊥-elim

  ------------------------------------------------------------------------------
  -- Enrich ∗-mono

  ∗-monoʳˡ :  Q ⊢[ ι ] Q' →  P ∗ Q ∗ R ⊢[ ι ] P ∗ Q' ∗ R
  ∗-monoʳˡ =  ∗-monoʳ ∘ ∗-monoˡ

  ∗-monoʳ² :  R ⊢[ ι ] R' →  P ∗ Q ∗ R ⊢[ ι ] P ∗ Q ∗ R'
  ∗-monoʳ² =  ∗-monoʳ ∘ ∗-monoʳ

  ∗-monoʳ²ˡ :  R ⊢[ ι ] R' →  P ∗ Q ∗ R ∗ S ⊢[ ι ] P ∗ Q ∗ R' ∗ S
  ∗-monoʳ²ˡ =  ∗-monoʳ² ∘ ∗-monoˡ

  ∗-monoʳ³ :  S ⊢[ ι ] S' →  P ∗ Q ∗ R ∗ S ⊢[ ι ] P ∗ Q ∗ R ∗ S'
  ∗-monoʳ³ =  ∗-monoʳ² ∘ ∗-monoʳ

  ∗-monoʳ³ˡ :  S ⊢[ ι ] S' →  P ∗ Q ∗ R ∗ S ∗ T ⊢[ ι ] P ∗ Q ∗ R ∗ S' ∗ T
  ∗-monoʳ³ˡ =  ∗-monoʳ³ ∘ ∗-monoˡ

  ∗-monoʳ⁴ :  T ⊢[ ι ] T' →  P ∗ Q ∗ R ∗ S ∗ T ⊢[ ι ] P ∗ Q ∗ R ∗ S ∗ T'
  ∗-monoʳ⁴ =  ∗-monoʳ³ ∘ ∗-monoʳ

  ∗-monoʳ⁴ˡ :  T ⊢[ ι ] T' →
               P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ ι ] P ∗ Q ∗ R ∗ S ∗ T' ∗ U
  ∗-monoʳ⁴ˡ =  ∗-monoʳ⁴ ∘ ∗-monoˡ

  ∗-monoʳ⁵ :  U ⊢[ ι ] U' →  P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ ι ] P ∗ Q ∗ R ∗ S ∗ T ∗ U'
  ∗-monoʳ⁵ =  ∗-monoʳ⁴ ∘ ∗-monoʳ

  ∗-monoʳ⁵ˡ :  U ⊢[ ι ] U' →
               P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ ι ] P ∗ Q ∗ R ∗ S ∗ T ∗ U' ∗ V
  ∗-monoʳ⁵ˡ =  ∗-monoʳ⁵ ∘ ∗-monoˡ

  ∗-monoʳ⁶ :  V ⊢[ ι ] V' →
              P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ ι ] P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V'
  ∗-monoʳ⁶ =  ∗-monoʳ⁵ ∘ ∗-monoʳ

  ------------------------------------------------------------------------------
  -- Shuffle a nested separating conjunction

  -- Move a separating conjunct to the head

  pullʳˡ :  P ∗ Q ∗ R ⊢[ ι ] Q ∗ P ∗ R
  pullʳˡ =  ∗-assocʳ » ∗-monoˡ ∗-comm » ∗-assocˡ

  pullʳ² :  P ∗ Q ∗ R ⊢[ ι ] R ∗ P ∗ Q
  pullʳ² =  ∗-monoʳ ∗-comm » pullʳˡ

  pullʳ²ˡ :  P ∗ Q ∗ R ∗ S ⊢[ ι ] R ∗ P ∗ Q ∗ S
  pullʳ²ˡ =  ∗-monoʳ pullʳˡ » pullʳˡ

  pullʳ³ :  P ∗ Q ∗ R ∗ S ⊢[ ι ] S ∗ P ∗ Q ∗ R
  pullʳ³ =  ∗-monoʳ pullʳ² » pullʳˡ

  pullʳ³ˡ :  P ∗ Q ∗ R ∗ S ∗ T ⊢[ ι ] S ∗ P ∗ Q ∗ R ∗ T
  pullʳ³ˡ =  ∗-monoʳ pullʳ²ˡ » pullʳˡ

  pullʳ⁴ :  P ∗ Q ∗ R ∗ S ∗ T ⊢[ ι ] T ∗ P ∗ Q ∗ R ∗ S
  pullʳ⁴ =  ∗-monoʳ pullʳ³ » pullʳˡ

  pullʳ⁴ˡ :  P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ ι ] T ∗ P ∗ Q ∗ R ∗ S ∗ U
  pullʳ⁴ˡ =  ∗-monoʳ pullʳ³ˡ » pullʳˡ

  pullʳ⁵ :  P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ ι ] U ∗ P ∗ Q ∗ R ∗ S ∗ T
  pullʳ⁵ =  ∗-monoʳ pullʳ⁴ » pullʳˡ

  pullʳ⁵ˡ :  P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ ι ] U ∗ P ∗ Q ∗ R ∗ S ∗ T ∗ V
  pullʳ⁵ˡ =  ∗-monoʳ pullʳ⁴ˡ » pullʳˡ

  pullʳ⁶ :  P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ ι ] V ∗ P ∗ Q ∗ R ∗ S ∗ T ∗ U
  pullʳ⁶ =  ∗-monoʳ pullʳ⁵ » pullʳˡ

  -- Move the head separating conjunct to somewhere deeper

  pushʳˡ :  P ∗ Q ∗ R ⊢[ ι ] Q ∗ P ∗ R
  pushʳˡ =  pullʳˡ

  pushʳ² :  P ∗ Q ∗ R ⊢[ ι ] Q ∗ R ∗ P
  pushʳ² =  pushʳˡ » ∗-monoʳ ∗-comm

  pushʳ²ˡ :  P ∗ Q ∗ R ∗ S ⊢[ ι ] Q ∗ R ∗ P ∗ S
  pushʳ²ˡ =  pushʳˡ » ∗-monoʳ pushʳˡ

  pushʳ³ :  P ∗ Q ∗ R ∗ S ⊢[ ι ] Q ∗ R ∗ S ∗ P
  pushʳ³ =  pushʳˡ » ∗-monoʳ pushʳ²

  pushʳ³ˡ :  P ∗ Q ∗ R ∗ S ∗ T ⊢[ ι ] Q ∗ R ∗ S ∗ P ∗ T
  pushʳ³ˡ =  pushʳˡ » ∗-monoʳ pushʳ²ˡ

  pushʳ⁴ :  P ∗ Q ∗ R ∗ S ∗ T ⊢[ ι ] Q ∗ R ∗ S ∗ T ∗ P
  pushʳ⁴ =  pushʳˡ » ∗-monoʳ pushʳ³

  pushʳ⁴ˡ :  P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ ι ] Q ∗ R ∗ S ∗ T ∗ P ∗ U
  pushʳ⁴ˡ =  pushʳˡ » ∗-monoʳ pushʳ³ˡ

  pushʳ⁵ :  P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ ι ] Q ∗ R ∗ S ∗ T ∗ U ∗ P
  pushʳ⁵ =  pushʳˡ » ∗-monoʳ pushʳ⁴

  pushʳ⁵ˡ :  P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ ι ] Q ∗ R ∗ S ∗ T ∗ U ∗ P ∗ V
  pushʳ⁵ˡ =  pushʳˡ » ∗-monoʳ pushʳ⁴ˡ

  pushʳ⁶ :  P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ ι ] Q ∗ R ∗ S ∗ T ∗ U ∗ V ∗ P
  pushʳ⁶ =  pushʳˡ » ∗-monoʳ pushʳ⁵

  ------------------------------------------------------------------------------
  -- On -∗

  -- Introduce P -∗

  -∗-const :  Q ⊢[ ι ] P -∗ Q
  -∗-const =  -∗-intro ∗-elimʳ

  -- Apply -∗

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

  -- Apply the head magic wand to the succedent

  -∗∗-apply :  Q ⊢[ ι ] P →  (P -∗ P') ∗ Q ⊢[ ι ] P'
  -∗∗-apply Q⊢P =  ∗-monoˡ (-∗-monoˡ Q⊢P) » ∗-comm » -∗-apply

  ------------------------------------------------------------------------------
  -- On |=>

  -- Eliminate |=> from the antecedent

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

  -- Introduce |=> to the succedent

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
  -- Derive Pers P

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
  -- Use Pers P

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

  -- Duplicate a persistent separting conjunct
  dup-Pers-∗ :  {{Pers P}} →  P ∗ Q ⊢[ ι ] P ∗ P ∗ Q
  dup-Pers-∗ =  ∗-monoˡ dup-Pers » ∗-assocˡ

  -- -∗ can turn into →' when the left-hand side is persistent
  Pers--∗⇒→ :  {{Pers P}} →  P -∗ Q ⊢[ ι ] P →' Q
  Pers--∗⇒→ =  -∗Pers-⇒□→ » →-monoˡ Pers-⇒□

  -- Introduce & eliminate ⌜ ⌝ ∗

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
