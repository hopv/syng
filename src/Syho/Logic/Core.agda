--------------------------------------------------------------------------------
-- Proof rules on core connectives
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Core where

open import Base.Level using (Level; ↓_; ↑_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk; !)
open import Base.Func using (_$_; _∘_; it)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_)
open import Base.Sum using (_⊎_; inj₀; inj₁; ⊎-case)
open import Base.Few using (⟨2⟩; 0₂; 1₂; ⊤; ⊥; binary; absurd)
open import Base.List using (List; []; _∷_; _++_)
open import Base.List.All2 using (All²; []ᴬ²; _∷ᴬ²_)
open import Syho.Logic.Prop using (Prop'; ∀₁˙; ∃₁˙; ∀₀˙; ∃₀˙; ∀₁∈-syntax;
  ∃₁∈-syntax; ∀₁-syntax;∃₁-syntax; ∀₀∈-syntax; ∃₀∈-syntax; ∀₀-syntax; ∃₀-syntax;
  _∧_; _∨_; ⊤'; ⊥'; ⌜_⌝₁; ⌜_⌝₀; _→'_; _∗_; _-∗_; |=>_; □_; [∗]_)

-- Import and re-export
open import Syho.Logic.Judg public using (JudgRes; Pure; _⊢[_]*_; _⊢[_]_;
  _⊢[<_]_; Pers; Pers-⇒□; ⊢-refl; _»_; ∀₁-intro; ∃₁-elim; ∀₁-elim; ∃₁-intro;
  choice₁; →-intro; →-elim; ⊤∗-elim; ⊤∗-intro; ∗-comm; ∗-assocˡ; ∗-monoˡ;
  -∗-intro; -∗-elim; |=>-mono; |=>-intro; |=>-join; |=>-eatˡ; |=>-∃₁-out;
  □-mono; □-elim; □-dup; □ˡ-∧⇒∗; □-∀₁-in; □-∃₁-out)

private variable
  ι :  Size
  P P' Q Q' R R' S S' T T' U U' V V' :  Prop' ∞
  Jr :  JudgRes
  ℓ :  Level
  X Y :  Set ℓ
  x :  X
  Y˙ :  X → Set ℓ
  P˙ Q˙ :  X → Prop' ∞
  Ps Qs :  List (Prop' ∞)

abstract

  -->  ⊢-refl :  P ⊢[ ι ] P

  -->  _»_ :  P ⊢[ ι ] Q →  Q ⊢[ ι ]* Jr →  P ⊢[ ι ]* Jr

  ------------------------------------------------------------------------------
  -- On ∀/∃/∧/∨/⊤'/⊥'

  -- Introduce ∀/∧/⊤' & eliminate ∃/∨/⊥'

  -->  ∀₁-intro :  (∀ x →  P ⊢[ ι ] Q˙ x) →  P ⊢[ ι ] ∀₁˙ Q˙

  ∀₀-intro :  (∀ x →  P ⊢[ ι ] Q˙ x) →  P ⊢[ ι ] ∀₀˙ Q˙
  ∀₀-intro =  ∀₁-intro ∘ _∘ ↓_

  -->  ∃₁-elim :  (∀ x →  P˙ x ⊢[ ι ]* Jr) →  ∃₁˙ P˙ ⊢[ ι ]* Jr

  ∃₀-elim :  (∀ x →  P˙ x ⊢[ ι ]* Jr) →  ∃₀˙ P˙ ⊢[ ι ]* Jr
  ∃₀-elim =  ∃₁-elim ∘ _∘ ↓_

  ∧-intro :  P ⊢[ ι ] Q →  P ⊢[ ι ] R →  P ⊢[ ι ] Q ∧ R
  ∧-intro P⊢Q P⊢R =  ∀₁-intro $ binary P⊢Q P⊢R

  ∨-elim :  P ⊢[ ι ]* Jr →  Q ⊢[ ι ]* Jr →  P ∨ Q ⊢[ ι ]* Jr
  ∨-elim P⊢*Jr Q⊢*Jr =  ∃₁-elim $ binary P⊢*Jr Q⊢*Jr

  ⊤-intro :  P ⊢[ ι ] ⊤'
  ⊤-intro =  ∀₁-intro absurd

  ⊥-elim :  ⊥' ⊢[ ι ]* Jr
  ⊥-elim =  ∃₁-elim absurd

  -- Eliminate ∀/∧/⊤' & introduce ∃/∨/⊥'

  -->  ∀₁-elim :  ∀ x →  ∀₁˙ P˙ ⊢[ ι ] P˙ x

  ∀₀-elim :  ∀ x →  ∀₀˙ P˙ ⊢[ ι ] P˙ x
  ∀₀-elim =  ∀₁-elim ∘ ↑_

  -->  ∃₁-intro :  ∀ x →  P˙ x ⊢[ ι ] ∃₁˙ P˙

  ∃₀-intro :  ∀ x →  P˙ x ⊢[ ι ] ∃₀˙ P˙
  ∃₀-intro =  ∃₁-intro ∘ ↑_

  ∧-elimˡ :  P ∧ Q ⊢[ ι ] P
  ∧-elimˡ =  ∀₁-elim 0₂

  ∧-elimʳ :  P ∧ Q ⊢[ ι ] Q
  ∧-elimʳ =  ∀₁-elim 1₂

  ∨-introˡ :  P ⊢[ ι ] P ∨ Q
  ∨-introˡ =  ∃₁-intro 0₂

  ∨-introʳ :  Q ⊢[ ι ] P ∨ Q
  ∨-introʳ =  ∃₁-intro 1₂

  -- ∀/∃/∧/∨ is monotone

  ∀₁-mono :  (∀ x →  P˙ x ⊢[ ι ] Q˙ x) →  ∀₁˙ P˙ ⊢[ ι ] ∀₁˙ Q˙
  ∀₁-mono P˙⊢Q˙ =  ∀₁-intro $ λ x →  ∀₁-elim x » P˙⊢Q˙ x

  ∃₁-mono :  (∀ x →  P˙ x ⊢[ ι ] Q˙ x) →  ∃₁˙ P˙ ⊢[ ι ] ∃₁˙ Q˙
  ∃₁-mono P˙⊢Q˙ =  ∃₁-elim $ λ x →  P˙⊢Q˙ x » ∃₁-intro x

  ∀₀-mono :  (∀ x →  P˙ x ⊢[ ι ] Q˙ x) →  ∀₀˙ P˙ ⊢[ ι ] ∀₀˙ Q˙
  ∀₀-mono =  ∀₁-mono ∘ _∘ ↓_

  ∃₀-mono :  (∀ x →  P˙ x ⊢[ ι ] Q˙ x) →  ∃₀˙ P˙ ⊢[ ι ] ∃₀˙ Q˙
  ∃₀-mono =  ∃₁-mono ∘ _∘ ↓_

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

  -- Choice

  -->  choice₁ :  ∀ {P˙˙ : ∀ (x : X) → Y˙ x → Prop' ∞} →
  -->    ∀₁ x , ∃₁ y , P˙˙ x y ⊢[ ι ] ∃₁ y˙ ∈ (∀ x → Y˙ x) , ∀₁ x , P˙˙ x (y˙ x)

  choice₀ :  ∀ {P˙˙ : ∀ (x : X) → Y˙ x → Prop' ∞} →
    ∀₀ x , ∃₀ y , P˙˙ x y ⊢[ ι ] ∃₀ y˙ ∈ (∀ x → Y˙ x) , ∀₀ x , P˙˙ x (y˙ x)
  choice₀ =  choice₁ » ∃₁-elim $ λ _ → ∃₀-intro _

  ------------------------------------------------------------------------------
  -- On →'

  -->  →-intro :  P ∧ Q ⊢[ ι ] R →  Q ⊢[ ι ] P →' R

  -->  →-elim :  Q ⊢[ ι ] P →' R →  P ∧ Q ⊢[ ι ] R

  -- Introduce P →'

  →-const :  Q ⊢[ ι ] P →' Q
  →-const =  →-intro ∧-elimʳ

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

  ⌜⌝₁-intro :  X →  P ⊢[ ι ] ⌜ X ⌝₁
  ⌜⌝₁-intro x =  ⊤-intro » ∃₁-intro x

  ⌜⌝₁-elim :  (X →  ⊤' ⊢[ ι ]* Jr) →  ⌜ X ⌝₁ ⊢[ ι ]* Jr
  ⌜⌝₁-elim X→⊤⊢P =  ∃₁-elim $ λ x →  X→⊤⊢P x

  ⌜⌝₀-intro :  X →  P ⊢[ ι ] ⌜ X ⌝₀
  ⌜⌝₀-intro =  ⌜⌝₁-intro ∘ ↑_

  ⌜⌝₀-elim :  (X →  ⊤' ⊢[ ι ]* Jr) →  ⌜ X ⌝₀ ⊢[ ι ]* Jr
  ⌜⌝₀-elim =  ⌜⌝₁-elim ∘ _∘ ↓_

  -- ⌜⌝ is monotone

  ⌜⌝₁-mono :  (X → Y) →  ⌜ X ⌝₁ ⊢[ ι ] ⌜ Y ⌝₁
  ⌜⌝₁-mono f =  ⌜⌝₁-elim $ λ x →  ⌜⌝₁-intro $ f x

  ⌜⌝₀-mono :  (X → Y) →  ⌜ X ⌝₀ ⊢[ ι ] ⌜ Y ⌝₀
  ⌜⌝₀-mono f =  ⌜⌝₁-mono $ ↑_ ∘ f ∘ ↓_

  -- Introduce & eliminate ⌜ ⌝ ∧

  ⌜⌝₁∧-intro :  X →  P ⊢[ ι ] ⌜ X ⌝₁ ∧ P
  ⌜⌝₁∧-intro x =  ∧-intro (⌜⌝₁-intro x) ⊢-refl

  ⌜⌝₁∧-elim :  (X →  P ⊢[ ι ] Q) →  ⌜ X ⌝₁ ∧ P ⊢[ ι ] Q
  ⌜⌝₁∧-elim X→P⊢Q =  ∧-comm » →-elim $ ⌜⌝₁-elim $
    λ x →  →-intro $ ∧-elimˡ » X→P⊢Q x

  ⌜⌝₀∧-intro :  X →  P ⊢[ ι ] ⌜ X ⌝₀ ∧ P
  ⌜⌝₀∧-intro =  ⌜⌝₁∧-intro ∘ ↑_

  ⌜⌝₀∧-elim :  (X →  P ⊢[ ι ] Q) →  ⌜ X ⌝₀ ∧ P ⊢[ ι ] Q
  ⌜⌝₀∧-elim =  ⌜⌝₁∧-elim ∘ _∘ ↓_

  -- ⌜ X ⌝ →' is the same with ∀ _ ∈ X ,

  ⌜⌝→⇒∀₁ :  ⌜ X ⌝₁ →' P ⊢[ ι ] ∀₁ _ ∈ X , P
  ⌜⌝→⇒∀₁ =  ∀₁-intro $ λ x →  ⌜⌝₁∧-intro x » →-apply

  ∀₁⇒⌜⌝→ :  ∀₁ _ ∈ X , P ⊢[ ι ] ⌜ X ⌝₁ →' P
  ∀₁⇒⌜⌝→ =  →-intro $ ⌜⌝₁∧-elim $ λ x →  ∀₁-elim x

  ⌜⌝→⇒∀₀ :  ⌜ X ⌝₀ →' P ⊢[ ι ] ∀₀ _ ∈ X , P
  ⌜⌝→⇒∀₀ =  ⌜⌝→⇒∀₁

  ∀₀⇒⌜⌝→ :  ∀₀ _ ∈ X , P ⊢[ ι ] ⌜ X ⌝₀ →' P
  ∀₀⇒⌜⌝→ =  ∀₁⇒⌜⌝→

  -- ⌜ X ⌝ ∧ is the same with ∃ _ ∈ X ,

  ⌜⌝∧⇒∃₁ :  ⌜ X ⌝₁ ∧ P ⊢[ ι ] ∃₁ _ ∈ X , P
  ⌜⌝∧⇒∃₁ =  ⌜⌝₁∧-elim $ λ x →  ⊢-refl » ∃₁-intro x

  ∃₁⇒⌜⌝∧ :  ∃₁ _ ∈ X , P ⊢[ ι ] ⌜ X ⌝₁ ∧ P
  ∃₁⇒⌜⌝∧ =  ∃₁-elim $ λ x →  ⌜⌝₁∧-intro x

  ⌜⌝∧⇒∃₀ :  ⌜ X ⌝₀ ∧ P ⊢[ ι ] ∃₀ _ ∈ X , P
  ⌜⌝∧⇒∃₀ =  ⌜⌝∧⇒∃₁

  ∃₀⇒⌜⌝∧ :  ∃₀ _ ∈ X , P ⊢[ ι ] ⌜ X ⌝₀ ∧ P
  ∃₀⇒⌜⌝∧ =  ∃₁⇒⌜⌝∧

  -- ⌜⌝ commutes with ∀/∃/∧/∨/⊤'/⊥'/→

  ⌜⌝₁-∀₁-in :  ∀₁ x , ⌜ Y˙ x ⌝₁ ⊢[ ι ] ⌜ (∀ x → Y˙ x) ⌝₁
  ⌜⌝₁-∀₁-in =  choice₁ » ∃₁-mono $ λ _ → ⊤-intro

  ⌜⌝₁-∀₁-out :  ⌜ (∀ x → Y˙ x) ⌝₁ ⊢[ ι ] ∀₁ x , ⌜ Y˙ x ⌝₁
  ⌜⌝₁-∀₁-out =  ∀₁-intro $ λ x →  ⌜⌝₁-elim $ λ f →  ⌜⌝₁-intro $ f x

  ⌜⌝₀-∀₀-in :  ∀₀ x , ⌜ Y˙ x ⌝₀ ⊢[ ι ] ⌜ (∀ x → Y˙ x) ⌝₀
  ⌜⌝₀-∀₀-in =  choice₀ » ∃₀-mono $ λ _ → ⊤-intro

  ⌜⌝₀-∀₀-out :  ⌜ (∀ x → Y˙ x) ⌝₀ ⊢[ ι ] ∀₀ x , ⌜ Y˙ x ⌝₀
  ⌜⌝₀-∀₀-out =  ∀₀-intro $ λ x →  ⌜⌝₀-elim $ λ f →  ⌜⌝₀-intro $ f x

  ⌜⌝₁-∃₁-in :  ∃₁ x , ⌜ Y˙ x ⌝₁ ⊢[ ι ] ⌜ ∑ x , Y˙ x ⌝₁
  ⌜⌝₁-∃₁-in =  ∃₁-elim $ λ x →  ⌜⌝₁-mono $ λ y →  x , y

  ⌜⌝₁-∃₁-out :  ⌜ ∑ x , Y˙ x ⌝₁ ⊢[ ι ] ∃₁ x , ⌜ Y˙ x ⌝₁
  ⌜⌝₁-∃₁-out =  ⌜⌝₁-elim $ λ (x , y) →  ⌜⌝₁-intro y » ∃₁-intro x

  ⌜⌝₀-∃₀-in :  ∃₀ x , ⌜ Y˙ x ⌝₀ ⊢[ ι ] ⌜ ∑ x , Y˙ x ⌝₀
  ⌜⌝₀-∃₀-in =  ∃₀-elim $ λ x →  ⌜⌝₀-mono $ λ y →  x , y

  ⌜⌝₀-∃₀-out :  ⌜ ∑ x , Y˙ x ⌝₀ ⊢[ ι ] ∃₀ x , ⌜ Y˙ x ⌝₀
  ⌜⌝₀-∃₀-out =  ⌜⌝₀-elim $ λ (x , y) →  ⌜⌝₀-intro y » ∃₀-intro x

  ⌜⌝₁-∧-in :  ⌜ X ⌝₁ ∧ ⌜ Y ⌝₁ ⊢[ ι ] ⌜ X × Y ⌝₁
  ⌜⌝₁-∧-in =  ⌜⌝₁∧-elim $ λ x →  ⌜⌝₁-mono $ λ y →  (x , y)

  ⌜⌝₁-∧-out :  ⌜ X × Y ⌝₁ ⊢[ ι ] ⌜ X ⌝₁ ∧ ⌜ Y ⌝₁
  ⌜⌝₁-∧-out =  ⌜⌝₁-elim $ λ (x , y) →  ∧-intro (⌜⌝₁-intro x) (⌜⌝₁-intro y)

  ⌜⌝₀-∧-in :  ⌜ X ⌝₀ ∧ ⌜ Y ⌝₀ ⊢[ ι ] ⌜ X × Y ⌝₀
  ⌜⌝₀-∧-in =  ⌜⌝₀∧-elim $ λ x →  ⌜⌝₀-mono $ λ y →  (x , y)

  ⌜⌝₀-∧-out :  ⌜ X × Y ⌝₀ ⊢[ ι ] ⌜ X ⌝₀ ∧ ⌜ Y ⌝₀
  ⌜⌝₀-∧-out =  ⌜⌝₀-elim $ λ (x , y) →  ∧-intro (⌜⌝₀-intro x) (⌜⌝₀-intro y)

  ⌜⌝₁-∨-in :  ⌜ X ⌝₁ ∨ ⌜ Y ⌝₁ ⊢[ ι ] ⌜ X ⊎ Y ⌝₁
  ⌜⌝₁-∨-in =  ∨-elim (⌜⌝₁-mono inj₀) (⌜⌝₁-mono inj₁)

  ⌜⌝₁-∨-out :  ⌜ X ⊎ Y ⌝₁ ⊢[ ι ] ⌜ X ⌝₁ ∨ ⌜ Y ⌝₁
  ⌜⌝₁-∨-out =  ⌜⌝₁-elim $ ⊎-case
    (λ x → ⌜⌝₁-intro x » ∨-introˡ) (λ y → ⌜⌝₁-intro y » ∨-introʳ)

  ⌜⌝₀-∨-in :  ⌜ X ⌝₀ ∨ ⌜ Y ⌝₀ ⊢[ ι ] ⌜ X ⊎ Y ⌝₀
  ⌜⌝₀-∨-in =  ∨-elim (⌜⌝₀-mono inj₀) (⌜⌝₀-mono inj₁)

  ⌜⌝₀-∨-out :  ⌜ X ⊎ Y ⌝₀ ⊢[ ι ] ⌜ X ⌝₀ ∨ ⌜ Y ⌝₀
  ⌜⌝₀-∨-out =  ⌜⌝₀-elim $ ⊎-case
    (λ x → ⌜⌝₀-intro x » ∨-introˡ) (λ y → ⌜⌝₀-intro y » ∨-introʳ)

  ⌜⊤⌝₁-intro :  P ⊢[ ι ] ⌜ ⊤ ⌝₁
  ⌜⊤⌝₁-intro =  ⌜⌝₁-intro _

  ⌜⊤⌝₀-intro :  P ⊢[ ι ] ⌜ ⊤ ⌝₀
  ⌜⊤⌝₀-intro =  ⌜⌝₀-intro _

  ⌜⊥⌝₁-elim :  ⌜ ⊥ ⌝₁ ⊢[ ι ]* Jr
  ⌜⊥⌝₁-elim =  ⌜⌝₁-elim absurd

  ⌜⊥⌝₀-elim :  ⌜ ⊥ ⌝₀ ⊢[ ι ]* Jr
  ⌜⊥⌝₀-elim =  ⌜⌝₀-elim absurd

  ⌜⌝₁-→-in :  ⌜ X ⌝₁ →' ⌜ Y ⌝₁ ⊢[ ι ] ⌜ (X → Y) ⌝₁
  ⌜⌝₁-→-in =  ⌜⌝→⇒∀₁ » ⌜⌝₁-∀₁-in

  ⌜⌝₁-→-out :  ⌜ (X → Y) ⌝₁ ⊢[ ι ] ⌜ X ⌝₁ →' ⌜ Y ⌝₁
  ⌜⌝₁-→-out =  →-intro $ ⌜⌝₁∧-elim $ λ x → ⌜⌝₁-mono $ λ f → f x

  ⌜⌝₀-→-in :  ⌜ X ⌝₀ →' ⌜ Y ⌝₀ ⊢[ ι ] ⌜ (X → Y) ⌝₀
  ⌜⌝₀-→-in =  ⌜⌝→⇒∀₀ » ⌜⌝₀-∀₀-in

  ⌜⌝₀-→-out :  ⌜ (X → Y) ⌝₀ ⊢[ ι ] ⌜ X ⌝₀ →' ⌜ Y ⌝₀
  ⌜⌝₀-→-out =  →-intro $ ⌜⌝₀∧-elim $ λ x → ⌜⌝₀-mono $ λ f → f x

  ------------------------------------------------------------------------------
  -- On ∗

  -->  ∗-comm :  P ∗ Q ⊢[ ι ] Q ∗ P

  -- ∗ is monotone

  -->  ∗-monoˡ :  P ⊢[ ι ] Q →  P ∗ R ⊢[ ι ] Q ∗ R

  ∗-monoʳ :  P ⊢[ ι ] Q →  R ∗ P ⊢[ ι ] R ∗ Q
  ∗-monoʳ P⊢Q =  ∗-comm » ∗-monoˡ P⊢Q » ∗-comm

  ∗-mono :  P ⊢[ ι ] Q →  R ⊢[ ι ] S →  P ∗ R ⊢[ ι ] Q ∗ S
  ∗-mono P⊢Q R⊢S =  ∗-monoˡ P⊢Q » ∗-monoʳ R⊢S

  -- Eliminating ∗

  -->  ⊤∗-elim :  ⊤' ∗ P ⊢[ ι ] P

  ∗-elimʳ :  P ∗ Q ⊢[ ι ] Q
  ∗-elimʳ =  ∗-monoˡ ⊤-intro » ⊤∗-elim

  ∗-elimˡ :  P ∗ Q ⊢[ ι ] P
  ∗-elimˡ =  ∗-comm » ∗-elimʳ

  -- Introduce ⊤' with ∗

  -->  ⊤∗-intro :  P ⊢[ ι ] ⊤' ∗ P

  ∗⊤-intro :  P ⊢[ ι ] P ∗ ⊤'
  ∗⊤-intro =  ⊤∗-intro » ∗-comm

  -- ∗ is associative

  -->  ∗-assocˡ :  (P ∗ Q) ∗ R ⊢[ ι ] P ∗ (Q ∗ R)

  ∗-assocʳ :  P ∗ (Q ∗ R) ⊢[ ι ] (P ∗ Q) ∗ R
  ∗-assocʳ =  ∗-comm » ∗-monoˡ ∗-comm » ∗-assocˡ » ∗-comm » ∗-monoˡ ∗-comm

  -- ∗ can turn into ∧

  ∗⇒∧ :  P ∗ Q ⊢[ ι ] P ∧ Q
  ∗⇒∧ =  ∧-intro ∗-elimˡ ∗-elimʳ

  -- ∃ can get outside ∗

  ∗-∃₁-out :  P ∗ ∃₁˙ Q˙ ⊢[ ι ] ∃₁ x , P ∗ Q˙ x
  ∗-∃₁-out =  -∗-elim $ ∃₁-elim $ -∗-intro ∘ ∃₁-intro

  ∗-∃₀-out :  P ∗ ∃₀˙ Q˙ ⊢[ ι ] ∃₀ x , P ∗ Q˙ x
  ∗-∃₀-out =  ∗-∃₁-out

  -- Eliminate ∃/∨/⊥' with ∗

  ∃₁∗-elim :  (∀ x → P˙ x ∗ Q ⊢[ ι ]* Jr) →  ∃₁˙ P˙ ∗ Q ⊢[ ι ]* Jr
  ∃₁∗-elim ∀P˙∗⊢ =  ∗-comm » ∗-∃₁-out » ∃₁-elim $ λ x → ∗-comm » ∀P˙∗⊢ x

  ∃₀∗-elim :  (∀ x → P˙ x ∗ Q ⊢[ ι ]* Jr) →  ∃₀˙ P˙ ∗ Q ⊢[ ι ]* Jr
  ∃₀∗-elim =  ∃₁∗-elim ∘ _∘ ↓_

  ∨∗-elim :  P ∗ Q ⊢[ ι ]* Jr →  P' ∗ Q ⊢[ ι ]* Jr →  (P ∨ P') ∗ Q ⊢[ ι ]* Jr
  ∨∗-elim P∗⊢ P'∗⊢ =  ∃₁∗-elim (binary P∗⊢ P'∗⊢)

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

  -->  -∗-intro :  P ∗ Q ⊢[ ι ] R →  Q ⊢[ ι ] P -∗ R
  -->  -∗-elim :  Q ⊢[ ι ] P -∗ R →  P ∗ Q ⊢[ ι ] R

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

  -->  |=>-mono :  P ⊢[ ι ] Q →  |=> P ⊢[ ι ] |=> Q

  -->  |=>-intro :  P ⊢[ ι ] |=> P

  -->  |=>-join :  |=> |=> P ⊢[ ι ] |=> P

  -- Eliminate |=> from the antecedent

  |=>-elim :  P ⊢[ ι ] |=> Q →  |=> P ⊢[ ι ] |=> Q
  |=>-elim P⊢|=>Q =  |=>-mono P⊢|=>Q » |=>-join

  -- ∃ -, can get outside |=>

  -->  |=>-∃₁-out :  |=> (∃₁ _ ∈ X , P) ⊢[ ι ] ∃₁ _ ∈ X , |=> P

  |=>-∃₀-out :  |=> (∃₀ _ ∈ X , P) ⊢[ ι ] ∃₀ _ ∈ X , |=> P
  |=>-∃₀-out =  |=>-∃₁-out

  -- ⌜ ⌝ ∧ can get outside |=>

  |=>-⌜⌝₁∧-out :  |=> (⌜ X ⌝₁ ∧ P) ⊢[ ι ] ⌜ X ⌝₁ ∧ |=> P
  |=>-⌜⌝₁∧-out =  |=>-mono ⌜⌝∧⇒∃₁ » |=>-∃₁-out » ∃₁⇒⌜⌝∧

  |=>-⌜⌝₀∧-out :  |=> (⌜ X ⌝₀ ∧ P) ⊢[ ι ] ⌜ X ⌝₀ ∧ |=> P
  |=>-⌜⌝₀∧-out =  |=>-⌜⌝₁∧-out

  -- ∗ can get inside |=>

  -->  |=>-eatˡ :  P ∗ |=> Q ⊢[ ι ] |=> (P ∗ Q)

  |=>-eatʳ :  |=> P ∗ Q ⊢[ ι ] |=> (P ∗ Q)
  |=>-eatʳ =  ∗-comm » |=>-eatˡ » |=>-mono ∗-comm

  -- Updates |=> can be merged

  |=>-merge :  |=> P ∗ |=> Q ⊢[ ι ] |=> (P ∗ Q)
  |=>-merge =  |=>-eatˡ » |=>-mono |=>-eatʳ » |=>-join

  ------------------------------------------------------------------------------
  -- On □

  -->  □-mono :  P ⊢[ ι ] Q →  □ P ⊢[ ι ] □ Q

  -->  □-elim :  □ P ⊢[ ι ] P

  -->  □-dup :  □ P ⊢[ ι ] □ □ P

  -- Introduce |=> to the succedent

  □-intro :  □ P ⊢[ ι ] Q →  □ P ⊢[ ι ] □ Q
  □-intro □P⊢Q =  □-dup » □-mono □P⊢Q

  -- The antecedent can be retained when the succedent is under □

  retain-□ :  P ⊢[ ι ] □ Q →  P ⊢[ ι ] □ Q ∗ P
  retain-□ P⊢Q =  ∧-intro P⊢Q ⊢-refl » □ˡ-∧⇒∗

  -- A proposition under □ can be duplicated

  dup-□ :  □ P ⊢[ ι ] □ P ∗ □ P
  dup-□ =  retain-□ ⊢-refl

  -- ∧ can turn into ∗ when one argument is under □

  -->  □ˡ-∧⇒∗ :  □ P ∧ Q ⊢[ ι ] □ P ∗ Q

  □ʳ-∧⇒∗ :  P ∧ □ Q ⊢[ ι ] P ∗ □ Q
  □ʳ-∧⇒∗ =  ∧-comm » □ˡ-∧⇒∗ » ∗-comm

  -- Under □, ∧ can turn into ∗

  in□-∧⇒∗ :  □ (P ∧ Q) ⊢[ ι ] □ (P ∗ Q)
  in□-∧⇒∗ =  □-intro $ dup-□ » ∗-mono (□-elim » ∧-elimˡ) (□-elim » ∧-elimʳ)

  -- P -∗ can turn into □ P →'

  -∗⇒□→ :  P -∗ Q ⊢[ ι ] □ P →' Q
  -∗⇒□→ =  →-intro $ □ˡ-∧⇒∗ » ∗-monoˡ □-elim » -∗-apply

  -- Under □, -∗ can turn into →'

  in□--∗⇒→ :  □ (P -∗ Q) ⊢[ ι ] □ (P →' Q)
  in□--∗⇒→ =  □-intro $ →-intro $ □ʳ-∧⇒∗ » -∗-elim □-elim

  -- ∀, ∧, ∃, ∨ and ∗ commute with □

  -->  □-∀₁-in :  ∀₁˙ (□_ ∘ P˙) ⊢[ ι ] □ ∀₁˙ P˙

  □-∀₀-in :  ∀₀˙ (□_ ∘ P˙) ⊢[ ι ] □ ∀₀˙ P˙
  □-∀₀-in =  □-∀₁-in

  □-∀₁-out :  □ ∀₁˙ P˙ ⊢[ ι ] ∀₁˙ (□_ ∘ P˙)
  □-∀₁-out =  ∀₁-intro $ □-mono ∘ ∀₁-elim

  □-∀₀-out :  □ ∀₀˙ P˙ ⊢[ ι ] ∀₀˙ (□_ ∘ P˙)
  □-∀₀-out =  □-∀₁-out

  □-∃₁-in :  ∃₁˙ (□_ ∘ P˙) ⊢[ ι ] □ ∃₁˙ P˙
  □-∃₁-in =  ∃₁-elim $ □-mono ∘ ∃₁-intro

  □-∃₀-in :  ∃₀˙ (□_ ∘ P˙) ⊢[ ι ] □ ∃₀˙ P˙
  □-∃₀-in =  □-∃₁-in

  -->  □-∃₁-out :  □ ∃₁˙ P˙ ⊢[ ι ] ∃₁˙ (□_ ∘ P˙)

  □-∃₀-out :  □ ∃₀˙ P˙ ⊢[ ι ] ∃₀˙ (□_ ∘ P˙)
  □-∃₀-out =  □-∃₁-out

  □-∧-in :  □ P ∧ □ Q ⊢[ ι ] □ (P ∧ Q)
  □-∧-in =  ∀₁-intro (binary ∧-elimˡ ∧-elimʳ) » □-∀₁-in

  □-∧-out :  □ (P ∧ Q) ⊢[ ι ] □ P ∧ □ Q
  □-∧-out =  ∧-intro (□-mono ∧-elimˡ) (□-mono ∧-elimʳ)

  □-∨-in :  □ P ∨ □ Q ⊢[ ι ] □ (P ∨ Q)
  □-∨-in =  ∨-elim (□-mono ∨-introˡ) (□-mono ∨-introʳ)

  □-∨-out :  □ (P ∨ Q) ⊢[ ι ] □ P ∨ □ Q
  □-∨-out =  □-∃₁-out » ∃₁-elim $ binary ∨-introˡ ∨-introʳ

  □-∗-in :  □ P ∗ □ Q ⊢[ ι ] □ (P ∗ Q)
  □-∗-in =  ∗⇒∧ » □-∧-in » in□-∧⇒∗

  □-∗-out :  □ (P ∗ Q) ⊢[ ι ] □ P ∗ □ Q
  □-∗-out =  □-mono ∗⇒∧ » □-∧-out » □ˡ-∧⇒∗

  -- □ ⊤' can be introduced and □ ⊥' can be eliminated

  □-⊤-intro :  P ⊢[ ι ] □ ⊤'
  □-⊤-intro =  ∀₁-intro absurd » □-∀₁-in

  □-⊥-elim :  □ ⊥' ⊢[ ι ]* Jr
  □-⊥-elim =  □-elim » ⊥-elim

  ------------------------------------------------------------------------------
  -- Derive Pers P

  -- For ∀/∃
  -- They are not instances, because unfortunately Agda can't search a
  -- universally quantified instance (∀ x → ...)

  ∀₁-Pers :  (∀ x → Pers (P˙ x)) →  Pers (∀₁˙ P˙)
  ∀₁-Pers ∀Pers .Pers-⇒□ =  ∀₁-mono (λ x → ∀Pers x .Pers-⇒□) » □-∀₁-in

  ∀₀-Pers :  (∀ x → Pers (P˙ x)) →  Pers (∀₀˙ P˙)
  ∀₀-Pers =  ∀₁-Pers ∘ _∘ ↓_

  ∃₁-Pers :  (∀ x → Pers (P˙ x)) →  Pers (∃₁˙ P˙)
  ∃₁-Pers ∀Pers .Pers-⇒□ =  ∃₁-mono (λ x → ∀Pers x .Pers-⇒□) » □-∃₁-in

  ∃₀-Pers :  (∀ x → Pers (P˙ x)) →  Pers (∃₀˙ P˙)
  ∃₀-Pers =  ∃₁-Pers ∘ _∘ ↓_

  instance

    -- For ∧/∨/⊤'/⊥'

    ∧-Pers :  {{Pers P}} →  {{Pers Q}} →  Pers (P ∧ Q)
    ∧-Pers =  ∀₁-Pers $ binary it it

    ∨-Pers :  {{Pers P}} →  {{Pers Q}} →  Pers (P ∨ Q)
    ∨-Pers =  ∃₁-Pers $ binary it it

    ⊤-Pers :  Pers ⊤'
    ⊤-Pers =  ∀₁-Pers absurd

    ⊥-Pers :  Pers ⊥'
    ⊥-Pers =  ∃₁-Pers absurd

    -- For ∗

    ∗-Pers :  {{Pers P}} →  {{Pers Q}} →  Pers (P ∗ Q)
    ∗-Pers .Pers-⇒□ =  ∗⇒∧ » Pers-⇒□ » in□-∧⇒∗

    -- For ⌜ ⌝

    ⌜⌝₁-Pers :  Pers ⌜ X ⌝₁
    ⌜⌝₁-Pers =  ∃₁-Pers $ λ _ → ⊤-Pers

    ⌜⌝₀-Pers :  Pers ⌜ X ⌝₀
    ⌜⌝₀-Pers =  ⌜⌝₁-Pers

    -- For □

    □-Pers :  Pers (□ P)
    □-Pers .Pers-⇒□ =  □-dup

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
  Pers--∗⇒→ =  -∗⇒□→ » →-monoˡ Pers-⇒□

  -- Introduce & eliminate ⌜ ⌝ ∗

  ⌜⌝₁∗-intro :  X →  P ⊢[ ι ] ⌜ X ⌝₁ ∗ P
  ⌜⌝₁∗-intro x =  ⌜⌝₁∧-intro x » Persˡ-∧⇒∗

  ⌜⌝₀∗-intro :  X →  P ⊢[ ι ] ⌜ X ⌝₀ ∗ P
  ⌜⌝₀∗-intro =  ⌜⌝₁∗-intro ∘ ↑_

  ⌜⌝₁∗-elim :  (X →  P ⊢[ ι ] Q) →  ⌜ X ⌝₁ ∗ P ⊢[ ι ] Q
  ⌜⌝₁∗-elim X→P⊢Q =  ∗⇒∧ » ⌜⌝₁∧-elim X→P⊢Q

  ⌜⌝₀∗-elim :  (X →  P ⊢[ ι ] Q) →  ⌜ X ⌝₀ ∗ P ⊢[ ι ] Q
  ⌜⌝₀∗-elim =  ⌜⌝₁∗-elim ∘ _∘ ↓_

  -- ⌜ ⌝ ∗ can get outside |=>

  |=>-⌜⌝₁∗-out :  |=> (⌜ X ⌝₁ ∗ P) ⊢[ ι ] ⌜ X ⌝₁ ∗ |=> P
  |=>-⌜⌝₁∗-out =  |=>-mono ∗⇒∧ » |=>-⌜⌝₁∧-out » Persˡ-∧⇒∗

  |=>-⌜⌝₀∗-out :  |=> (⌜ X ⌝₀ ∗ P) ⊢[ ι ] ⌜ X ⌝₀ ∗ |=> P
  |=>-⌜⌝₀∗-out =  |=>-⌜⌝₁∗-out

  ------------------------------------------------------------------------------
  -- On [∗]

  -- [∗] is monotone

  [∗]-mono :  All² _⊢[ ι ]_ Ps Qs →  [∗] Ps ⊢[ ι ] [∗] Qs
  [∗]-mono []ᴬ² =  ⊢-refl
  [∗]-mono (P⊢Q ∷ᴬ² Ps⊢Qs) =  ∗-mono P⊢Q $ [∗]-mono Ps⊢Qs

  -- ++ can get inside and outside [∗]

  [∗]-++-in :  [∗] Ps ∗ [∗] Qs ⊢[ ι ] [∗] (Ps ++ Qs)
  [∗]-++-in {[]} =  ∗-elimʳ
  [∗]-++-in {_ ∷ Ps'} =  ∗-assocˡ » ∗-monoʳ $ [∗]-++-in {Ps'}

  [∗]-++-out :  [∗] (Ps ++ Qs) ⊢[ ι ] [∗] Ps ∗ [∗] Qs
  [∗]-++-out {[]} =  ⊤∗-intro
  [∗]-++-out {_ ∷ Ps'} =  ∗-monoʳ ([∗]-++-out {Ps'}) » ∗-assocʳ
