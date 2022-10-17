--------------------------------------------------------------------------------
-- Proof rules on core connectives
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Core where

open import Base.Func using (_$_; _∘_; it)
open import Base.Few using (𝟚; 0₂; 1₂; ⊤; ⊥; binary; absurd)
open import Base.Size using (𝕊; Thunk; !)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_)
open import Base.Sum using (_⨿_; ĩ₀_; ĩ₁_; ⨿-case)
open import Base.List using (List; []; _∷_; _⧺_; All²; []ᴬ²; _∷ᴬ²_)
open import Syho.Logic.Prop using (Prop∞; ∀˙; ∃˙; ∀∈-syntax; ∃∈-syntax;
  ∀-syntax; ∃-syntax; _∧_; _∨_; ⊤'; ⊥'; ⌜_⌝∧_; ⌜_⌝→_; ⌜_⌝; _→'_; _∗_; _-∗_; ⤇_;
  □_; [∗])

-- Import and re-export
open import Syho.Logic.Judg public using (JudgRes; Pure; Judg; _⊢[_]*_;
  _⊢[<_]*_; _⊢[_]_; _⊢[<_]_; Pers; Pers-⇒□; ⊢-refl; _»_; ∀-intro; ∃-elim;
  ∀-elim; ∃-intro; choice; →-introˡ; →-elimˡ; ∗-monoˡ; ⊤∗-elim; ⊤∗-intro;
  ∗-comm; ∗-assocˡ; -∗-introˡ; -∗-elimˡ; ⤇-mono; ⤇-intro; ⤇-join; ⤇-eatˡ;
  ⤇-⌜⌝∧-out; □-mono; □-elim; □-dup; □ˡ-∧⇒∗; □-∀-in; □-∃-out)

private variable
  ι :  𝕊
  P P' Q Q' R R' S S' T T' U U' V V' :  Prop∞
  Jr :  JudgRes
  X Y :  Set₀
  x :  X
  Y˙ :  X → Set₀
  P˙ Q˙ :  X → Prop∞
  Ps Qs :  List Prop∞

abstract

  ------------------------------------------------------------------------------
  -- General

  -->  ⊢-refl :  P ⊢[ ι ] P

  -->  _»_ :  P ⊢[ ι ] Q →  Q ⊢[ ι ]* Jr →  P ⊢[ ι ]* Jr

  -- ⊢[ ]* into ⊢[< ]*

  ⇒< :  P ⊢[ ι ]* Jr →  P ⊢[< ι ]* Jr
  ⇒< P⊢Jr .! =  P⊢Jr

  ------------------------------------------------------------------------------
  -- On ∀/∃/∧/∨/⊤'/⊥'

  -- Introduce ∀/∧/⊤' & eliminate ∃/∨/⊥'

  -->  ∀-intro :  (∀ x →  P ⊢[ ι ] Q˙ x) →  P ⊢[ ι ] ∀˙ Q˙
  -->  ∃-elim :  (∀ x →  P˙ x ⊢[ ι ]* Jr) →  ∃˙ P˙ ⊢[ ι ]* Jr

  ∧-intro :  P ⊢[ ι ] Q →  P ⊢[ ι ] R →  P ⊢[ ι ] Q ∧ R
  ∧-intro P⊢Q P⊢R =  ∀-intro $ binary P⊢Q P⊢R

  ∨-elim :  P ⊢[ ι ]* Jr →  Q ⊢[ ι ]* Jr →  P ∨ Q ⊢[ ι ]* Jr
  ∨-elim P⊢*Jr Q⊢*Jr =  ∃-elim $ binary P⊢*Jr Q⊢*Jr

  ⊤-intro :  P ⊢[ ι ] ⊤'
  ⊤-intro =  ∀-intro absurd

  ⊥-elim :  ⊥' ⊢[ ι ]* Jr
  ⊥-elim =  ∃-elim absurd

  -- Eliminate ∀/∧/⊤' & introduce ∃/∨/⊥'

  -->  ∀-elim :  ∀ x →  ∀˙ P˙ ⊢[ ι ] P˙ x

  -->  ∃-intro :  ∀ x →  P˙ x ⊢[ ι ] ∃˙ P˙

  ∧-elimˡ :  P ∧ Q ⊢[ ι ] P
  ∧-elimˡ =  ∀-elim 0₂

  ∧-elimʳ :  P ∧ Q ⊢[ ι ] Q
  ∧-elimʳ =  ∀-elim 1₂

  ∨-introˡ :  P ⊢[ ι ] P ∨ Q
  ∨-introˡ =  ∃-intro 0₂

  ∨-introʳ :  Q ⊢[ ι ] P ∨ Q
  ∨-introʳ =  ∃-intro 1₂

  -- ∀/∃/∧/∨ is monotone

  ∀-mono :  (∀ x →  P˙ x ⊢[ ι ] Q˙ x) →  ∀˙ P˙ ⊢[ ι ] ∀˙ Q˙
  ∀-mono P˙⊢Q˙ =  ∀-intro λ x →  ∀-elim x » P˙⊢Q˙ x

  ∃-mono :  (∀ x →  P˙ x ⊢[ ι ] Q˙ x) →  ∃˙ P˙ ⊢[ ι ] ∃˙ Q˙
  ∃-mono P˙⊢Q˙ =  ∃-elim λ x →  P˙⊢Q˙ x » ∃-intro x

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

  -- ∧/∨ is unital with the unit ⊤'/⊥'

  ∧⊤-intro :  P ⊢[ ι ] P ∧ ⊤'
  ∧⊤-intro =  ∧-intro ⊢-refl ⊤-intro

  ⊤∧-intro :  P ⊢[ ι ] ⊤' ∧ P
  ⊤∧-intro =  ∧-intro ⊤-intro ⊢-refl

  ∨⊥-elim :  P ∨ ⊥' ⊢[ ι ] P
  ∨⊥-elim =  ∨-elim ⊢-refl ⊥-elim

  ⊥∨-elim :  ⊥' ∨ P ⊢[ ι ] P
  ⊥∨-elim =  ∨-elim ⊥-elim ⊢-refl

  -- Choice

  -->  choice :  ∀{P˙˙ : ∀(x : X) → Y˙ x → Prop∞} →
  -->    ∀' x , ∃ y , P˙˙ x y ⊢[ ι ] ∃ y˙ ∈ (∀ x → Y˙ x) , ∀' x , P˙˙ x (y˙ x)

  ------------------------------------------------------------------------------
  -- On →'

  -- Introduce →'

  -->  →-introˡ :  P ∧ Q ⊢[ ι ] R →  Q ⊢[ ι ] P →' R

  →-introʳ :  Q ∧ P ⊢[ ι ] R →  Q ⊢[ ι ] P →' R
  →-introʳ Q∧P⊢R =  →-introˡ $ ∧-comm » Q∧P⊢R

  →-const :  Q ⊢[ ι ] P →' Q
  →-const =  →-introˡ ∧-elimʳ

  -- Eliminate →'

  -->  →-elimˡ :  Q ⊢[ ι ] P →' R →  P ∧ Q ⊢[ ι ] R

  →-elimʳ :  Q ⊢[ ι ] P →' R →  Q ∧ P ⊢[ ι ] R
  →-elimʳ Q⊢P→R =  ∧-comm » →-elimˡ Q⊢P→R

  →-applyˡ :  P ∧ (P →' Q) ⊢[ ι ] Q
  →-applyˡ =  →-elimˡ ⊢-refl

  →-applyʳ :  (P →' Q) ∧ P ⊢[ ι ] Q
  →-applyʳ =  →-elimʳ ⊢-refl

  -- →' is monotone

  →-mono :  P ⊢[ ι ] Q →  R ⊢[ ι ] S →  Q →' R ⊢[ ι ] P →' S
  →-mono P⊢Q R⊢S =  →-introˡ $ ∧-monoˡ P⊢Q » →-applyˡ » R⊢S

  →-monoˡ :  P ⊢[ ι ] Q →  Q →' R ⊢[ ι ] P →' R
  →-monoˡ P⊢Q =  →-mono P⊢Q ⊢-refl

  →-monoʳ :  P ⊢[ ι ] Q →  R →' P ⊢[ ι ] R →' Q
  →-monoʳ P⊢Q =  →-mono ⊢-refl P⊢Q

  ------------------------------------------------------------------------------
  -- On ⌜⌝

  -- Introduce & eliminate ⌜⌝

  ⌜⌝-intro :  X →  P ⊢[ ι ] ⌜ X ⌝
  ⌜⌝-intro x =  ⊤-intro » ∃-intro x

  ⌜⌝-elim :  (X →  ⊤' ⊢[ ι ]* Jr) →  ⌜ X ⌝ ⊢[ ι ]* Jr
  ⌜⌝-elim X→⊤⊢P =  ∃-elim λ x →  X→⊤⊢P x

  -- ⌜⌝ is monotone

  ⌜⌝-mono :  (X → Y) →  ⌜ X ⌝ ⊢[ ι ] ⌜ Y ⌝
  ⌜⌝-mono f =  ⌜⌝-elim λ x →  ⌜⌝-intro $ f x

  -- ⌜ X ⌝ ∧ is the same with ⌜ X ⌝∧

  ⌜⌝'∧⇒⌜⌝∧ :  ⌜ X ⌝ ∧ P ⊢[ ι ] ⌜ X ⌝∧ P
  ⌜⌝'∧⇒⌜⌝∧ =  →-elimʳ $ ∃-elim λ x → →-introˡ $ ∧-elimˡ » ∃-intro x

  ⌜⌝∧⇒⌜⌝'∧ :  ⌜ X ⌝∧ P ⊢[ ι ] ⌜ X ⌝ ∧ P
  ⌜⌝∧⇒⌜⌝'∧ =  ∃-elim λ x → ∧-intro (⌜⌝-intro x) ⊢-refl

  -- ⌜ X ⌝ →' is the same with ⌜ X ⌝→

  ⌜⌝'→⇒⌜⌝→ :  ⌜ X ⌝ →' P ⊢[ ι ] ⌜ X ⌝→ P
  ⌜⌝'→⇒⌜⌝→ =  ∀-intro λ x → ∧-intro (⌜⌝-intro x) ⊢-refl » →-applyˡ

  ⌜⌝→⇒⌜⌝'→ :  ⌜ X ⌝→ P ⊢[ ι ] ⌜ X ⌝ →' P
  ⌜⌝→⇒⌜⌝'→ =  →-introˡ $ ⌜⌝'∧⇒⌜⌝∧ » ∃-elim λ x → ∀-elim x

  -- Turn P ⊢ ⌜ X ⌝ into P ⊢ ⌜ X ⌝∧ P

  retain-⌜⌝ :  P ⊢[ ι ] ⌜ X ⌝ →  P ⊢[ ι ] ⌜ X ⌝∧ P
  retain-⌜⌝ P⊢X =  ∧-intro P⊢X ⊢-refl » ⌜⌝'∧⇒⌜⌝∧

  -- ⌜⌝ commutes with ∀/∃/∧/∨/⊤'/⊥'/→

  ⌜⌝-∀-in :  ∀' x , ⌜ Y˙ x ⌝ ⊢[ ι ] ⌜ (∀ x → Y˙ x) ⌝
  ⌜⌝-∀-in =  choice » ∃-mono λ _ → ⊤-intro

  ⌜⌝-∀-out :  ⌜ (∀ x → Y˙ x) ⌝ ⊢[ ι ] ∀' x , ⌜ Y˙ x ⌝
  ⌜⌝-∀-out =  ∀-intro λ x →  ⌜⌝-elim λ f →  ⌜⌝-intro $ f x

  ⌜⌝-∃-in :  ∃ x , ⌜ Y˙ x ⌝ ⊢[ ι ] ⌜ ∑ x , Y˙ x ⌝
  ⌜⌝-∃-in =  ∃-elim λ x →  ⌜⌝-mono λ y →  x , y

  ⌜⌝-∃-out :  ⌜ ∑ x , Y˙ x ⌝ ⊢[ ι ] ∃ x , ⌜ Y˙ x ⌝
  ⌜⌝-∃-out =  ⌜⌝-elim λ (x , y) →  ⌜⌝-intro y » ∃-intro x

  ⌜⌝-∧-in :  ⌜ X ⌝ ∧ ⌜ Y ⌝ ⊢[ ι ] ⌜ X × Y ⌝
  ⌜⌝-∧-in =  ⌜⌝'∧⇒⌜⌝∧ » ∃-elim λ x → ⌜⌝-mono λ y → x , y

  ⌜⌝-∧-out :  ⌜ X × Y ⌝ ⊢[ ι ] ⌜ X ⌝ ∧ ⌜ Y ⌝
  ⌜⌝-∧-out =  ⌜⌝-elim λ (x , y) →  ∧-intro (⌜⌝-intro x) (⌜⌝-intro y)

  ⌜⌝-∨-in :  ⌜ X ⌝ ∨ ⌜ Y ⌝ ⊢[ ι ] ⌜ X ⨿ Y ⌝
  ⌜⌝-∨-in =  ∨-elim (⌜⌝-mono ĩ₀_) (⌜⌝-mono ĩ₁_)

  ⌜⌝-∨-out :  ⌜ X ⨿ Y ⌝ ⊢[ ι ] ⌜ X ⌝ ∨ ⌜ Y ⌝
  ⌜⌝-∨-out =  ⌜⌝-elim $ ⨿-case
    (λ x → ⌜⌝-intro x » ∨-introˡ) (λ y → ⌜⌝-intro y » ∨-introʳ)

  ⌜⊤⌝-intro :  P ⊢[ ι ] ⌜ ⊤ ⌝
  ⌜⊤⌝-intro =  ⌜⌝-intro _

  ⌜⊥⌝-elim :  ⌜ ⊥ ⌝ ⊢[ ι ]* Jr
  ⌜⊥⌝-elim =  ⌜⌝-elim absurd

  ⌜⌝-→-in :  ⌜ X ⌝ →' ⌜ Y ⌝ ⊢[ ι ] ⌜ (X → Y) ⌝
  ⌜⌝-→-in =  ⌜⌝'→⇒⌜⌝→ » ⌜⌝-∀-in

  ⌜⌝-→-out :  ⌜ (X → Y) ⌝ ⊢[ ι ] ⌜ X ⌝ →' ⌜ Y ⌝
  ⌜⌝-→-out =  →-introˡ $ ⌜⌝'∧⇒⌜⌝∧ » ∃-elim λ x → ⌜⌝-mono λ f → f x

  ------------------------------------------------------------------------------
  -- On ∗

  -->  ∗-comm :  P ∗ Q ⊢[ ι ] Q ∗ P

  -- ∗ is monotone

  -->  ∗-monoˡ :  P ⊢[ ι ] Q →  P ∗ R ⊢[ ι ] Q ∗ R

  ∗-monoʳ :  P ⊢[ ι ] Q →  R ∗ P ⊢[ ι ] R ∗ Q
  ∗-monoʳ P⊢Q =  ∗-comm » ∗-monoˡ P⊢Q » ∗-comm

  ∗-mono :  P ⊢[ ι ] Q →  R ⊢[ ι ] S →  P ∗ R ⊢[ ι ] Q ∗ S
  ∗-mono P⊢Q R⊢S =  ∗-monoˡ P⊢Q » ∗-monoʳ R⊢S

  -- Eliminate ∗

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

  -- - ∗ / ∗ - is commutative

  ?∗-comm :  P ∗ Q ∗ R ⊢[ ι ] Q ∗ P ∗ R
  ?∗-comm =  ∗-assocʳ » ∗-monoˡ ∗-comm » ∗-assocˡ

  ∗?-comm :  (P ∗ Q) ∗ R ⊢[ ι ] (P ∗ R) ∗ Q
  ∗?-comm =  ∗-assocˡ » ∗-monoʳ ∗-comm » ∗-assocʳ

  -- Turn ∗ into ∧

  ∗⇒∧ :  P ∗ Q ⊢[ ι ] P ∧ Q
  ∗⇒∧ =  ∧-intro ∗-elimˡ ∗-elimʳ

  -- Let ∃ go outside ∗

  ∗∃-out :  P ∗ ∃˙ Q˙ ⊢[ ι ] ∃ x , P ∗ Q˙ x
  ∗∃-out =  -∗-elimˡ $ ∃-elim $ -∗-introˡ ∘ ∃-intro

  ∃∗-out :  ∃˙ P˙ ∗ Q ⊢[ ι ] ∃ x , P˙ x ∗ Q
  ∃∗-out =  ∗-comm » ∗∃-out » ∃-mono λ _ → ∗-comm

  -- Let ∨ go outside ∗

  ∨∗-out :  (P ∨ Q) ∗ R ⊢[ ι ] (P ∗ R) ∨ (Q ∗ R)
  ∨∗-out =  ∃∗-out » ∃-mono $ binary ⊢-refl ⊢-refl

  ∗∨-out :  P ∗ (Q ∨ R) ⊢[ ι ] (P ∗ Q) ∨ (P ∗ R)
  ∗∨-out =  ∗-comm » ∨∗-out » ∨-mono ∗-comm ∗-comm

  -- Eliminate ∃/∨ under ∗

  ∃∗-elim :  (∀ x → P˙ x ∗ Q ⊢[ ι ]* Jr) →  ∃˙ P˙ ∗ Q ⊢[ ι ]* Jr
  ∃∗-elim Px∗⊢ =  ∃∗-out » ∃-elim Px∗⊢

  ∗∃-elim :  (∀ x → P ∗ Q˙ x ⊢[ ι ]* Jr) →  P ∗ ∃˙ Q˙ ⊢[ ι ]* Jr
  ∗∃-elim ∗Qx⊢ =  ∗∃-out » ∃-elim ∗Qx⊢

  ∨∗-elim :  P ∗ R ⊢[ ι ]* Jr →  Q ∗ R ⊢[ ι ]* Jr →  (P ∨ Q) ∗ R ⊢[ ι ]* Jr
  ∨∗-elim P∗⊢ Q∗⊢ =  ∃∗-elim $ binary P∗⊢ Q∗⊢

  ∗∨-elim :  P ∗ Q ⊢[ ι ]* Jr →  P ∗ R ⊢[ ι ]* Jr →  P ∗ (Q ∨ R) ⊢[ ι ]* Jr
  ∗∨-elim ∗Q⊢ ∗R⊢ =  ∗∃-elim $ binary ∗Q⊢ ∗R⊢

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

  ∗-pullʳ² :  P ∗ Q ∗ R ⊢[ ι ] R ∗ P ∗ Q
  ∗-pullʳ² =  ∗-monoʳ ∗-comm » ?∗-comm

  ∗-pullʳ²ˡ :  P ∗ Q ∗ R ∗ S ⊢[ ι ] R ∗ P ∗ Q ∗ S
  ∗-pullʳ²ˡ =  ∗-monoʳ ?∗-comm » ?∗-comm

  ∗-pullʳ³ :  P ∗ Q ∗ R ∗ S ⊢[ ι ] S ∗ P ∗ Q ∗ R
  ∗-pullʳ³ =  ∗-monoʳ ∗-pullʳ² » ?∗-comm

  ∗-pullʳ³ˡ :  P ∗ Q ∗ R ∗ S ∗ T ⊢[ ι ] S ∗ P ∗ Q ∗ R ∗ T
  ∗-pullʳ³ˡ =  ∗-monoʳ ∗-pullʳ²ˡ » ?∗-comm

  ∗-pullʳ⁴ :  P ∗ Q ∗ R ∗ S ∗ T ⊢[ ι ] T ∗ P ∗ Q ∗ R ∗ S
  ∗-pullʳ⁴ =  ∗-monoʳ ∗-pullʳ³ » ?∗-comm

  ∗-pullʳ⁴ˡ :  P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ ι ] T ∗ P ∗ Q ∗ R ∗ S ∗ U
  ∗-pullʳ⁴ˡ =  ∗-monoʳ ∗-pullʳ³ˡ » ?∗-comm

  ∗-pullʳ⁵ :  P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ ι ] U ∗ P ∗ Q ∗ R ∗ S ∗ T
  ∗-pullʳ⁵ =  ∗-monoʳ ∗-pullʳ⁴ » ?∗-comm

  ∗-pullʳ⁵ˡ :  P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ ι ] U ∗ P ∗ Q ∗ R ∗ S ∗ T ∗ V
  ∗-pullʳ⁵ˡ =  ∗-monoʳ ∗-pullʳ⁴ˡ » ?∗-comm

  ∗-pullʳ⁶ :  P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ ι ] V ∗ P ∗ Q ∗ R ∗ S ∗ T ∗ U
  ∗-pullʳ⁶ =  ∗-monoʳ ∗-pullʳ⁵ » ?∗-comm

  -- Move the head separating conjunct to somewhere deeper

  ∗-pushʳ² :  P ∗ Q ∗ R ⊢[ ι ] Q ∗ R ∗ P
  ∗-pushʳ² =  ?∗-comm » ∗-monoʳ ∗-comm

  ∗-pushʳ²ˡ :  P ∗ Q ∗ R ∗ S ⊢[ ι ] Q ∗ R ∗ P ∗ S
  ∗-pushʳ²ˡ =  ?∗-comm » ∗-monoʳ ?∗-comm

  ∗-pushʳ³ :  P ∗ Q ∗ R ∗ S ⊢[ ι ] Q ∗ R ∗ S ∗ P
  ∗-pushʳ³ =  ?∗-comm » ∗-monoʳ ∗-pushʳ²

  ∗-pushʳ³ˡ :  P ∗ Q ∗ R ∗ S ∗ T ⊢[ ι ] Q ∗ R ∗ S ∗ P ∗ T
  ∗-pushʳ³ˡ =  ?∗-comm » ∗-monoʳ ∗-pushʳ²ˡ

  ∗-pushʳ⁴ :  P ∗ Q ∗ R ∗ S ∗ T ⊢[ ι ] Q ∗ R ∗ S ∗ T ∗ P
  ∗-pushʳ⁴ =  ?∗-comm » ∗-monoʳ ∗-pushʳ³

  ∗-pushʳ⁴ˡ :  P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ ι ] Q ∗ R ∗ S ∗ T ∗ P ∗ U
  ∗-pushʳ⁴ˡ =  ?∗-comm » ∗-monoʳ ∗-pushʳ³ˡ

  ∗-pushʳ⁵ :  P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ ι ] Q ∗ R ∗ S ∗ T ∗ U ∗ P
  ∗-pushʳ⁵ =  ?∗-comm » ∗-monoʳ ∗-pushʳ⁴

  ∗-pushʳ⁵ˡ :  P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ ι ] Q ∗ R ∗ S ∗ T ∗ U ∗ P ∗ V
  ∗-pushʳ⁵ˡ =  ?∗-comm » ∗-monoʳ ∗-pushʳ⁴ˡ

  ∗-pushʳ⁶ :  P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ ι ] Q ∗ R ∗ S ∗ T ∗ U ∗ V ∗ P
  ∗-pushʳ⁶ =  ?∗-comm » ∗-monoʳ ∗-pushʳ⁵

  ------------------------------------------------------------------------------
  -- On -∗

  -- Introduce -∗

  -->  -∗-introˡ :  P ∗ Q ⊢[ ι ] R →  Q ⊢[ ι ] P -∗ R

  -∗-introʳ :  Q ∗ P ⊢[ ι ] R →  Q ⊢[ ι ] P -∗ R
  -∗-introʳ Q∗P⊢R =  -∗-introˡ $ ∗-comm » Q∗P⊢R

  -∗-const :  Q ⊢[ ι ] P -∗ Q
  -∗-const =  -∗-introˡ ∗-elimʳ

  -- Eliminate -∗

  -->  -∗-elimˡ :  Q ⊢[ ι ] P -∗ R →  P ∗ Q ⊢[ ι ] R

  -∗-elimʳ :  Q ⊢[ ι ] P -∗ R →  Q ∗ P ⊢[ ι ] R
  -∗-elimʳ Q⊢P-∗R =  ∗-comm » -∗-elimˡ Q⊢P-∗R

  -∗-applyˡ :  P ∗ (P -∗ Q) ⊢[ ι ] Q
  -∗-applyˡ =  -∗-elimˡ ⊢-refl

  -∗-applyʳ :  (P -∗ Q) ∗ P ⊢[ ι ] Q
  -∗-applyʳ =  -∗-elimʳ ⊢-refl

  -- -∗ is monotone

  -∗-mono :  P ⊢[ ι ] Q →  R ⊢[ ι ] S →  Q -∗ R ⊢[ ι ] P -∗ S
  -∗-mono P⊢Q R⊢S =  -∗-introˡ $ ∗-monoˡ P⊢Q » -∗-applyˡ » R⊢S

  -∗-monoˡ :  P ⊢[ ι ] Q →  Q -∗ R ⊢[ ι ] P -∗ R
  -∗-monoˡ P⊢Q =  -∗-mono P⊢Q ⊢-refl

  -∗-monoʳ :  P ⊢[ ι ] Q →  R -∗ P ⊢[ ι ] R -∗ Q
  -∗-monoʳ P⊢Q =  -∗-mono ⊢-refl P⊢Q

  -- Turn →' into -∗

  →⇒-∗ :  P →' Q ⊢[ ι ] P -∗ Q
  →⇒-∗ =  -∗-introˡ $ ∗⇒∧ » →-elimˡ ⊢-refl

  -- Apply the head magic wand to the succedent

  -∗∗-apply :  Q ⊢[ ι ] P →  (P -∗ P') ∗ Q ⊢[ ι ] P'
  -∗∗-apply Q⊢P =  ∗-monoˡ (-∗-monoˡ Q⊢P) » -∗-applyʳ

  -- Let -∗ eat a proposition

  -∗-eatʳ :  (P -∗ Q) ∗ R ⊢[ ι ] P -∗ Q ∗ R
  -∗-eatʳ =  -∗-introˡ $ ∗-assocʳ » ∗-monoˡ -∗-applyˡ

  -∗-eatˡ :  R ∗ (P -∗ Q) ⊢[ ι ] P -∗ R ∗ Q
  -∗-eatˡ =  ∗-comm » -∗-eatʳ » -∗-monoʳ ∗-comm

  ------------------------------------------------------------------------------
  -- On ⤇

  -->  ⤇-mono :  P ⊢[ ι ] Q →  ⤇ P ⊢[ ι ] ⤇ Q

  -->  ⤇-intro :  P ⊢[ ι ] ⤇ P

  -->  ⤇-join :  ⤇ ⤇ P ⊢[ ι ] ⤇ P

  -->  ⤇-⌜⌝∧-out :  ⤇ (⌜ X ⌝∧ P) ⊢[ ι ] ⌜ X ⌝∧ ⤇ P

  -- Eliminate ⤇ from the antecedent

  ⤇-elim :  P ⊢[ ι ] ⤇ Q →  ⤇ P ⊢[ ι ] ⤇ Q
  ⤇-elim P⊢⤇Q =  ⤇-mono P⊢⤇Q » ⤇-join

  -- Let ⤇ eat a proposition

  -->  ⤇-eatˡ :  Q ∗ (⤇ P) ⊢[ ι ] ⤇ Q ∗ P

  ⤇-eatʳ :  (⤇ P) ∗ Q ⊢[ ι ] ⤇ P ∗ Q
  ⤇-eatʳ =  ∗-comm » ⤇-eatˡ » ⤇-mono ∗-comm

  -- Merge ⤇

  ⤇-merge :  (⤇ P) ∗ (⤇ Q) ⊢[ ι ] ⤇ P ∗ Q
  ⤇-merge =  ⤇-eatˡ » ⤇-mono ⤇-eatʳ » ⤇-join

  ------------------------------------------------------------------------------
  -- On □

  -->  □-mono :  P ⊢[ ι ] Q →  □ P ⊢[ ι ] □ Q

  -->  □-elim :  □ P ⊢[ ι ] P

  -->  □-dup :  □ P ⊢[ ι ] □ □ P

  -- Introduce □ to the succedent

  □-intro-□ :  □ P ⊢[ ι ] Q →  □ P ⊢[ ι ] □ Q
  □-intro-□ □P⊢Q =  □-dup » □-mono □P⊢Q

  -- Retain the antecedent when the succedent is under □

  retain-□ :  P ⊢[ ι ] □ Q →  P ⊢[ ι ] □ Q ∗ P
  retain-□ P⊢Q =  ∧-intro P⊢Q ⊢-refl » □ˡ-∧⇒∗

  -- Duplicate a proposition under □

  dup-□ :  □ P ⊢[ ι ] □ P ∗ □ P
  dup-□ =  retain-□ ⊢-refl

  -- Turn ∧ into ∗ when one argument is under □

  -->  □ˡ-∧⇒∗ :  □ P ∧ Q ⊢[ ι ] □ P ∗ Q

  □ʳ-∧⇒∗ :  P ∧ □ Q ⊢[ ι ] P ∗ □ Q
  □ʳ-∧⇒∗ =  ∧-comm » □ˡ-∧⇒∗ » ∗-comm

  -- Turn ∧ into ∗ under □

  in□-∧⇒∗ :  □ (P ∧ Q) ⊢[ ι ] □ (P ∗ Q)
  in□-∧⇒∗ =  □-intro-□ $ dup-□ » ∗-mono (□-elim » ∧-elimˡ) (□-elim » ∧-elimʳ)

  -- Turn P -∗ into □ P →'

  -∗⇒□→ :  P -∗ Q ⊢[ ι ] □ P →' Q
  -∗⇒□→ =  →-introˡ $ □ˡ-∧⇒∗ » ∗-monoˡ □-elim » -∗-applyˡ

  -- Turn -∗ into →' under □

  in□--∗⇒→ :  □ (P -∗ Q) ⊢[ ι ] □ (P →' Q)
  in□--∗⇒→ =  □-intro-□ $ →-introˡ $ □ʳ-∧⇒∗ » -∗-elimˡ □-elim

  -- ∀, ∧, ∃, ∨ and ∗ commute with □

  -->  □-∀-in :  ∀˙ (□_ ∘ P˙) ⊢[ ι ] □ ∀˙ P˙

  □-∀-out :  □ ∀˙ P˙ ⊢[ ι ] ∀˙ (□_ ∘ P˙)
  □-∀-out =  ∀-intro $ □-mono ∘ ∀-elim

  □-∃-in :  ∃˙ (□_ ∘ P˙) ⊢[ ι ] □ ∃˙ P˙
  □-∃-in =  ∃-elim $ □-mono ∘ ∃-intro

  -->  □-∃-out :  □ ∃˙ P˙ ⊢[ ι ] ∃˙ (□_ ∘ P˙)

  □-∧-in :  □ P ∧ □ Q ⊢[ ι ] □ (P ∧ Q)
  □-∧-in =  ∀-intro (binary ∧-elimˡ ∧-elimʳ) » □-∀-in

  □-∧-out :  □ (P ∧ Q) ⊢[ ι ] □ P ∧ □ Q
  □-∧-out =  ∧-intro (□-mono ∧-elimˡ) (□-mono ∧-elimʳ)

  □-∨-in :  □ P ∨ □ Q ⊢[ ι ] □ (P ∨ Q)
  □-∨-in =  ∨-elim (□-mono ∨-introˡ) (□-mono ∨-introʳ)

  □-∨-out :  □ (P ∨ Q) ⊢[ ι ] □ P ∨ □ Q
  □-∨-out =  □-∃-out » ∃-elim $ binary ∨-introˡ ∨-introʳ

  □-∗-in :  □ P ∗ □ Q ⊢[ ι ] □ (P ∗ Q)
  □-∗-in =  ∗⇒∧ » □-∧-in » in□-∧⇒∗

  □-∗-out :  □ (P ∗ Q) ⊢[ ι ] □ P ∗ □ Q
  □-∗-out =  □-mono ∗⇒∧ » □-∧-out » □ˡ-∧⇒∗

  -- Introduce □ ⊤' / Eliminate □ ⊥'

  □-⊤-intro :  P ⊢[ ι ] □ ⊤'
  □-⊤-intro =  ∀-intro absurd » □-∀-in

  □-⊥-elim :  □ ⊥' ⊢[ ι ]* Jr
  □-⊥-elim =  □-elim » ⊥-elim

  ------------------------------------------------------------------------------
  -- Derive Pers P

  -- For ∀/∃
  -- They are not instances, because unfortunately Agda can't search a
  -- universally quantified instance (∀ x → …)

  ∀-Pers :  (∀ x → Pers $ P˙ x) →  Pers $ ∀˙ P˙
  ∀-Pers ∀Pers .Pers-⇒□ =  ∀-mono (λ x → ∀Pers x .Pers-⇒□) » □-∀-in

  ∃-Pers :  (∀ x → Pers $ P˙ x) →  Pers $ ∃˙ P˙
  ∃-Pers ∀Pers .Pers-⇒□ =  ∃-mono (λ x → ∀Pers x .Pers-⇒□) » □-∃-in

  instance

    -- For ∧/∨/⊤'/⊥'

    ∧-Pers :  {{Pers P}} →  {{Pers Q}} →  Pers $ P ∧ Q
    ∧-Pers =  ∀-Pers $ binary it it

    ∨-Pers :  {{Pers P}} →  {{Pers Q}} →  Pers $ P ∨ Q
    ∨-Pers =  ∃-Pers $ binary it it

    ⊤-Pers :  Pers ⊤'
    ⊤-Pers =  ∀-Pers absurd

    ⊥-Pers :  Pers ⊥'
    ⊥-Pers =  ∃-Pers absurd

    -- For ∗

    ∗-Pers :  {{Pers P}} →  {{Pers Q}} →  Pers $ P ∗ Q
    ∗-Pers .Pers-⇒□ =  ∗⇒∧ » Pers-⇒□ » in□-∧⇒∗

    -- For ⌜ ⌝ᵒ

    ⌜⌝-Pers :  Pers ⌜ X ⌝
    ⌜⌝-Pers =  ∃-Pers λ _ → ⊤-Pers

    -- For □

    □-Pers :  Pers $ □ P
    □-Pers .Pers-⇒□ =  □-dup

  ------------------------------------------------------------------------------
  -- Use Pers P

  -- Introduce □ to the succedent

  □-intro-Pers :  {{Pers P}} →  P ⊢[ ι ] Q →  P ⊢[ ι ] □ Q
  □-intro-Pers P⊢Q =  Pers-⇒□ » □-mono P⊢Q

  -- Turn ∧ into ∗ when one argument is persistent

  Persˡ-∧⇒∗ :  {{Pers P}} →  P ∧ Q ⊢[ ι ] P ∗ Q
  Persˡ-∧⇒∗ =  ∧-monoˡ Pers-⇒□ » □ˡ-∧⇒∗ » ∗-monoˡ □-elim

  Persʳ-∧⇒∗ :  {{Pers Q}} →  P ∧ Q ⊢[ ι ] P ∗ Q
  Persʳ-∧⇒∗ =  ∧-comm » Persˡ-∧⇒∗ » ∗-comm

  -- Retain the antecedent when the succedent is persistent

  retain-Pers :  {{Pers Q}} →  P ⊢[ ι ] Q →  P ⊢[ ι ] Q ∗ P
  retain-Pers P⊢Q =  retain-□ (P⊢Q » Pers-⇒□) » ∗-monoˡ □-elim

  -- Duplicate a persistent proposition

  dup-Pers :  {{Pers P}} →  P ⊢[ ι ] P ∗ P
  dup-Pers =  retain-Pers ⊢-refl

  -- Duplicate a persistent separting conjunct

  dup-Pers-∗ :  {{Pers P}} →  P ∗ Q ⊢[ ι ] P ∗ P ∗ Q
  dup-Pers-∗ =  ∗-monoˡ dup-Pers » ∗-assocˡ

  -- Turn -∗ into →' when the left-hand side is persistent

  Pers--∗⇒→ :  {{Pers P}} →  P -∗ Q ⊢[ ι ] P →' Q
  Pers--∗⇒→ =  -∗⇒□→ » →-monoˡ Pers-⇒□

  -- Let □ eat persistent propositions

  □-eatˡ-Pers :  {{Pers Q}} →  Q ∗ □ P ⊢[ ι ] □ (Q ∗ P)
  □-eatˡ-Pers =  ∗-monoˡ Pers-⇒□ » □-∗-in

  □-eatʳ-Pers :  {{Pers Q}} →  □ P ∗ Q ⊢[ ι ] □ (P ∗ Q)
  □-eatʳ-Pers =  ∗-monoʳ Pers-⇒□ » □-∗-in

  -- ⌜ ⌝ ∗ is the same thing with ⌜ ⌝∧

  ⌜⌝∗⇒⌜⌝∧ :  ⌜ X ⌝ ∗ P ⊢[ ι ] ⌜ X ⌝∧ P
  ⌜⌝∗⇒⌜⌝∧ =  ∗⇒∧ » ⌜⌝'∧⇒⌜⌝∧

  ⌜⌝∧⇒⌜⌝∗ :  ⌜ X ⌝∧ P ⊢[ ι ] ⌜ X ⌝ ∗ P
  ⌜⌝∧⇒⌜⌝∗ =  ⌜⌝∧⇒⌜⌝'∧ » Persˡ-∧⇒∗

  ------------------------------------------------------------------------------
  -- On [∗]

  -- [∗] is monotone

  [∗]-mono :  All² _⊢[ ι ]_ Ps Qs →  [∗] Ps ⊢[ ι ] [∗] Qs
  [∗]-mono []ᴬ² =  ⊢-refl
  [∗]-mono (P⊢Q ∷ᴬ² Ps⊢Qs) =  ∗-mono P⊢Q $ [∗]-mono Ps⊢Qs

  -- Let ⧺ go inside and outside [∗]

  [∗]-⧺-in :  [∗] Ps ∗ [∗] Qs ⊢[ ι ] [∗] (Ps ⧺ Qs)
  [∗]-⧺-in {[]} =  ∗-elimʳ
  [∗]-⧺-in {_ ∷ Ps'} =  ∗-assocˡ » ∗-monoʳ $ [∗]-⧺-in {Ps'}

  [∗]-⧺-out :  [∗] (Ps ⧺ Qs) ⊢[ ι ] [∗] Ps ∗ [∗] Qs
  [∗]-⧺-out {[]} =  ⊤∗-intro
  [∗]-⧺-out {_ ∷ Ps'} =  ∗-monoʳ ([∗]-⧺-out {Ps'}) » ∗-assocʳ
