--------------------------------------------------------------------------------
-- Judgment in Shog
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Logic.Judg (ℓ : Level) where

open import Base.Level using (^_; ○; ↑_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk; !)
open import Base.Func using (_∘_; _$_)
open import Base.Bool using (Bool)
open import Base.List using (List)
open import Base.Prod using (_,_)
open import Base.Sum using (inj₀; inj₁)
open import Shog.Logic.Prop ℓ using (Prop'; Prop˂; ∀˙; ∃˙; ∀-syntax; ∃-syntax;
  ∃∈-syntax; _∧_; ⊤'; _→'_; _∗_; _-∗_; |=>_; □_; [∗]_; [∗]-map; [∗∈]-syntax;
  saveˣ; save□; Basic)
open import Shog.Lang.Expr ℓ using (Type; Expr; ▶_; Val; Val⇒Expr)
open import Shog.Lang.Reduce ℓ using (▶ᴿ_; ndᴿ; _◁ᴿ_; ★ᴿ_; _←ᴿ_; allocᴿ; freeᴿ;
  Val/Ctxred; val/ctxred; Ktx; _•←_)

--------------------------------------------------------------------------------
-- WpK: Weakest precondion kind

data  WpK :  Set ○  where
  -- Partial/total
  par tot :  WpK

--------------------------------------------------------------------------------
-- JudgRes: Result of a judgment

private variable
  T U :  Type

infix 3 |=>>_

data  JudgRes :  Set (^ ℓ)  where
  -- Just a proposition
  Pure :  Prop' ∞ →  JudgRes
  -- Under the super update
  |=>>_ :  Prop' ∞ →  JudgRes
  -- Weakest precondion, over Val/Ctxred
  Wp' :  WpK →  Val/Ctxred T →  (Val T → Prop' ∞) →  JudgRes

--------------------------------------------------------------------------------
-- P ⊢[ ι ]* Jr :  Judgment

infix 2 _⊢[_]*_ _⊢[_]_ _⊢[<_]_ _⊢[_]=>>_ _⊢[_]'⟨_⟩[_]_ _⊢[_]'⟨_⟩_ _⊢[_]'⟨_⟩ᵀ_
  _⊢[_]⟨_⟩[_]_ _⊢[_]⟨_⟩_ _⊢[<_]⟨_⟩_ _⊢[_]⟨_⟩ᵀ_

-- Declaring _⊢[_]*_
data  _⊢[_]*_ :  Prop' ∞ →  Size →  JudgRes →  Set (^ ℓ)

-- ⊢[ ] : Pure sequent
_⊢[_]_ :  Prop' ∞ →  Size →  Prop' ∞ →  Set (^ ℓ)
P ⊢[ ι ] Q =  P ⊢[ ι ]* Pure Q

-- ⊢[< ] : Pure sequent under thunk
_⊢[<_]_ :  Prop' ∞ →  Size →  Prop' ∞ →  Set (^ ℓ)
P ⊢[< ι ] Q =  Thunk (P ⊢[_] Q) ι

-- ⊢[ ]=>> : Super update
_⊢[_]=>>_ :  Prop' ∞ →  Size →  Prop' ∞ →  Set (^ ℓ)
P ⊢[ ι ]=>> Q =  P ⊢[ ι ]* |=>> Q

-- ⊢[ ]'⟨ ⟩[ ] : Hoare-triple, over Val/Ctxred

_⊢[_]'⟨_⟩[_]_ :
  Prop' ∞ →  Size →  Val/Ctxred T →  WpK →  (Val T → Prop' ∞) →  Set (^ ℓ)
P ⊢[ ι ]'⟨ vc ⟩[ κ ] Qᵛ =  P ⊢[ ι ]* Wp' κ vc Qᵛ

_⊢[_]'⟨_⟩_ _⊢[_]'⟨_⟩ᵀ_ :
  Prop' ∞ →  Size →  Val/Ctxred T →  (Val T → Prop' ∞) →  Set (^ ℓ)
P ⊢[ ι ]'⟨ vc ⟩ Qᵛ =  P ⊢[ ι ]'⟨ vc ⟩[ par ] Qᵛ
P ⊢[ ι ]'⟨ vc ⟩ᵀ Qᵛ =  P ⊢[ ι ]'⟨ vc ⟩[ tot ] Qᵛ

-- ⊢[ ]⟨ ⟩[ ] : Hoare-triple, over Expr
_⊢[_]⟨_⟩[_]_ :
  Prop' ∞ →  Size →  Expr ∞ T →  WpK →  (Val T → Prop' ∞) →  Set (^ ℓ)
P ⊢[ ι ]⟨ e ⟩[ κ ] Qᵛ =  P ⊢[ ι ]'⟨ val/ctxred e ⟩[ κ ] Qᵛ

_⊢[_]⟨_⟩_ _⊢[<_]⟨_⟩_ _⊢[_]⟨_⟩ᵀ_ :
  Prop' ∞ →  Size →  Expr ∞ T →  (Val T → Prop' ∞) →  Set (^ ℓ)
P ⊢[ ι ]⟨ e ⟩ Qᵛ =  P ⊢[ ι ]⟨ e ⟩[ par ] Qᵛ
P ⊢[< ι ]⟨ e ⟩ Qᵛ =  Thunk (P ⊢[_]⟨ e ⟩[ par ] Qᵛ) ι
P ⊢[ ι ]⟨ e ⟩ᵀ Qᵛ =  P ⊢[ ι ]⟨ e ⟩[ tot ] Qᵛ

private variable
  ι :  Size
  A :  Set ℓ
  a :  A
  F :  A → Set ℓ
  Jr :  JudgRes
  P P' Q R :  Prop' ∞
  P˙ Q˙ :  A → Prop' ∞
  P˂ Q˂ :  Prop˂ ∞
  P˂s :  List (Prop˂ ∞)
  κ :  WpK
  vc :  Val/Ctxred T
  ctx :  Expr ∞ U → Expr ∞ T
  Qᵛ Q'ᵛ Rᵛ :  Val T → Prop' ∞
  e :  Expr ∞ U
  e˙ :  A → Expr ∞ U
  ktx :  Ktx T U
  v :  Val T

infixr -1 _»_ _ᵘ»ᵘ_

-- Defining _⊢[_]*_
data  _⊢[_]*_  where
  ------------------------------------------------------------------------------
  -- Pure rules

  -- The sequent is reflexive
  ⊢-refl :  P ⊢[ ι ] P
  -- The left-hand side of a judgment can be modified with a sequent
  _»_ :  P ⊢[ ι ] Q →  Q ⊢[ ι ]* Jr →  P ⊢[ ι ]* Jr

  -- Introducing ∀ / Eliminating ∃
  ∀-intro :  (∀ a → P ⊢[ ι ] Q˙ a) →  P ⊢[ ι ] ∀˙ Q˙
  ∃-elim :  (∀ a → P˙ a ⊢[ ι ]* Jr) →  ∃˙ P˙ ⊢[ ι ]* Jr
  -- Eliminating ∀ / Introducing ∃
  ∀-elim :  ∀˙ P˙ ⊢[ ι ] P˙ a
  ∃-intro :  P˙ a ⊢[ ι ] ∃˙ P˙
  -- Choice
  choice :  ∀ {P˙˙ : ∀ (a : A) → F a → Prop' ∞} →
            ∀' a , ∃ b , P˙˙ a b ⊢[ ι ] ∃ f ∈ (∀ a → F a) , ∀' a , P˙˙ a (f a)

  -- → is the right adjoint of ∧
  →-intro :  P ∧ Q ⊢[ ι ] R →  Q ⊢[ ι ] P →' R
  →-elim :  Q ⊢[ ι ] P →' R →  P ∧ Q ⊢[ ι ] R

  ------------------------------------------------------------------------------
  -- Rules on ∗, -*, |=> & □

  -- ∗ is unital w.r.t. ⊤', commutative, associative, and monotone
  ⊤∗-elim :  ⊤' ∗ P ⊢[ ι ] P
  ⊤∗-intro :  P ⊢[ ι ] ⊤' ∗ P
  ∗-comm :  P ∗ Q ⊢[ ι ] Q ∗ P
  ∗-assocˡ :  (P ∗ Q) ∗ R ⊢[ ι ] P ∗ (Q ∗ R)
  ∗-monoˡ :  P ⊢[ ι ] Q →  P ∗ R ⊢[ ι ] Q ∗ R

  -- -∗ is the right adjoint of ∗
  -∗-intro :  P ∗ Q ⊢[ ι ] R →  Q ⊢[ ι ] P -∗ R
  -∗-elim :  Q ⊢[ ι ] P -∗ R →  P ∗ Q ⊢[ ι ] R

  -- |=> is monadic: monotone, increasing, and idempotent
  |=>-mono :  P ⊢[ ι ] Q →  |=> P ⊢[ ι ] |=> Q
  |=>-intro :  P ⊢[ ι ] |=> P
  |=>-join :  |=> |=> P ⊢[ ι ] |=> P
  -- ∗ can get inside |=>
  |=>-frameˡ :  P ∗ |=> Q ⊢[ ι ] |=> (P ∗ Q)
  -- ∃ _ , can get outside |=>
  |=>-∃-out :  |=> (∃ _ ∈ A , P) ⊢[ ι ] ∃ _ ∈ A , |=> P

  -- □ is comonadic: monotone, decreasing, and idempotent
  □-mono :  P ⊢[ ι ] Q →  □ P ⊢[ ι ] □ Q
  □-elim :  □ P ⊢[ ι ] P
  □-dup :  □ P ⊢[ ι ] □ □ P
  -- ∧ can turn into ∗ when one argument is under □
  □ˡ-∧⇒∗ :  □ P ∧ Q ⊢[ ι ] □ P ∗ Q
  -- ∀ can get inside □
  □-∀-in :  ∀˙ (□_ ∘ P˙) ⊢[ ι ] □ ∀˙ P˙
  -- ∃ can get outside □
  □-∃-out :  □ ∃˙ P˙ ⊢[ ι ] ∃˙ (□_ ∘ P˙)

  ------------------------------------------------------------------------------
  -- Rules on super update

  -- Lift a sequent under |=> to a super update =>>
  |=>⇒=>> :  P ⊢[ ι ] |=> Q →  P ⊢[ ι ]=>> Q
  -- The super update =>> is transitive
  _ᵘ»ᵘ_ :  P ⊢[ ι ]=>> Q →  Q ⊢[ ι ]=>> R →  P ⊢[ ι ]=>> R
  -- The super update =>> can frame
  =>>-frameˡ :  Q ⊢[ ι ]=>> R →  P ∗ Q ⊢[ ι ]=>> P ∗ R

  ------------------------------------------------------------------------------
  -- Rules on save token

  -- save□ is persistent
  save□-□ :  save□ P˂ ⊢[ ι ] □ save□ P˂

  -- An exclusive/persistent save token can be modified using a thunk sequent
  saveˣ-mono-∧ :  {{Basic R}} →  R ∧ P˂ .! ⊢[< ι ] Q˂ .! →
                  R ∧ saveˣ P˂ ⊢[ ι ] saveˣ Q˂
  save□-mono-∧ :  {{Basic R}} →  R ∧ P˂ .! ⊢[< ι ] Q˂ .! →
                  R ∧ save□ P˂ ⊢[ ι ] save□ Q˂

  -- An exclusive save token saveˣ P˂ is obtained by allocating P˂
  saveˣ-alloc :  P˂ .! ⊢[ ι ]=>> saveˣ P˂
  -- Persistent save tokens save□ P˂ (for P˂ ∈ P˂s) can be obtained
  -- by allocating □ P˂ (for P˂ ∈ P˂s) minus the save tokens themselves
  save□-alloc-rec :
    [∗]-map save□ P˂s -∗ [∗ P˂ ∈ P˂s ] □ P˂ .! ⊢[ ι ]=>> [∗]-map save□ P˂s

  -- Use a exclusive/persistent save token
  saveˣ-use :  saveˣ P˂ ⊢[ ι ]=>> P˂ .!
  save□-use :  save□ P˂ ⊢[ ι ]=>> □ P˂ .!

  ------------------------------------------------------------------------------
  -- Rules on Hoare triple

  -- Monotonicity
  hor-monoˡᵘ :  ∀{Qᵛ : _} →  P' ⊢[ ι ]=>> P →
                P ⊢[ ι ]'⟨ vc ⟩[ κ ] Qᵛ →  P' ⊢[ ι ]'⟨ vc ⟩[ κ ] Qᵛ
  hor-monoʳᵘ :  ∀{Qᵛ : Val T → _} →  (∀ v → Qᵛ v ⊢[ ι ]=>> Q'ᵛ v) →
                P ⊢[ ι ]'⟨ vc ⟩[ κ ] Qᵛ →  P ⊢[ ι ]'⟨ vc ⟩[ κ ] Q'ᵛ

  -- Weaken a Hoare triple from total to partial
  hor-ᵀ⇒ :  ∀{Qᵛ : _} →  P ⊢[ ι ]'⟨ vc ⟩ᵀ Qᵛ →  P ⊢[ ι ]'⟨ vc ⟩ Qᵛ

  -- Bind by a context
  hor-bind :  ∀{Qᵛ : _ → _} {Rᵛ : _ → _} →  P ⊢[ ι ]⟨ e ⟩[ κ ] Qᵛ →
              (∀ v → Qᵛ v ⊢[ ι ]⟨ ktx •← Val⇒Expr v ⟩[ κ ] Rᵛ) →
              P ⊢[ ι ]⟨ ktx •← e ⟩[ κ ] Rᵛ

  -- Value
  hor-valᵘ :  ∀{v : Val T} →  P ⊢[ ι ]=>> Qᵛ v →  P ⊢[ ι ]'⟨ inj₀ v ⟩[ κ ] Qᵛ

  -- Application
  hor-nd :  (∀ a → P ⊢[ ι ]=>> Qᵛ (↑ a)) →
            P ⊢[ ι ]'⟨ inj₁ $ _ , ctx , ndᴿ ⟩[ κ ] Qᵛ

  -- ▶, for partial Hoare triple
  hor-▶ :  ∀{Qᵛ : _} →
           P ⊢[< ι ]⟨ ctx e ⟩ Qᵛ →  P ⊢[ ι ]'⟨ inj₁ $ _ , ctx , ▶ᴿ e ⟩ Qᵛ

  -- Application
  hor-◁ :  ∀{Qᵛ : _} →  P ⊢[ ι ]⟨ ctx $ e˙ a ⟩[ κ ] Qᵛ →
           P ⊢[ ι ]'⟨ inj₁ $ _ , ctx , e˙ ◁ᴿ a ⟩[ κ ] Qᵛ

--------------------------------------------------------------------------------
-- Pers: Persistence of a proposition

record  Pers (P : Prop' ∞) :  Set (^ ℓ)  where
  -- Pers-⇒□: P can turn into □ P
  field Pers-⇒□ :  P ⊢[ ι ] □ P
open Pers {{...}} public
