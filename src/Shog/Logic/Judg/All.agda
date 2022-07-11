--------------------------------------------------------------------------------
-- Judgment in Shog
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Logic.Judg.All (ℓ : Level) where

open import Base.Level using (^_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk; !)
open import Base.Func using (_∘_)
open import Base.Bool using (Bool)
open import Base.List using (List)
open import Shog.Logic.Prop ℓ

--------------------------------------------------------------------------------
-- Judgment: P ⊢[ ι ]* Jr

infix 3 |=>>_

-- Result of a judgment
data  JudgRes :  Set (^ ℓ)  where
  -- Just a proposition
  pure :  Prop' ∞ →  JudgRes
  -- Under the super update
  |=>>_ :  Prop' ∞ →  JudgRes

private variable
  P Q R :  Prop' ∞
  Jr :  JudgRes
  A :  Set ℓ
  P˙ Q˙ :  A → Prop' ∞
  P˂ Q˂ :  Prop˂ ∞
  a :  A
  F :  A → Set ℓ
  b :  Bool
  P˂s :  List (Prop˂ ∞)
  ι :  Size

-- Declaring Judg
data  Judg (ι : Size) :  Prop' ∞ →  JudgRes →  Set (^ ℓ)

infix 2 _⊢[_]*_ _⊢[_]_ _⊢[<_]_ _⊢[_]=>>_

-- ⊢[ ]* : General judgment
_⊢[_]*_ :  Prop' ∞ →  Size →  JudgRes →  Set (^ ℓ)
P ⊢[ ι ]* Jr =  Judg ι P Jr

-- ⊢[ ] : Sequent
_⊢[_]_ :  Prop' ∞ →  Size →  Prop' ∞ →  Set (^ ℓ)
P ⊢[ ι ] Q =  P ⊢[ ι ]* pure Q

-- ⊢[< ] : Sequent under thunk
_⊢[<_]_ :  Prop' ∞ →  Size →  Prop' ∞ →  Set (^ ℓ)
P ⊢[< ι ] Q =  Thunk (P ⊢[_] Q) ι

-- ⊢[ ]=>> : Super update
_⊢[_]=>>_ :  Prop' ∞ →  Size →  Prop' ∞ →  Set (^ ℓ)
P ⊢[ ι ]=>> Q =  P ⊢[ ι ]* |=>> Q

infixr -1 _»_ _ᵘ»ᵘ_

-- Defining Judg
data  Judg ι  where
  ------------------------------------------------------------------------------
  -- The sequent is reflexive
  ⊢-refl :  P ⊢[ ι ] P
  -- The left-hand side of a judgment can be modified with a sequent
  _»_ :  P ⊢[ ι ] Q →  Q ⊢[ ι ]* Jr →  P ⊢[ ι ]* Jr
  ------------------------------------------------------------------------------
  -- Introducing ∀ / Eliminating ∃
  ∀-intro :  (∀ a → P ⊢[ ι ] Q˙ a) →  P ⊢[ ι ] ∀˙ _ Q˙
  ∃-elim :  (∀ a → P˙ a ⊢[ ι ]* Jr) →  ∃˙ _ P˙ ⊢[ ι ]* Jr
  -- Eliminating ∀ / Introducing ∃
  ∀-elim :  ∀˙ _ P˙ ⊢[ ι ] P˙ a
  ∃-intro :  P˙ a ⊢[ ι ] ∃˙ _ P˙
  choice :  ∀ {P˙˙ : ∀ (a : A) → F a → Prop' ∞} →
    ∀' a , ∃ b , P˙˙ a b ⊢[ ι ] ∃ f ∈ (∀ a → F a) , ∀' a , P˙˙ a (f a)
  ------------------------------------------------------------------------------
  -- → is the right adjoint of ∧
  →-intro :  P ∧ Q ⊢[ ι ] R →  Q ⊢[ ι ] P →' R
  →-elim :  Q ⊢[ ι ] P →' R →  P ∧ Q ⊢[ ι ] R
  ------------------------------------------------------------------------------
  -- ∗ is unital w.r.t. ⊤', commutative, associative, and monotone
  ⊤∗-elim :  ⊤' ∗ P ⊢[ ι ] P
  ⊤∗-intro :  P ⊢[ ι ] ⊤' ∗ P
  ∗-comm :  P ∗ Q ⊢[ ι ] Q ∗ P
  ∗-assocˡ :  (P ∗ Q) ∗ R ⊢[ ι ] P ∗ (Q ∗ R)
  ∗-monoˡ :  P ⊢[ ι ] Q →  P ∗ R ⊢[ ι ] Q ∗ R
  ------------------------------------------------------------------------------
  -- -∗ is the right adjoint of ∗
  -∗-intro :  P ∗ Q ⊢[ ι ] R →  Q ⊢[ ι ] P -∗ R
  -∗-elim :  Q ⊢[ ι ] P -∗ R →  P ∗ Q ⊢[ ι ] R
  ------------------------------------------------------------------------------
  -- |=> is monadic: monotone, increasing, and idempotent
  |=>-mono :  P ⊢[ ι ] Q →  |=> P ⊢[ ι ] |=> Q
  |=>-intro :  P ⊢[ ι ] |=> P
  |=>-join :  |=> |=> P ⊢[ ι ] |=> P
  -- ∗ can get inside |=>
  |=>-frameˡ :  P ∗ |=> Q ⊢[ ι ] |=> (P ∗ Q)
  -- ∃ _ , can get outside |=>
  |=>-∃-out :  |=> (∃ _ ∈ A , P) ⊢[ ι ] ∃ _ ∈ A , |=> P
  ------------------------------------------------------------------------------
  -- □ is comonadic: monotone, decreasing, and idempotent
  □-mono :  P ⊢[ ι ] Q →  □ P ⊢[ ι ] □ Q
  □-elim :  □ P ⊢[ ι ] P
  □-dup :  □ P ⊢[ ι ] □ □ P
  -- ∧ can turn into ∗ when one argument is under □
  □ˡ-∧⇒∗ :  □ P ∧ Q ⊢[ ι ] □ P ∗ Q
  -- ∀ can get inside □
  □-∀-in :  ∀˙ _ (□_ ∘ P˙) ⊢[ ι ] □ ∀˙ _ P˙
  -- ∃ can get outside □
  □-∃-out :  □ ∃˙ _ P˙ ⊢[ ι ] ∃˙ _ (□_ ∘ P˙)
  ------------------------------------------------------------------------------
  -- A thunk sequent under |=> can be lifted to a super update =>>
  ˂|=>⇒=>> :  P ⊢[< ι ] |=> Q →  P ⊢[ ι ]=>> Q
  -- The super update =>> is transitive
  _ᵘ»ᵘ_ :  P ⊢[ ι ]=>> Q →  Q ⊢[ ι ]=>> R →  P ⊢[ ι ]=>> R
  -- The super update =>> can frame
  =>>-frameˡ :  Q ⊢[ ι ]=>> R →  P ∗ Q ⊢[ ι ]=>> P ∗ R
  ------------------------------------------------------------------------------
  -- save□ is persistent
  save□-□ :  save□ P˂ ⊢[ ι ] □ save□ P˂
  -- An exclusive/persistent save token can be modified using a thunk sequent
  saveˣ-mono-∧ :  {{Basic R}} →
    R ∧ P˂ .! ⊢[< ι ] Q˂ .! →  R ∧ saveˣ P˂ ⊢[ ι ] saveˣ Q˂
  save□-mono-∧ :  {{Basic R}} →
    R ∧ P˂ .! ⊢[< ι ] Q˂ .! →  R ∧ save□ P˂ ⊢[ ι ] save□ Q˂
  -- An exclusive save token saveˣ P˂ is obtained by allocating P˂
  saveˣ-alloc :  P˂ .! ⊢[ ι ]=>> saveˣ P˂
  -- Persistent save tokens save□ P˂, ... can be obtained
  -- by allocating □ P˂, ... minus the tokens save□ P˂, ... themselves
  save□-alloc-rec :
    [∗]-map save□ P˂s -∗ [∗ P˂ ∈ P˂s ] □ P˂ .! ⊢[ ι ]=>> [∗]-map save□ P˂s
  -- Use a exclusive/persistent save token
  saveˣ-use :  saveˣ P˂ ⊢[ ι ]=>> P˂ .!
  save□-use :  save□ P˂ ⊢[ ι ]=>> □ P˂ .!

--------------------------------------------------------------------------------
-- Pers: Persistence of a proposition

record  Pers (P : Prop' ∞) :  Set (^ ℓ)  where
  -- Pers-⇒□: P can turn into □ P
  field Pers-⇒□ :  P ⊢[ ι ] □ P
open Pers {{...}} public
