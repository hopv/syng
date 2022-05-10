--------------------------------------------------------------------------------
-- Judgment in Shog
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Logic.Judg.All (ℓ : Level) where

open import Base.Level using (sucˡ)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk; !)
open import Base.Func using (_∘_)
open import Base.Bool using (Bool)
open import Base.List using (List)
open import Shog.Logic.Prop ℓ

--------------------------------------------------------------------------------
-- Judgment: P ⊢[ ι ]* Jr

-- Result of a judgment
data JudgRes : Set (sucˡ ℓ) where
  -- Just a proposition
  pure : Prop' ∞ → JudgRes
  -- Under the super update
  |=>> : Prop' ∞ → JudgRes

private variable
  P Q R : Prop' ∞
  Jr : JudgRes
  A : Set ℓ
  P˙ Q˙ : A → Prop' ∞
  P^ Q^ : Prop< ∞
  a : A
  F : A → Set ℓ
  b : Bool
  P^s : List (Prop< ∞)

-- Declaring Judg
data Judg (ι : Size) : Prop' ∞ → JudgRes → Set (sucˡ ℓ)

infix 2 _⊢[_]*_ _⊢[_]_ _⊢[<_]_ _⊢[_]=>>_

-- General judgment
_⊢[_]*_ : Prop' ∞ → Size → JudgRes → Set (sucˡ ℓ)
P ⊢[ ι ]* Jr = Judg ι P Jr

-- Sequent
_⊢[_]_ : Prop' ∞ → Size → Prop' ∞ → Set (sucˡ ℓ)
P ⊢[ ι ] Q = P ⊢[ ι ]* pure Q

-- Sequent under thunk
_⊢[<_]_ : Prop' ∞ → Size → Prop' ∞ → Set (sucˡ ℓ)
P ⊢[< ι ] Q = Thunk (P ⊢[_] Q) ι

-- Super update
_⊢[_]=>>_ : Prop' ∞ → Size → Prop' ∞ → Set (sucˡ ℓ)
P ⊢[ ι ]=>> Q = P ⊢[ ι ]* |=>> Q

infixr -1 _»_ _ᵘ»ᵘ_

-- Defining Judg
data Judg ι where
  ------------------------------------------------------------------------------
  -- The sequent is reflexive
  refl : P ⊢[ ι ] P
  -- The left-hand side of a judgment can be modified with a sequent
  _»_ : P ⊢[ ι ] Q → Q ⊢[ ι ]* Jr → P ⊢[ ι ]* Jr
  ------------------------------------------------------------------------------
  -- Introducing ∀ / Eliminating ∃
  ∀-intro : (∀ a → P ⊢[ ι ] Q˙ a) → P ⊢[ ι ] ∀˙ A Q˙
  ∃-elim : (∀ a → P˙ a ⊢[ ι ]* Jr) → ∃˙ A P˙ ⊢[ ι ]* Jr
  -- Eliminating ∀ / Introducing ∃
  ∀-elim : ∀˙ A P˙ ⊢[ ι ] P˙ a
  ∃-intro : P˙ a ⊢[ ι ] ∃˙ A P˙
  -- ∀ can get inside ⌜ ⌝
  ⌜⌝-∀-in : ∀' a ∈ A , ⌜ F a ⌝ ⊢[ ι ] ⌜ (∀ a → F a) ⌝
  ------------------------------------------------------------------------------
  -- → is the right adjoint of ∧
  →-intro : P ∧ Q ⊢[ ι ] R → Q ⊢[ ι ] P →' R
  →-elim : Q ⊢[ ι ] P →' R → P ∧ Q ⊢[ ι ] R
  ------------------------------------------------------------------------------
  -- ∗ is unital w.r.t. ⊤', commutative, associative, and monotone
  ⊤∗-elim : ⊤' ∗ P ⊢[ ι ] P
  ⊤∗-intro : P ⊢[ ι ] ⊤' ∗ P
  ∗-comm : P ∗ Q ⊢[ ι ] Q ∗ P
  ∗-assocˡ : (P ∗ Q) ∗ R ⊢[ ι ] P ∗ (Q ∗ R)
  ∗-monoˡ : P ⊢[ ι ] Q → P ∗ R ⊢[ ι ] Q ∗ R
  ------------------------------------------------------------------------------
  -- -∗ is the right adjoint of ∗
  -∗-intro : P ∗ Q ⊢[ ι ] R → Q ⊢[ ι ] P -∗ R
  -∗-elim : Q ⊢[ ι ] P -∗ R → P ∗ Q ⊢[ ι ] R
  ------------------------------------------------------------------------------
  -- |=> is monadic: monotone, increasing, and idempotent
  |=>-mono : P ⊢[ ι ] Q → |=> P ⊢[ ι ] |=> Q
  |=>-intro : P ⊢[ ι ] |=> P
  |=>-join : |=> (|=> P) ⊢[ ι ] |=> P
  -- ∗ can get inside |=>
  |=>-frameˡ : P ∗ |=> Q ⊢[ ι ] |=> (P ∗ Q)
  -- ∃ _ , can get outside |=>
  |=>-∃-out : |=> (∃ _ ∈ A , P) ⊢[ ι ] ∃ _ ∈ A , |=> P
  ------------------------------------------------------------------------------
  -- □ is comonadic: monotone, decreasing, and idempotent
  □-mono : P ⊢[ ι ] Q → □ P ⊢[ ι ] □ Q
  □-elim : □ P ⊢[ ι ] P
  □-dup : □ P ⊢[ ι ] □ (□ P)
  -- ∧ can turn into ∗ when one argument is under □
  □ˡ-∧⇒∗ : □ P ∧ Q ⊢[ ι ] □ P ∗ Q
  -- ∀ can get inside □
  □-∀-in : ∀˙ A (□ ∘ P˙) ⊢[ ι ] □ (∀˙ A P˙)
  -- ∃ can get outside □
  □-∃-out : □ (∃˙ A P˙) ⊢[ ι ] ∃˙ A (□ ∘ P˙)
  ------------------------------------------------------------------------------
  -- A thunk sequent under |=> can be lifted to a super update =>>
  ^|=>⇒=>> : P ⊢[< ι ] |=> Q → P ⊢[ ι ]=>> Q
  -- The super update =>> is transitive
  _ᵘ»ᵘ_ : P ⊢[ ι ]=>> Q → Q ⊢[ ι ]=>> R → P ⊢[ ι ]=>> R
  -- The super update =>> can frame
  =>>-frameˡ : Q ⊢[ ι ]=>> R → P ∗ Q ⊢[ ι ]=>> P ∗ R
  ------------------------------------------------------------------------------
  -- The save token can be modified with a thunk sequent
  save-monoʳ : {{Basic R}} →
    R ∗ P^ .! ⊢[< ι ] Q^ .! → R ∗ save b P^ ⊢[ ι ] save b Q^
  -- save□ weakens into savex
  save-□⇒x : save□ P^ ⊢[ ι ] savex P^
  -- save□ is persistent
  save□-□ : save□ P^ ⊢[ ι ] □ (save□ P^)
  -- An exclusive save token savex P^ is obtained by allocating P^
  savex-alloc : P^ .! ⊢[ ι ]=>> savex P^
  -- Persistent save tokens save□ P^, ... can be obtained
  -- by allocating □ P^, ... minus the tokens save□ P^, ... themselves
  save□-alloc-rec : [∗]-map save□ P^s -∗ [∗]-map (λ P^ → □ (P^ .!)) P^s
                      ⊢[ ι ]=>> [∗]-map save□ P^s

--------------------------------------------------------------------------------
-- Pers P : Persistence of a proposition

record Pers (P : Prop' ∞) : Set (sucˡ ℓ) where
  -- P can turn into □ P
  field pers : ∀ {ι} → P ⊢[ ι ] □ P
open Pers {{...}} public
