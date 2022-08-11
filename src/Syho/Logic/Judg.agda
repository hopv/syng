--------------------------------------------------------------------------------
-- Judgment in Syho
--------------------------------------------------------------------------------
-- Its contents are re-exported across Syho.Logic.Core, Supd, Ind, and Hor

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Judg where

open import Base.Level using (Level; ↑_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk; !)
open import Base.Func using (_∘_; _$_)
open import Base.Few using (⊤)
open import Base.Eq using (_≡_)
open import Base.Prod using (_×_; _,_)
open import Base.Sum using (inj₀; inj₁)
open import Base.Bool using (Bool)
open import Base.Nat using (ℕ; suc)
open import Base.List using (List; map)
open import Base.List.Nat using (rep; len)
open import Base.List.All using (All)
open import Base.RatPos using (ℚ⁺)
open import Syho.Logic.Prop using (Prop'; Prop˂; ∀₁˙; ∃₁˙; ∀₁-syntax; ∃₁-syntax;
  ∃₁∈-syntax; _∧_; ⊤'; _→'_; _∗_; _-∗_; |=>_; □_; [∧]_; [∧∈]-syntax; _↪[_]=>>_;
  ○_; _↦⟨_⟩_; _↦_; _↦ˡ_; Free; Basic)
open import Syho.Lang.Expr using (Addr; Type; ◸_; Expr; Expr˂; ∇_; Val; V⇒E;
  AnyVal; ⊤-val)
open import Syho.Lang.Ktxred using (▶ᴿ_; ndᴿ; _◁ᴿ_; ★ᴿ_; _←ᴿ_; allocᴿ; freeᴿ;
  Ktx; _ᴷ◁_; _ᴷ|ᴿ_; Val/Ktxred; val/ktxred)

--------------------------------------------------------------------------------
-- WpKind :  Weakest precondion kind

data  WpKind :  Set₀  where
  -- Partial/total
  par tot :  WpKind

--------------------------------------------------------------------------------
-- JudgRes :  Result of a judgment

private variable
  T U V :  Type
  ι :  Size

infix 3 [_]=>>_ ⁺⟨_⟩[_]_

data  JudgRes :  Set₂  where
  -- Just a proposition
  Pure :  Prop' ∞ →  JudgRes
  -- Under the super update
  [_]=>>_ :  ℕ →  Prop' ∞ →  JudgRes
  -- Weakest precondion, over Val/Ktxred
  ⁺⟨_⟩[_]_ :  Val/Ktxred T →  WpKind →  (Val T → Prop' ∞) →  JudgRes

--------------------------------------------------------------------------------
-- P ⊢[ ι ]* Jr :  Judgment

infix 2 _⊢[_]*_ _⊢[_]_ _⊢[<_]_ _⊢[_][_]=>>_ _⊢[_]⁺⟨_⟩[_]_ _⊢[_]⁺⟨_⟩ᴾ_
  _⊢[_]⁺⟨_⟩ᵀ_ _⊢[_]⟨_⟩[_]_ _⊢[_]⟨_⟩ᴾ_ _⊢[<_]⟨_⟩ᴾ_ _⊢[_]⟨_⟩ᵀ_

-- Declaring _⊢[_]*_
data  _⊢[_]*_ :  Prop' ∞ →  Size →  JudgRes →  Set₂

-- ⊢[ ] : Pure sequent
_⊢[_]_ :  Prop' ∞ →  Size →  Prop' ∞ →  Set₂
P ⊢[ ι ] Q =  P ⊢[ ι ]* Pure Q

-- ⊢[< ] : Pure sequent under ¡
_⊢[<_]_ :  Prop' ∞ →  Size →  Prop' ∞ →  Set₂
P ⊢[< ι ] Q =  Thunk (P ⊢[_] Q) ι

-- ⊢[ ][ ]=>> : Super update
_⊢[_][_]=>>_ :  Prop' ∞ →  Size →  ℕ →  Prop' ∞ →  Set₂
P ⊢[ ι ][ i ]=>> Q =  P ⊢[ ι ]* [ i ]=>> Q

-- ⊢[ ]⁺⟨ ⟩[ ] : Hoare-triple over Val/Ktxred

_⊢[_]⁺⟨_⟩[_]_ :
  Prop' ∞ →  Size →  Val/Ktxred T →  WpKind →  (Val T → Prop' ∞) →  Set₂
P ⊢[ ι ]⁺⟨ vk ⟩[ wκ ] Qᵛ =  P ⊢[ ι ]* ⁺⟨ vk ⟩[ wκ ] Qᵛ

_⊢[_]⁺⟨_⟩ᴾ_ _⊢[_]⁺⟨_⟩ᵀ_ :
  Prop' ∞ →  Size →  Val/Ktxred T →  (Val T → Prop' ∞) →  Set₂
P ⊢[ ι ]⁺⟨ vk ⟩ᴾ Qᵛ =  P ⊢[ ι ]⁺⟨ vk ⟩[ par ] Qᵛ
P ⊢[ ι ]⁺⟨ vk ⟩ᵀ Qᵛ =  P ⊢[ ι ]⁺⟨ vk ⟩[ tot ] Qᵛ

-- ⊢[ ]⟨ ⟩[ ] : Hoare-triple over Expr

_⊢[_]⟨_⟩[_]_ :
  Prop' ∞ →  Size →  Expr ∞ T →  WpKind →  (Val T → Prop' ∞) →  Set₂
P ⊢[ ι ]⟨ e ⟩[ wκ ] Qᵛ =  P ⊢[ ι ]⁺⟨ val/ktxred e ⟩[ wκ ] Qᵛ

_⊢[_]⟨_⟩ᴾ_ _⊢[<_]⟨_⟩ᴾ_ _⊢[_]⟨_⟩ᵀ_ :
  Prop' ∞ →  Size →  Expr ∞ T →  (Val T → Prop' ∞) →  Set₂
P ⊢[ ι ]⟨ e ⟩ᴾ Qᵛ =  P ⊢[ ι ]⟨ e ⟩[ par ] Qᵛ
P ⊢[< ι ]⟨ e ⟩ᴾ Qᵛ =  Thunk (P ⊢[_]⟨ e ⟩[ par ] Qᵛ) ι
P ⊢[ ι ]⟨ e ⟩ᵀ Qᵛ =  P ⊢[ ι ]⟨ e ⟩[ tot ] Qᵛ

-- Pers :  Persistence of a proposition

record  Pers (P : Prop' ∞) :  Set₂  where
  inductive
  -- Pers-⇒□ :  P can turn into □ P
  field Pers-⇒□ :  P ⊢[ ι ] □ P
open Pers {{...}} public

private variable
  ℓ :  Level
  i j n :  ℕ
  X :  Set ℓ
  x :  X
  Y˙ :  X → Set ℓ
  Jr :  JudgRes
  P P' Q R :  Prop' ∞
  P˙ Q˙ :  X → Prop' ∞
  P˂ P'˂ Q˂ Q'˂ R˂ :  Prop˂ ∞
  P˂˙ Q˂˙ :  X → Prop˂ ∞
  P˂s :  List (Prop˂ ∞)
  wκ :  WpKind
  vk :  Val/Ktxred T
  Qᵛ Rᵛ :  Val T → Prop' ∞
  e :  Expr ∞ U
  e˂ :  Expr˂ ∞ U
  e˙ :  X → Expr ∞ U
  ktx :  Ktx T U
  v :  Val T
  θ :  Addr
  p :  ℚ⁺
  av :  AnyVal
  avs :  List AnyVal

infixr -1 _»_ _ᵘ»ᵘ_ _ᵘ»ʰ_ _ʰ»ᵘ_

-- Defining _⊢[_]*_
data  _⊢[_]*_  where
  ------------------------------------------------------------------------------
  -- General rules

  -- The sequent is reflexive

  ⊢-refl :  P ⊢[ ι ] P

  -- The left-hand side of a judgment can be modified with a sequent

  _»_ :  P ⊢[ ι ] Q →  Q ⊢[ ι ]* Jr →  P ⊢[ ι ]* Jr

  ------------------------------------------------------------------------------
  -- On ∀ / ∃

  -- Introducing ∀ / Eliminating ∃

  ∀₁-intro :  (∀ x →  P ⊢[ ι ] Q˙ x) →  P ⊢[ ι ] ∀₁˙ Q˙

  ∃₁-elim :  (∀ x →  P˙ x ⊢[ ι ]* Jr) →  ∃₁˙ P˙ ⊢[ ι ]* Jr

  -- Eliminating ∀ / Introducing ∃

  ∀₁-elim :  ∀ x →  ∀₁˙ P˙ ⊢[ ι ] P˙ x

  ∃₁-intro :  ∀ x →  P˙ x ⊢[ ι ] ∃₁˙ P˙

  -- Choice, which is safe to have thanks to the logic's predicativity

  choice₁ :  ∀ {P˙˙ : ∀ (x : X) → Y˙ x → Prop' ∞} →
    ∀₁ x , ∃₁ y , P˙˙ x y ⊢[ ι ] ∃₁ y˙ ∈ (∀ x → Y˙ x) , ∀₁ x , P˙˙ x (y˙ x)

  ------------------------------------------------------------------------------
  -- On →

  -- → is the right adjoint of ∧

  →-intro :  P ∧ Q ⊢[ ι ] R →  Q ⊢[ ι ] P →' R

  →-elim :  Q ⊢[ ι ] P →' R →  P ∧ Q ⊢[ ι ] R

  ------------------------------------------------------------------------------
  -- On ∗

  -- ∗ is unital w.r.t. ⊤', commutative, associative, and monotone

  ⊤∗-elim :  ⊤' ∗ P ⊢[ ι ] P

  ⊤∗-intro :  P ⊢[ ι ] ⊤' ∗ P

  ∗-comm :  P ∗ Q ⊢[ ι ] Q ∗ P

  ∗-assocˡ :  (P ∗ Q) ∗ R ⊢[ ι ] P ∗ (Q ∗ R)

  ∗-monoˡ :  P ⊢[ ι ] Q →  P ∗ R ⊢[ ι ] Q ∗ R

  ------------------------------------------------------------------------------
  -- On -∗

  -- -∗ is the right adjoint of ∗

  -∗-intro :  P ∗ Q ⊢[ ι ] R →  Q ⊢[ ι ] P -∗ R

  -∗-elim :  Q ⊢[ ι ] P -∗ R →  P ∗ Q ⊢[ ι ] R

  ------------------------------------------------------------------------------
  -- On |=>

  -- |=> is monadic :  monotone, increasing, and idempotent

  |=>-mono :  P ⊢[ ι ] Q →  |=> P ⊢[ ι ] |=> Q

  |=>-intro :  P ⊢[ ι ] |=> P

  |=>-join :  |=> |=> P ⊢[ ι ] |=> P

  -- ∗ can get inside |=>

  |=>-frameˡ :  P ∗ |=> Q ⊢[ ι ] |=> (P ∗ Q)

  -- ∃ _ , can get outside |=>

  |=>-∃₁-out :  |=> (∃₁ _ ∈ X , P) ⊢[ ι ] ∃₁ _ ∈ X , |=> P

  ------------------------------------------------------------------------------
  -- On □

  -- □ is comonadic :  monotone, decreasing, and idempotent

  □-mono :  P ⊢[ ι ] Q →  □ P ⊢[ ι ] □ Q

  □-elim :  □ P ⊢[ ι ] P

  □-dup :  □ P ⊢[ ι ] □ □ P

  -- ∧ can turn into ∗ when one argument is under □

  □ˡ-∧⇒∗ :  □ P ∧ Q ⊢[ ι ] □ P ∗ Q

  -- ∀ can get inside □

  □-∀₁-in :  ∀₁˙ (□_ ∘ P˙) ⊢[ ι ] □ ∀₁˙ P˙

  -- ∃ can get outside □

  □-∃₁-out :  □ ∃₁˙ P˙ ⊢[ ι ] ∃₁˙ (□_ ∘ P˙)

  ------------------------------------------------------------------------------
  -- On =>>

  -- Increment the counter of a super update by 1

  =>>-suc :  P ⊢[ ι ][ i ]=>> Q →  P ⊢[ ι ][ suc i ]=>> Q

  -- Lift a sequent under |=> to a super update =>>

  |=>⇒=>> :  P ⊢[ ι ] |=> Q →  P ⊢[ ι ][ i ]=>> Q

  -- The super update =>> is transitive

  _ᵘ»ᵘ_ :  P ⊢[ ι ][ i ]=>> Q →  Q ⊢[ ι ][ i ]=>> R →  P ⊢[ ι ][ i ]=>> R

  -- The super update =>> can frame

  =>>-frameˡ :  Q ⊢[ ι ][ i ]=>> R →  P ∗ Q ⊢[ ι ][ i ]=>> P ∗ R

  ------------------------------------------------------------------------------
  -- On ○

  -- Monotonicity of ○

  ○-mono-∗ :  {{Basic R}} →  R ∗ P˂ .! ⊢[< ι ] Q˂ .! →  R ∗ ○ P˂ ⊢[ ι ] ○ Q˂

  -- ○ P˂ is obtained by allocating P˂

  ○-alloc :  P˂ .! ⊢[ ι ][ i ]=>> ○ P˂

  -- When every P˂_i is persistent,
  -- ∧_i □ ○ P˂_i can be obtained mutually recursively, i.e.,
  -- by allocating ∧_i P˂_i minus the target ∧_i □ ○ P˂_i

  □○-alloc-mutrec :  {{All (λ P˂ → Pers (P˂ .!)) P˂s}} →
    [∧ P˂ ∈ P˂s ] □ ○ P˂ →' [∧ P˂ ∈ P˂s ] P˂ .!
      ⊢[ ι ][ i ]=>> [∧ P˂ ∈ P˂s ] □ ○ P˂

  -- Use ○ P˂

  ○-use :  ○ P˂ ⊢[ ι ][ i ]=>> P˂ .!

  ------------------------------------------------------------------------------
  -- On ↪=>>

  -- Monotonicity of ↪=>>

  ↪=>>-monoˡ-∗ :  {{Basic R}} →  (R ∗ P'˂ .! ⊢[< ι ] P˂ .!) →
                  R ∗ (P˂ ↪[ i ]=>> Q˂)  ⊢[ ι ]  P'˂ ↪[ i ]=>> Q˂

  ↪=>>-monoʳ-∗ :  {{Basic R}} →  (R ∗ Q˂ .! ⊢[< ι ] Q'˂ .!) →
                  R ∗ (P˂ ↪[ i ]=>> Q˂)  ⊢[ ι ]  P˂ ↪[ i ]=>> Q'˂

  -- Make ↪=>> out of ○

  ○⇒∀₁↪=>> :  (∀ x →  R˂ .! ∗ P˂˙ x .! ⊢[ ι ][ i ]=>> Q˂˙ x .!) →
              ○ R˂  ⊢[ ι ]  ∀₁ x , (P˂˙ x ↪[ i ]=>> Q˂˙ x)

  -- Use ↪=>>

  ↪=>>-use :  P˂ .! ∗ (P˂ ↪[ i ]=>> Q˂)  ⊢[ ι ][ suc i ]=>>  Q˂ .!

  ------------------------------------------------------------------------------
  -- On Hoare triple

  -- Weaken a Hoare triple from total to partial

  hor-ᵀ⇒ᴾ :  ∀{Qᵛ : _} →  P ⊢[ ι ]⁺⟨ vk ⟩ᵀ Qᵛ →  P ⊢[ ι ]⁺⟨ vk ⟩ᴾ Qᵛ

  -- Compose with a super update

  _ᵘ»ʰ_ :  ∀{Rᵛ : _} →  P ⊢[ ι ][ i ]=>> Q →  Q ⊢[ ι ]⁺⟨ vk ⟩[ wκ ] Rᵛ →
                        P ⊢[ ι ]⁺⟨ vk ⟩[ wκ ] Rᵛ

  _ʰ»ᵘ_ :  ∀{Qᵛ : Val T → _} →
    P ⊢[ ι ]⁺⟨ vk ⟩[ wκ ] Qᵛ →  (∀ v →  Qᵛ v ⊢[ ι ][ i ]=>> Rᵛ v) →
    P ⊢[ ι ]⁺⟨ vk ⟩[ wκ ] Rᵛ

  -- Frame

  hor-frameˡ :  ∀{Qᵛ : _} →  P ⊢[ ι ]⁺⟨ vk ⟩[ wκ ] Qᵛ →
                             R ∗ P ⊢[ ι ]⁺⟨ vk ⟩[ wκ ] λ v → R ∗ Qᵛ v

  -- Bind by a context

  hor-bind :  ∀{Qᵛ : _} {Rᵛ : _} →
    P ⊢[ ι ]⟨ e ⟩[ wκ ] Qᵛ →  (∀ v →  Qᵛ v ⊢[ ι ]⟨ ktx ᴷ◁ V⇒E v ⟩[ wκ ] Rᵛ) →
    P ⊢[ ι ]⟨ ktx ᴷ◁ e ⟩[ wκ ] Rᵛ

  -- Value

  hor-valᵘ :  ∀{v : Val T} →
    P ⊢[ ι ][ i ]=>> Qᵛ v →  P ⊢[ ι ]⁺⟨ inj₀ v ⟩[ wκ ] Qᵛ

  -- Non-deterministic value

  hor-ndᵘ :  (∀ x →  P ⊢[ ι ][ i ]=>> Qᵛ (↑ x)) →
             P ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ ndᴿ ⟩[ wκ ] Qᵛ

  -- ▶, for partial and total Hoare triples

  horᴾ-▶ :  ∀{Qᵛ : _} →  P ⊢[< ι ]⟨ ktx ᴷ◁ e˂ .! ⟩ᴾ Qᵛ →
                         P ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ ▶ᴿ e˂ ⟩ᴾ Qᵛ

  horᵀ-▶ :  ∀{Qᵛ : _} →  P ⊢[ ι ]⟨ ktx ᴷ◁ e˂ .! ⟩ᵀ Qᵛ →
                         P ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ ▶ᴿ e˂ ⟩ᵀ Qᵛ

  -- Application

  hor-◁ :  ∀{Qᵛ : _} →  P ⊢[ ι ]⟨ ktx ᴷ◁ e˙ x ⟩[ wκ ] Qᵛ →
                        P ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ e˙ ◁ᴿ x ⟩[ wκ ] Qᵛ

  -- Memory read

  hor-★ :  ∀{Qᵛ : _} →
    θ ↦⟨ p ⟩ (V , v) ∗ P ⊢[ ι ]⟨ ktx ᴷ◁ V⇒E v ⟩[ wκ ] Qᵛ →
    θ ↦⟨ p ⟩ (_ , v) ∗ P ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ ★ᴿ θ ⟩[ wκ ] Qᵛ

  -- Memory write

  hor-← :  ∀{Qᵛ : _} →
    θ ↦ (V , v) ∗ P ⊢[ ι ]⟨ ktx ᴷ◁ ∇ _ ⟩[ wκ ] Qᵛ →
    θ ↦ av ∗ P ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ θ ←ᴿ v ⟩[ wκ ] Qᵛ

  -- Memory allocation

  hor-alloc :  ∀{Qᵛ : _} →
    (∀ θ →  θ ↦ˡ rep n ⊤-val ∗ Free n θ ∗ P ⊢[ ι ]⟨ ktx ᴷ◁ ∇ θ ⟩[ wκ ] Qᵛ) →
    P ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ allocᴿ n ⟩[ wκ ] Qᵛ

  -- Memory freeing

  hor-free :  ∀{Qᵛ : _} →
    len avs ≡ n →  P ⊢[ ι ]⟨ ktx ᴷ◁ ∇ _ ⟩[ wκ ] Qᵛ →
    θ ↦ˡ avs ∗ Free n θ ∗ P ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ freeᴿ θ ⟩[ wκ ] Qᵛ
