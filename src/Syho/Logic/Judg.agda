--------------------------------------------------------------------------------
-- Judgment in Syho
--------------------------------------------------------------------------------
-- Its contents are re-exported across Syho.Logic.Core, Supd, Ind, and Hor

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Judg where

open import Base.Level using (Level; ↑_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk; ¡_; !)
open import Base.Func using (_∘_; _$_)
open import Base.Few using (⊤)
open import Base.Eq using (_≡_)
open import Base.Prod using (_×_; _,_)
open import Base.Sum using (inj₀; inj₁)
open import Base.Nat using (ℕ; suc)
open import Base.List using (List)
open import Base.List.Nat using (rep; len)
open import Base.RatPos using (ℚ⁺)
open import Syho.Logic.Prop using (Prop'; Prop˂; ∀₁˙; ∃₁˙; ∀₁-syntax; ∃₁-syntax;
  ∃₁∈-syntax; _∧_; ⊤'; _→'_; _∗_; _-∗_; |=>_; □_; _↪[_]=>>_; ○_; _↦⟨_⟩_;
  _↪⟨_⟩ᴾ_; _↪⟨_⟩ᵀ[_]_; _↦_; _↦ˡ_; Free; Basic)
open import Syho.Lang.Expr using (Addr; Type; ◸_; Expr; Expr˂; ▶_; ∇_; Val; V⇒E;
  AnyVal; ⊤-val)
open import Syho.Lang.Ktxred using (▶ᴿ_; ndᴿ; _◁ᴿ_; ★ᴿ_; _←ᴿ_; allocᴿ; freeᴿ;
  Ktx; _ᴷ◁_; _ᴷ|ᴿ_; Val/Ktxred; val/ktxred)

--------------------------------------------------------------------------------
-- WpKind :  Weakest precondion kind

data  WpKind :  Set₀  where
  -- Partial
  par :  WpKind
  -- Total, with a counter
  tot :  ℕ →  WpKind

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

infix 2 _⊢[_]*_ _⊢[_]_ _⊢[<_]_ _⊢[_][_]=>>_ _⊢[<_][_]=>>_ _⊢[_]⁺⟨_⟩[_]_
  _⊢[_]⁺⟨_⟩ᴾ_ _⊢[_]⁺⟨_⟩ᵀ[_]_ _⊢[_]⟨_⟩[_]_ _⊢[_]⟨_⟩ᴾ_ _⊢[<_]⟨_⟩ᴾ_ _⊢[_]⟨_⟩ᵀ[_]_
  _⊢[<_]⟨_⟩ᵀ[_]_

-- Declaring _⊢[_]*_

data  _⊢[_]*_ :  Prop' ∞ →  Size →  JudgRes →  Set₂

-- ⊢[ ] :  Pure sequent

_⊢[_]_ :  Prop' ∞ →  Size →  Prop' ∞ →  Set₂
P ⊢[ ι ] Q =  P ⊢[ ι ]* Pure Q

-- ⊢[< ] :  Pure sequent under thunk

_⊢[<_]_ :  Prop' ∞ →  Size →  Prop' ∞ →  Set₂
P ⊢[< ι ] Q =  Thunk (P ⊢[_] Q) ι

-- ⊢[ ][ ]=>> etc. :  Super update

_⊢[_][_]=>>_ _⊢[<_][_]=>>_ :  Prop' ∞ →  Size →  ℕ →  Prop' ∞ →  Set₂
P ⊢[ ι ][ i ]=>> Q =  P ⊢[ ι ]* [ i ]=>> Q
P ⊢[< ι ][ i ]=>> Q =  Thunk (P ⊢[_][ i ]=>> Q) ι

-- ⊢[ ]⁺⟨ ⟩[ ] etc. :  Hoare triple over Val/Ktxred

_⊢[_]⁺⟨_⟩[_]_ :
  Prop' ∞ →  Size →  Val/Ktxred T →  WpKind →  (Val T → Prop' ∞) →  Set₂
P ⊢[ ι ]⁺⟨ vk ⟩[ wκ ] Qᵛ =  P ⊢[ ι ]* ⁺⟨ vk ⟩[ wκ ] Qᵛ

_⊢[_]⁺⟨_⟩ᴾ_ :  Prop' ∞ →  Size →  Val/Ktxred T →  (Val T → Prop' ∞) →  Set₂
P ⊢[ ι ]⁺⟨ vk ⟩ᴾ Qᵛ =  P ⊢[ ι ]⁺⟨ vk ⟩[ par ] Qᵛ

_⊢[_]⁺⟨_⟩ᵀ[_]_ :
  Prop' ∞ →  Size →  Val/Ktxred T →  ℕ →  (Val T → Prop' ∞) →  Set₂
P ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ i ] Qᵛ =  P ⊢[ ι ]⁺⟨ vk ⟩[ tot i ] Qᵛ

-- ⊢[ ]⟨ ⟩[ ] etc. :  Hoare triple over Expr

_⊢[_]⟨_⟩[_]_ :
  Prop' ∞ →  Size →  Expr ∞ T →  WpKind →  (Val T → Prop' ∞) →  Set₂
P ⊢[ ι ]⟨ e ⟩[ wκ ] Qᵛ =  P ⊢[ ι ]⁺⟨ val/ktxred e ⟩[ wκ ] Qᵛ

_⊢[_]⟨_⟩ᴾ_ _⊢[<_]⟨_⟩ᴾ_ :
  Prop' ∞ →  Size →  Expr ∞ T →  (Val T → Prop' ∞) →  Set₂
P ⊢[ ι ]⟨ e ⟩ᴾ Qᵛ =  P ⊢[ ι ]⟨ e ⟩[ par ] Qᵛ
P ⊢[< ι ]⟨ e ⟩ᴾ Qᵛ =  Thunk (P ⊢[_]⟨ e ⟩[ par ] Qᵛ) ι

_⊢[_]⟨_⟩ᵀ[_]_ _⊢[<_]⟨_⟩ᵀ[_]_ :
  Prop' ∞ →  Size →  Expr ∞ T →  ℕ →  (Val T → Prop' ∞) →  Set₂
P ⊢[ ι ]⟨ e ⟩ᵀ[ i ] Qᵛ =  P ⊢[ ι ]⟨ e ⟩[ tot i ] Qᵛ
P ⊢[< ι ]⟨ e ⟩ᵀ[ i ] Qᵛ =  Thunk (P ⊢[_]⟨ e ⟩ᵀ[ i ] Qᵛ) ι

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
  P˂s :  List (Prop˂ ∞)
  wκ :  WpKind
  vk :  Val/Ktxred T
  Qᵛ Rᵛ :  Val T → Prop' ∞
  Q˂ᵛ Q'˂ᵛ :  Val T → Prop˂ ∞
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

  -- When P˂ is persistent, □ ○ P˂_i can be obtained recursively, i.e.,
  -- by allocating P˂ minus the target □ ○ P˂

  □○-alloc-rec :  {{Pers (P˂ .!)}} →  □ ○ P˂ →' P˂ .! ⊢[ ι ][ i ]=>> □ ○ P˂

  -- Use ○ P˂

  ○-use :  ○ P˂ ⊢[ ι ][ i ]=>> P˂ .!

  ------------------------------------------------------------------------------
  -- On ↪=>>

  -- Monotonicity of ↪=>>

  ↪=>>-monoˡ-∗ :  {{Basic R}} →  R ∗ P'˂ .! ⊢[< ι ] P˂ .! →
                  R ∗ (P˂ ↪[ i ]=>> Q˂)  ⊢[ ι ]  P'˂ ↪[ i ]=>> Q˂

  ↪=>>-monoʳ-∗ :  {{Basic R}} →  R ∗ Q˂ .! ⊢[< ι ] Q'˂ .! →
                  R ∗ (P˂ ↪[ i ]=>> Q˂)  ⊢[ ι ]  P˂ ↪[ i ]=>> Q'˂

  -- Modify =>> proof

  ↪=>>-suc :  P˂ ↪[ i ]=>> Q˂  ⊢[ ι ]  P˂ ↪[ suc i ]=>> Q˂

  ↪=>>-frameˡ :  ¡ P ↪[ i ]=>> ¡ Q  ⊢[ ι ]  ¡ (R ∗ P) ↪[ i ]=>> ¡ (R ∗ Q)

  -- Make ↪=>> out of ○

  ○⇒↪=>> :  P˂ .! ∗ R˂ .! ⊢[< ι ][ i ]=>> Q˂ .! →  ○ R˂  ⊢[ ι ]  P˂ ↪[ i ]=>> Q˂

  -- Use ↪=>>, with counter increment
  ---- Without that counter increment, we could do any super update
  ---- (=>>/↪=>>-use' in Syho.Logic.Paradox)

  ↪=>>-use :  P˂ .! ∗ (P˂ ↪[ i ]=>> Q˂)  ⊢[ ι ][ suc i ]=>>  Q˂ .!

  ------------------------------------------------------------------------------
  -- On ↪⟨ ⟩ᴾ

  -- Monotonicity of ↪⟨ ⟩ᴾ

  ↪⟨⟩ᴾ-monoˡ-∗ :  ∀{Q˂ᵛ} →
    {{Basic R}} →  (R ∗ P'˂ .! ⊢[< ι ] P˂ .!) →
    R ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ)  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᴾ Q˂ᵛ

  ↪⟨⟩ᴾ-monoʳ-∗ :  ∀{Q˂ᵛ : Val T → _} →
    {{Basic R}} →  (∀ v →  R ∗ Q˂ᵛ v .! ⊢[< ι ] Q'˂ᵛ v .!) →
    R ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ)  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q'˂ᵛ

  -- Modify ⟨ ⟩ᴾ proof

  ↪⟨⟩ᴾ-frameˡ :  ∀{Qᵛ : _ → Prop' ∞} →
    ¡ P ↪⟨ e ⟩ᴾ (λ v → ¡ Qᵛ v)  ⊢[ ι ]  ¡ (R ∗ P) ↪⟨ e ⟩ᴾ λ v → ¡ (R ∗ Qᵛ v)

  -- Make ↪⟨ ⟩ᴾ out of ○

  ○⇒↪⟨⟩ᴾ :  ∀{Q˂ᵛ} →
    P˂ .! ∗ R˂ .! ⊢[< ι ]⟨ e ⟩ᴾ (λ v → Q˂ᵛ v .!) →  ○ R˂  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ

  -- Use ↪⟨⟩ᴾ, with ▶ on the expression
  ---- Without that ▶, we could have any partial Hoare triple
  ---- (horᴾ/↪⟨⟩ᴾ-use' in Syho.Logic.Paradox)

  ↪⟨⟩ᴾ-use :  ∀{Q˂ᵛ} →
    P˂ .! ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ)  ⊢[ ι ]⟨ ▶ ¡ e ⟩ᴾ  λ v → Q˂ᵛ v .!

  ------------------------------------------------------------------------------
  -- On ↪⟨ ⟩ᵀ

  -- Monotonicity of ↪⟨ ⟩ᵀ

  ↪⟨⟩ᵀ-monoˡ-∗ :  ∀{Q˂ᵛ} →
    {{Basic R}} →  (R ∗ P'˂ .! ⊢[< ι ] P˂ .!) →
    R ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ)  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ

  ↪⟨⟩ᵀ-monoʳ-∗ :  ∀{Q˂ᵛ : Val T → _} →
    {{Basic R}} →  (∀ v →  R ∗ Q˂ᵛ v .! ⊢[< ι ] Q'˂ᵛ v .!) →
    R ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ)  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q'˂ᵛ

  -- Modify ⟨ ⟩ᵀ proof

  ↪⟨⟩ᵀ-suc :  ∀{Q˂ᵛ} →  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ suc i ] Q˂ᵛ

  ↪⟨⟩ᵀ-frameˡ :  ∀{Qᵛ : _ → Prop' ∞} →
    ¡ P ↪⟨ e ⟩ᵀ[ i ] (λ v → ¡ Qᵛ v)  ⊢[ ι ]
      ¡ (R ∗ P) ↪⟨ e ⟩ᵀ[ i ] λ v → ¡ (R ∗ Qᵛ v)

  -- Make ↪⟨ ⟩ᵀ out of ○

  ○⇒↪⟨⟩ᵀ :  ∀{Q˂ᵛ} →
    P˂ .! ∗ R˂ .! ⊢[< ι ]⟨ e ⟩ᵀ[ i ] (λ v → Q˂ᵛ v .!) →
    ○ R˂  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ

  -- Use ↪⟨⟩ᵀ, with counter increment
  ---- Without that counter increment, we could have any total Hoare triple
  ---- (horᵀ/↪⟨⟩ᵀ-use' in Syho.Logic.Paradox)

  ↪⟨⟩ᵀ-use :  ∀{Q˂ᵛ} →
    P˂ .! ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ)  ⊢[ ι ]⟨ e ⟩ᵀ[ suc i ]  λ v → Q˂ᵛ v .!

  ------------------------------------------------------------------------------
  -- On Hoare triple

  -- Weaken a Hoare triple from total to partial

  hor-ᵀ⇒ᴾ :  ∀{Qᵛ} →  P ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ i ] Qᵛ →  P ⊢[ ι ]⁺⟨ vk ⟩ᴾ Qᵛ

  -- Counter increment on total Hoare triple

  horᵀ-suc :  ∀{Qᵛ} →  P ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ i ] Qᵛ →  P ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ suc i ] Qᵛ

  -- Compose with a super update

  _ᵘ»ʰ_ :  ∀{Rᵛ} →  P ⊢[ ι ][ i ]=>> Q →  Q ⊢[ ι ]⁺⟨ vk ⟩[ wκ ] Rᵛ →
                    P ⊢[ ι ]⁺⟨ vk ⟩[ wκ ] Rᵛ

  _ʰ»ᵘ_ :  ∀{Qᵛ : Val T → _} →
    P ⊢[ ι ]⁺⟨ vk ⟩[ wκ ] Qᵛ →  (∀ v →  Qᵛ v ⊢[ ι ][ i ]=>> Rᵛ v) →
    P ⊢[ ι ]⁺⟨ vk ⟩[ wκ ] Rᵛ

  -- Frame

  hor-frameˡ :  ∀{Qᵛ} →  P ⊢[ ι ]⁺⟨ vk ⟩[ wκ ] Qᵛ →
                         R ∗ P ⊢[ ι ]⁺⟨ vk ⟩[ wκ ] λ v → R ∗ Qᵛ v

  -- Bind by a context

  hor-bind :  ∀{Qᵛ Rᵛ} →
    P ⊢[ ι ]⟨ e ⟩[ wκ ] Qᵛ →  (∀ v →  Qᵛ v ⊢[ ι ]⟨ ktx ᴷ◁ V⇒E v ⟩[ wκ ] Rᵛ) →
    P ⊢[ ι ]⟨ ktx ᴷ◁ e ⟩[ wκ ] Rᵛ

  -- Value

  hor-valᵘ :  ∀{v : Val T} →
    P ⊢[ ι ][ i ]=>> Qᵛ v →  P ⊢[ ι ]⁺⟨ inj₀ v ⟩[ wκ ] Qᵛ

  -- Non-deterministic value

  hor-ndᵘ :  (∀ x →  P ⊢[ ι ][ i ]=>> Qᵛ (↑ x)) →
             P ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ ndᴿ ⟩[ wκ ] Qᵛ

  -- ▶, for partial and total Hoare triples

  horᴾ-▶ :  ∀{Qᵛ} →  P ⊢[< ι ]⟨ ktx ᴷ◁ e˂ .! ⟩ᴾ Qᵛ →
                     P ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ ▶ᴿ e˂ ⟩ᴾ Qᵛ

  horᵀ-▶ :  ∀{Qᵛ} →  P ⊢[ ι ]⟨ ktx ᴷ◁ e˂ .! ⟩ᵀ[ i ] Qᵛ →
                     P ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ ▶ᴿ e˂ ⟩ᵀ[ i ] Qᵛ

  -- Application

  hor-◁ :  ∀{Qᵛ} →  P ⊢[ ι ]⟨ ktx ᴷ◁ e˙ x ⟩[ wκ ] Qᵛ →
                    P ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ e˙ ◁ᴿ x ⟩[ wκ ] Qᵛ

  -- Memory read

  hor-★ :  ∀{Qᵛ} →
    θ ↦⟨ p ⟩ (V , v) ∗ P ⊢[ ι ]⟨ ktx ᴷ◁ V⇒E v ⟩[ wκ ] Qᵛ →
    θ ↦⟨ p ⟩ (_ , v) ∗ P ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ ★ᴿ θ ⟩[ wκ ] Qᵛ

  -- Memory write

  hor-← :  ∀{Qᵛ} →
    θ ↦ (V , v) ∗ P ⊢[ ι ]⟨ ktx ᴷ◁ ∇ _ ⟩[ wκ ] Qᵛ →
    θ ↦ av ∗ P ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ θ ←ᴿ v ⟩[ wκ ] Qᵛ

  -- Memory allocation

  hor-alloc :  ∀{Qᵛ} →
    (∀ θ →  θ ↦ˡ rep n ⊤-val ∗ Free n θ ∗ P ⊢[ ι ]⟨ ktx ᴷ◁ ∇ θ ⟩[ wκ ] Qᵛ) →
    P ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ allocᴿ n ⟩[ wκ ] Qᵛ

  -- Memory freeing

  hor-free :  ∀{Qᵛ} →
    len avs ≡ n →  P ⊢[ ι ]⟨ ktx ᴷ◁ ∇ _ ⟩[ wκ ] Qᵛ →
    θ ↦ˡ avs ∗ Free n θ ∗ P ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ freeᴿ θ ⟩[ wκ ] Qᵛ
