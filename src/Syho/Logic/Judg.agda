--------------------------------------------------------------------------------
-- Judgment in Syho
--------------------------------------------------------------------------------
-- Its contents are re-exported across Syho.Logic.Core, Supd, Ind, and Hor

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Judg where

open import Base.Level using (Level; ↑_)
open import Base.Func using (_∘_; _$_)
open import Base.Few using (⊤)
open import Base.Eq using (_≡_)
open import Base.Size using (Size; ∞; Thunk; ¡_; !)
open import Base.Prod using (_×_; _,_; -,_)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Base.Nat using (ℕ; ṡ_)
open import Base.List using (List; len; rep)
open import Base.RatPos using (ℚ⁺; _+ᴿ⁺_; _≤1ᴿ⁺)

open import Syho.Logic.Prop using (Prop'; Prop˂; ∀₁˙; ∃₁˙; ∀₁-syntax; ∃₁-syntax;
  ∃₁∈-syntax; _∧_; ⊤'; ⌜_⌝₁; ⌜_⌝₀; _→'_; _∗_; _-∗_; ⤇_; □_; _↪[_]⇛_; ○_; _↦⟨_⟩_;
  _↪⟨_⟩ᴾ_; _↪⟨_⟩ᵀ[_]_; _↦_; _↦ˡ_; Free; Basic)
open import Syho.Lang.Expr using (Addr; Type; ◸_; Expr; Expr˂; ▶_; ∇_; Val; ṽ_;
  V⇒E; TyVal; ⊤ṽ)
open import Syho.Lang.Ktxred using (▶ᴿ_; ndᴿ; _◁ᴿ_; _⁏ᴿ_; 🞰ᴿ_; _←ᴿ_; allocᴿ;
  freeᴿ; Ktx; _ᴷ◁_; _ᴷ|_; Val/Ktxred; val/ktxred)

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

infix 3 [_]⇛_ ⁺⟨_⟩[_]_

data  JudgRes :  Set₂  where
  -- Just a proposition
  Pure :  Prop' ∞ →  JudgRes
  -- Under the super update
  [_]⇛_ :  ℕ →  Prop' ∞ →  JudgRes
  -- Weakest precondion, over Val/Ktxred
  ⁺⟨_⟩[_]_ :  Val/Ktxred T →  WpKind →  (Val T → Prop' ∞) →  JudgRes

--------------------------------------------------------------------------------
-- P ⊢[ ι ]* Jr :  Judgment

infix 2 _⊢[_]*_ _⊢[_]_ _⊢[<_]_ _⊢[_][_]⇛_ _⊢[<_][_]⇛_ _⊢[_]⁺⟨_⟩[_]_
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

-- ⊢[ ][ ]⇛ etc. :  Super update

_⊢[_][_]⇛_ _⊢[<_][_]⇛_ :  Prop' ∞ →  Size →  ℕ →  Prop' ∞ →  Set₂
P ⊢[ ι ][ i ]⇛ Q =  P ⊢[ ι ]* [ i ]⇛ Q
P ⊢[< ι ][ i ]⇛ Q =  Thunk (P ⊢[_][ i ]⇛ Q) ι

-- ⊢[ ]⁺⟨ ⟩[ ] etc. :  Hoare triple over Val/Ktxred

_⊢[_]⁺⟨_⟩[_]_ :
  Prop' ∞ →  Size →  Val/Ktxred T →  WpKind →  (Val T → Prop' ∞) →  Set₂
P ⊢[ ι ]⁺⟨ vk ⟩[ wκ ] Q˙ =  P ⊢[ ι ]* ⁺⟨ vk ⟩[ wκ ] Q˙

_⊢[_]⁺⟨_⟩ᴾ_ :  Prop' ∞ →  Size →  Val/Ktxred T →  (Val T → Prop' ∞) →  Set₂
P ⊢[ ι ]⁺⟨ vk ⟩ᴾ Q˙ =  P ⊢[ ι ]⁺⟨ vk ⟩[ par ] Q˙

_⊢[_]⁺⟨_⟩ᵀ[_]_ :
  Prop' ∞ →  Size →  Val/Ktxred T →  ℕ →  (Val T → Prop' ∞) →  Set₂
P ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ i ] Q˙ =  P ⊢[ ι ]⁺⟨ vk ⟩[ tot i ] Q˙

-- ⊢[ ]⟨ ⟩[ ] etc. :  Hoare triple over Expr

_⊢[_]⟨_⟩[_]_ :
  Prop' ∞ →  Size →  Expr ∞ T →  WpKind →  (Val T → Prop' ∞) →  Set₂
P ⊢[ ι ]⟨ e ⟩[ wκ ] Q˙ =  P ⊢[ ι ]⁺⟨ val/ktxred e ⟩[ wκ ] Q˙

_⊢[_]⟨_⟩ᴾ_ _⊢[<_]⟨_⟩ᴾ_ :
  Prop' ∞ →  Size →  Expr ∞ T →  (Val T → Prop' ∞) →  Set₂
P ⊢[ ι ]⟨ e ⟩ᴾ Q˙ =  P ⊢[ ι ]⟨ e ⟩[ par ] Q˙
P ⊢[< ι ]⟨ e ⟩ᴾ Q˙ =  Thunk (P ⊢[_]⟨ e ⟩[ par ] Q˙) ι

_⊢[_]⟨_⟩ᵀ[_]_ _⊢[<_]⟨_⟩ᵀ[_]_ :
  Prop' ∞ →  Size →  Expr ∞ T →  ℕ →  (Val T → Prop' ∞) →  Set₂
P ⊢[ ι ]⟨ e ⟩ᵀ[ i ] Q˙ =  P ⊢[ ι ]⟨ e ⟩[ tot i ] Q˙
P ⊢[< ι ]⟨ e ⟩ᵀ[ i ] Q˙ =  Thunk (P ⊢[_]⟨ e ⟩ᵀ[ i ] Q˙) ι

-- Pers :  Persistence of a proposition

record  Pers (P : Prop' ∞) :  Set₂  where
  inductive
  -- Pers-⇒□ :  P can turn into □ P
  field Pers-⇒□ :  P ⊢[ ι ] □ P
open Pers {{…}} public

private variable
  ł :  Level
  i j n :  ℕ
  X :  Set ł
  x :  X
  Y˙ :  X → Set ł
  Jr :  JudgRes
  P P' Q R :  Prop' ∞
  P˙ Q˙ R˙ :  X → Prop' ∞
  P˂ P'˂ Q˂ Q'˂ R˂ :  Prop˂ ∞
  Q˂˙ Q'˂˙ :  X → Prop˂ ∞
  P˂s :  List (Prop˂ ∞)
  wκ :  WpKind
  vk :  Val/Ktxred T
  e :  Expr ∞ U
  e˂ :  Expr˂ ∞ U
  e˙ :  X → Expr ∞ U
  K :  Ktx T U
  v :  Val T
  θ :  Addr
  p q :  ℚ⁺
  ᵗu ᵗv :  TyVal
  ᵗvs :  List TyVal

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

  choice₁ :  ∀{P˙˙ : ∀(x : X) → Y˙ x → Prop' ∞} →
    ∀₁ x , ∃₁ y , P˙˙ x y ⊢[ ι ] ∃₁ y˙ ∈ (∀ x → Y˙ x) , ∀₁ x , P˙˙ x (y˙ x)

  ------------------------------------------------------------------------------
  -- On →

  -- → is the right adjoint of ∧

  →-intro :  P ∧ Q ⊢[ ι ] R →  Q ⊢[ ι ] P →' R

  →-elim :  Q ⊢[ ι ] P →' R →  P ∧ Q ⊢[ ι ] R

  ------------------------------------------------------------------------------
  -- On ∗

  -- ∗ is unital with the unit ⊤', commutative, associative, and monotone with
  -- respect to ⊢

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
  -- On ⤇

  -- ⤇ is monadic :  monotone, increasing, and idempotent

  ⤇-mono :  P ⊢[ ι ] Q →  ⤇ P ⊢[ ι ] ⤇ Q

  ⤇-intro :  P ⊢[ ι ] ⤇ P

  ⤇-join :  ⤇ ⤇ P ⊢[ ι ] ⤇ P

  -- ∗ can get inside ⤇

  ⤇-eatˡ :  P ∗ ⤇ Q ⊢[ ι ] ⤇ (P ∗ Q)

  -- ∃ -, can get outside ⤇

  ⤇-∃-out :  ⤇ (∃₁ _ ∈ X , P) ⊢[ ι ] ∃₁ _ ∈ X , ⤇ P

  ------------------------------------------------------------------------------
  -- On □

  -- □ is comonadic :  monotone, decreasing, and idempotent

  □-mono :  P ⊢[ ι ] Q →  □ P ⊢[ ι ] □ Q

  □-elim :  □ P ⊢[ ι ] P

  □-dup :  □ P ⊢[ ι ] □ □ P

  -- ∧ can turn into ∗ when one argument is under □

  □ˡ-∧⇒∗ :  □ P ∧ Q ⊢[ ι ] □ P ∗ Q

  -- ∀ can get inside □

  ---- This can work also for ∀₀

  □-∀-in :  ∀₁˙ (□_ ∘ P˙) ⊢[ ι ] □ ∀₁˙ P˙

  -- ∃ can get outside □

  ---- This can work also for ∃₀

  □-∃-out :  □ ∃₁˙ P˙ ⊢[ ι ] ∃₁˙ (□_ ∘ P˙)

  ------------------------------------------------------------------------------
  -- On ⇛

  -- Increment the counter of ⇛ by 1

  ⇛-ṡ :  P ⊢[ ι ][ i ]⇛ Q →  P ⊢[ ι ][ ṡ i ]⇛ Q

  -- ⊢⇛ is reflexive, with removal of ⤇

  ⇛-refl-⤇ :  ⤇ P ⊢[ ι ][ i ]⇛ P

  -- ⊢⇛ is transitive

  _ᵘ»ᵘ_ :  P ⊢[ ι ][ i ]⇛ Q →  Q ⊢[ ι ][ i ]⇛ R →  P ⊢[ ι ][ i ]⇛ R

  -- ⊢⇛ can frame

  ⇛-frameˡ :  Q ⊢[ ι ][ i ]⇛ R →  P ∗ Q ⊢[ ι ][ i ]⇛ P ∗ R

  ------------------------------------------------------------------------------
  -- On ○

  -- ○ is monotone

  ○-mono :  P˂ .! ⊢[< ι ] Q˂ .! →  ○ P˂ ⊢[ ι ] ○ Q˂

  -- ○ can eat a basic proposition

  ○-eatˡ :  {{Basic Q}} →  Q ∗ ○ P˂ ⊢[ ι ] ○ ¡ (Q ∗ P˂ .!)

  -- ○ P can be obtained by allocating P

  ○-alloc :  P˂ .! ⊢[ ι ][ i ]⇛ ○ P˂

  -- When P is persistent, □ ○ P_i can be obtained recursively, i.e.,
  -- by allocating P minus the target □ ○ P

  -- This can be seen as an analog of Löb induction in step-indexed logics

  □○-alloc-rec :  □ ○ P˂ -∗ □ P˂ .! ⊢[ ι ][ i ]⇛ □ ○ P˂

  -- Use ○ P

  ○-use :  ○ P˂ ⊢[ ι ][ i ]⇛ P˂ .!

  ------------------------------------------------------------------------------
  -- On ↪⇛

  -- Modify ⇛ proof

  ↪⇛-ṡ :  P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P˂ ↪[ ṡ i ]⇛ Q˂

  ↪⇛-eatˡ⁻ˡᵘ :  {{Basic R}} →  R ∗ P'˂ .! ⊢[< ι ][ i ]⇛ P˂ .! →
                R ∗ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ]  P'˂ ↪[ i ]⇛ Q˂

  ↪⇛-eatˡ⁻ʳ :  {{Basic R}} →
    R ∗ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ]  P˂ ↪[ i ]⇛ ¡ (R ∗ Q˂ .!)

  ↪⇛-monoʳᵘ :  Q˂ .! ⊢[< ι ][ i ]⇛ Q'˂ .! →
               P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P˂ ↪[ i ]⇛ Q'˂

  ↪⇛-frameˡ :  P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  ¡ (R ∗ P˂ .!) ↪[ i ]⇛ ¡ (R ∗ Q˂ .!)

  -- Make ↪⇛ out of ○

  ○⇒↪⇛ :  P˂ .! ∗ R˂ .! ⊢[< ι ][ i ]⇛ Q˂ .! →  ○ R˂  ⊢[ ι ]  P˂ ↪[ i ]⇛ Q˂

  -- Use ↪⇛, with counter increment
  ---- Without that counter increment, we could do any super update
  ---- (⇛/↪⇛-use' in Syho.Logic.Paradox)

  ↪⇛-use :  P˂ .! ∗ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ][ ṡ i ]⇛  Q˂ .!

  ------------------------------------------------------------------------------
  -- On ↪⟨ ⟩ᴾ

  -- Modify ⟨ ⟩ᴾ proof

  ↪⟨⟩ᴾ-eatˡ⁻ˡᵘ :  {{Basic R}} →  (R ∗ P'˂ .! ⊢[< ι ][ i ]⇛ P˂ .!) →
                  R ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂˙)  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᴾ Q˂˙

  ↪⟨⟩ᴾ-eatˡ⁻ʳ :  {{Basic R}} →
    R ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂˙)  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ λ v → ¡ (R ∗ Q˂˙ v .!)

  ↪⟨⟩ᴾ-monoʳᵘ :  (∀ v →  Q˂˙ v .! ⊢[< ι ][ i ]⇛ Q'˂˙ v .!) →
                 P˂ ↪⟨ e ⟩ᴾ Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q'˂˙

  ↪⟨⟩ᴾ-frameˡ :  P˂ ↪⟨ e ⟩ᴾ Q˂˙  ⊢[ ι ]
                   ¡ (R ∗ P˂ .!) ↪⟨ e ⟩ᴾ λ v → ¡ (R ∗ Q˂˙ v .!)

  -- Make ↪⟨ ⟩ᴾ out of ○

  ○⇒↪⟨⟩ᴾ :  P˂ .! ∗ R˂ .! ⊢[< ι ]⟨ e ⟩ᴾ (λ v → Q˂˙ v .!) →
            ○ R˂  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q˂˙

  -- Use ↪⟨⟩ᴾ, with ▶ on the expression
  ---- Without that ▶, we could have any partial Hoare triple
  ---- (horᴾ/↪⟨⟩ᴾ-use' in Syho.Logic.Paradox)

  ↪⟨⟩ᴾ-use :  P˂ .! ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂˙)  ⊢[ ι ]⟨ ▶ ¡ e ⟩ᴾ  λ v → Q˂˙ v .!

  ------------------------------------------------------------------------------
  -- On ↪⟨ ⟩ᵀ

  -- Modify ⟨ ⟩ᵀ proof

  ↪⟨⟩ᵀ-ṡ :  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ ṡ i ] Q˂˙

  ↪⟨⟩ᵀ-eatˡ⁻ˡᵘ :  {{Basic R}} →  (R ∗ P'˂ .! ⊢[< ι ][ j ]⇛ P˂ .!) →
                  R ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙)  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙

  ↪⟨⟩ᵀ-eatˡ⁻ʳ :  {{Basic R}} →
    R ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙)  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] λ v → ¡ (R ∗ Q˂˙ v .!)

  ↪⟨⟩ᵀ-monoʳᵘ :  (∀ v →  Q˂˙ v .! ⊢[< ι ][ j ]⇛ Q'˂˙ v .!) →
                 P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q'˂˙

  ↪⟨⟩ᵀ-frameˡ :  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]
                   ¡ (R ∗ P˂ .!) ↪⟨ e ⟩ᵀ[ i ] λ v → ¡ (R ∗ Q˂˙ v .!)

  -- Make ↪⟨ ⟩ᵀ out of ○

  ○⇒↪⟨⟩ᵀ :  P˂ .! ∗ R˂ .! ⊢[< ι ]⟨ e ⟩ᵀ[ i ] (λ v → Q˂˙ v .!) →
            ○ R˂  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙

  -- Use ↪⟨⟩ᵀ, with counter increment
  ---- Without that counter increment, we could have any total Hoare triple
  ---- (horᵀ/↪⟨⟩ᵀ-use' in Syho.Logic.Paradox)

  ↪⟨⟩ᵀ-use :  P˂ .! ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙)
                ⊢[ ι ]⟨ e ⟩ᵀ[ ṡ i ]  λ v → Q˂˙ v .!

  ------------------------------------------------------------------------------
  -- On Hoare triple

  -- Weaken a Hoare triple from total to partial

  hor-ᵀ⇒ᴾ :  P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ i ]  Q˙  →   P  ⊢[ ι ]⁺⟨ vk ⟩ᴾ  Q˙

  -- Counter increment on total Hoare triple

  horᵀ-ṡ :  P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ i ]  Q˙  →   P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ ṡ i ]  Q˙

  -- Compose with a super update

  _ᵘ»ʰ_ :  P  ⊢[ ι ][ i ]⇛  Q  →   Q  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  R˙  →
           P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  R˙

  _ʰ»ᵘ_ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  Q˙  →   (∀ v →  Q˙ v  ⊢[ ι ][ i ]⇛  R˙ v)  →
           P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  R˙

  -- Frame

  hor-frameˡ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  Q˙  →
                R  ∗  P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  λ v →  R  ∗  Q˙ v

  -- Bind by a context

  hor-bind :  P  ⊢[ ι ]⟨ e ⟩[ wκ ]  Q˙  →
              (∀ v →  Q˙ v  ⊢[ ι ]⟨ K ᴷ◁ V⇒E v ⟩[ wκ ]  R˙) →
              P  ⊢[ ι ]⟨ K ᴷ◁ e ⟩[ wκ ]  R˙

  -- Value

  hor-valᵘ :  P  ⊢[ ι ][ i ]⇛  Q˙ v  →   P  ⊢[ ι ]⁺⟨ ĩ₀ v ⟩[ wκ ]  Q˙

  -- Non-deterministic value

  hor-nd :  (∀ x →  P  ⊢[ ι ]⟨ K ᴷ◁ ∇ x ⟩[ wκ ]  Q˙)  →
            P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| ndᴿ) ⟩[ wκ ]  Q˙

  -- ▶, for partial and total Hoare triples

  horᴾ-▶ :  P  ⊢[< ι ]⟨ K ᴷ◁ e˂ .! ⟩ᴾ  Q˙  →
            P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| ▶ᴿ e˂) ⟩ᴾ  Q˙

  horᵀ-▶ :  P  ⊢[ ι ]⟨ K ᴷ◁ e˂ .! ⟩ᵀ[ i ]  Q˙  →
            P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| ▶ᴿ e˂) ⟩ᵀ[ i ]  Q˙

  -- Application

  hor-◁ :  P  ⊢[ ι ]⟨ K ᴷ◁ e˙ x ⟩[ wκ ]  Q˙  →
           P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| e˙ ◁ᴿ x) ⟩[ wκ ]  Q˙

  -- Sequential execution

  hor-⁏ :  P  ⊢[ ι ]⟨ K ᴷ◁ e ⟩[ wκ ]  Q˙  →
           P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| v ⁏ᴿ e) ⟩[ wκ ]  Q˙

  ------------------------------------------------------------------------------
  -- On the memory

  -- Points-to tokens agree with the target value

  ↦⟨⟩-agree :  θ ↦⟨ p ⟩ ᵗu  ∗  θ ↦⟨ q ⟩ ᵗv  ⊢[ ι ]  ⌜ ᵗu ≡ ᵗv ⌝₁

  -- The fraction of the points-to token is no more than 1

  ↦⟨⟩-≤1 :  θ ↦⟨ p ⟩ ᵗv  ⊢[ ι ]  ⌜ p ≤1ᴿ⁺ ⌝₀

  -- Points-to tokens can be merged and split with respect to the fraction

  ↦⟨⟩-merge :  θ ↦⟨ p ⟩ ᵗv  ∗  θ ↦⟨ q ⟩ ᵗv  ⊢[ ι ]  θ ↦⟨ p +ᴿ⁺ q ⟩ ᵗv

  ↦⟨⟩-split :  θ ↦⟨ p +ᴿ⁺ q ⟩ ᵗv  ⊢[ ι ]  θ ↦⟨ p ⟩ ᵗv  ∗  θ ↦⟨ q ⟩ ᵗv

  -- Memory read

  hor-🞰 :  θ ↦⟨ p ⟩ (V , v)  ∗  P  ⊢[ ι ]⟨ K ᴷ◁ V⇒E v ⟩[ wκ ]  Q˙  →
           θ ↦⟨ p ⟩ (-, v)  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| 🞰ᴿ θ) ⟩[ wκ ]  Q˙

  -- Memory write

  hor-← :  θ ↦ (V , v)  ∗  P  ⊢[ ι ]⟨ K ᴷ◁ ∇ _ ⟩[ wκ ]  Q˙  →
           θ ↦ ᵗu  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| θ ←ᴿ v) ⟩[ wκ ]  Q˙

  -- Memory allocation

  hor-alloc :
    (∀ θ →  θ ↦ˡ rep n ⊤ṽ  ∗  Free n θ  ∗  P  ⊢[ ι ]⟨ K ᴷ◁ ∇ θ ⟩[ wκ ]  Q˙)  →
    P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| allocᴿ n) ⟩[ wκ ]  Q˙

  -- Memory freeing

  hor-free :  len ᵗvs ≡ n  →   P  ⊢[ ι ]⟨ K ᴷ◁ ∇ _ ⟩[ wκ ]  Q˙  →
    θ ↦ˡ ᵗvs  ∗  Free n θ  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| freeᴿ θ) ⟩[ wκ ]  Q˙
