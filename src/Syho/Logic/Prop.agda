--------------------------------------------------------------------------------
-- Proposition
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Prop where

open import Base.Func using (_$_; _∘_; it)
open import Base.Few using (binary; absurd)
open import Base.Size using (𝕊; ∞; Thunk; ¡_; !)
open import Base.Prod using (_×_; _,_; curry)
open import Base.Sum using (_⨿_; ĩ₀_)
open import Base.Zoi using (Zoi; ✔ᶻ_; ⊤ᶻ; ^ᶻ_; ^ᶻ-✔)
open import Base.Nat using (ℕ)
open import Base.List using (List; []; _∷_; [_]; _$ᴸ_; _$ⁱᴸ_; _$ⁱᴸ⟨_⟩_)
open import Base.Str using (Str)
open import Base.Ratp using (ℚ⁺; 1ᴿ⁺)
open import Syho.Lang.Expr using (Addr; _ₒ_; Type; Expr∞; Val; TyVal)
open import Syho.Lang.Ktxred using (Redex)

--------------------------------------------------------------------------------
-- WpKind :  Weakest precondion kind

data  WpKind :  Set₀  where
  -- Partial
  par :  WpKind
  -- Total, with a level
  tot :  ℕ →  WpKind

--------------------------------------------------------------------------------
-- Name :  Name of invariants
--         We can choose any type with decidable equality;
--         we choose here List (Str ⨿ ℕ) for good expressivity

Name :  Set₀
Name =  List (Str ⨿ ℕ)

-- Name by a single string

strnm :  Str →  Name
strnm s =  [ ĩ₀ s ]

--------------------------------------------------------------------------------
-- Lft :  Lifetime

Lft :  Set₀
Lft =  ℕ

--------------------------------------------------------------------------------
-- Prop' :  Proposition

data  Prop' (ι : 𝕊) :  Set₁

-- Prop˂ :  Prop' under Thunk
Prop˂ :  𝕊 →  Set₁
Prop˂ ι =  Thunk Prop' ι

-- Utility for ∞

Prop∞ Prop˂∞ :  Set₁
Prop∞ =  Prop' ∞
Prop˂∞ =  Prop˂ ∞

private variable
  ι :  𝕊
  X :  Set₀
  P˙ :  X → Prop∞
  P Q :  Prop∞
  n o :  ℕ
  θ :  Addr
  p :  ℚ⁺
  ᵗv :  TyVal
  T :  Type
  Nm :  Name → Zoi
  nm :  Name
  α :  Lft

infix 3 ⤇_ _→'_ _-∗_
infixr 5 _↪[_]⇛_ _↪[_]ᵃ⟨_⟩_ _↪⟨_⟩[_]_ _↪[_]⟨_⟩∞
infixr 7 _∗_
infix 8 □_ ○_ †ᴸ_ &ⁱ⟨_⟩_ %ⁱ⟨_⟩_ ⟨†_⟩_ &ᵐ⟨_⟩_ %ᵐ⟨_⟩_ #ᵁᵇ⟨_⟩_ ≤ᵁᵇ⟨_⟩_
infix 9 _↦⟨_⟩_


data  Prop' ι  where

  -- ∀˙, ∃˙ :  Universal/existential quantification over any type X in Set₀,
  --           which does not include Prop' ι itself (predicativity)
  ∀˙ ∃˙ :  (X → Prop' ι) →  Prop' ι

  -- →' :  Implication
  _→'_ :  Prop' ι →  Prop' ι →  Prop' ι

  -- ∗ :  Separating conjunction
  _∗_ :  Prop' ι →  Prop' ι →  Prop' ι

  -- -∗ :  Magic wand
  _-∗_ :  Prop' ι →  Prop' ι →  Prop' ι

  -- ⤇ :  Update modality
  ⤇_ :  Prop' ι →  Prop' ι

  -- □ :  Persistence modality
  □_ :  Prop' ι →  Prop' ι

  -- [ ]ᴺ :  Name set token
  [_]ᴺ :  (Name → Zoi) →  Prop' ι

  -- ↦⟨ ⟩ :  Points-to token
  _↦⟨_⟩_ :  Addr →  ℚ⁺ →  TyVal →  Prop' ι

  -- Free :  Freeing token
  Free :  ℕ →  Addr →  Prop' ι

  -- ○ :  Indirection modality
  ○_ :  Prop˂ ι →  Prop' ι

  -- ↪[ ]⇛ :  Super-update precursor, with a level
  _↪[_]⇛_ :  Prop˂ ι →  ℕ →  Prop˂ ι →  Prop' ι

  -- ↪[ ]ᵃ⟨ ⟩ :  Atomic Hoare-triple precursor, with a level
  _↪[_]ᵃ⟨_⟩_ :  Prop˂ ι →  ℕ →  Redex T →  (Val T → Prop˂ ι) →  Prop' ι

  -- ↪⟨ ⟩[ ] :  Hoare-triple precursor
  _↪⟨_⟩[_]_ :  Prop˂ ι →  Expr∞ T →  WpKind →  (Val T → Prop˂ ι) →  Prop' ι

  -- ↪[ ]⟨ ⟩∞ :  Infinite Hoare-triple precursor, with a level
  _↪[_]⟨_⟩∞ :  Prop˂ ι →  ℕ →  Expr∞ T →  Prop' ι

  -- &ⁱ⟨ ⟩ :  Invariant token
  &ⁱ⟨_⟩_ :  Name →  Prop˂ ι →  Prop' ι

  -- %ⁱ⟨ ⟩ :  Open invariant token
  %ⁱ⟨_⟩_ :  Name →  Prop˂ ι →  Prop' ι

  -- [ ]ᴸ⟨ ⟩ :  Lifetime token
  [_]ᴸ⟨_⟩ :  Lft →  ℚ⁺ →  Prop' ι

  -- †ᴸ :  Dead lifetime token
  †ᴸ_ :  Lft →  Prop' ι

  -- ⟨† ⟩ :  Lender token

  ⟨†_⟩_ :  Lft →  Prop˂ ι →  Prop' ι

  -- &ᵐ :  Mutable borrow token

  &ᵐ⟨_⟩_ :  Lft →  Prop˂ ι →  Prop' ι

  -- %ᵐ :  Open mutable borrow token

  %ᵐ⟨_⟩_ :  Lft × ℚ⁺ →  Prop˂ ι →  Prop' ι

  -- Upper-boundee token

  #ᵁᵇ⟨_⟩_ :  ℕ →  ℕ →  Prop' ι

  -- Upper-bound token

  ≤ᵁᵇ⟨_⟩_ :  ℕ →  ℕ →  Prop' ι

-- ¡ᴾ :  Prop' into Prop˂

infix 8 ¡ᴾ_
¡ᴾ_ :  Prop' ι →  Prop˂ ι
(¡ᴾ P) .! =  P

--------------------------------------------------------------------------------
-- Utility for ∀/∃

∀∈-syntax ∃∈-syntax ∀-syntax ∃-syntax :  (X → Prop' ι) →  Prop' ι
∀∈-syntax =  ∀˙
∃∈-syntax =  ∃˙
∀-syntax =  ∀˙
∃-syntax =  ∃˙

infix 3 ∀∈-syntax ∃∈-syntax ∀-syntax ∃-syntax
  ∀∈-syntax ∃∈-syntax ∀-syntax ∃-syntax
syntax ∀∈-syntax {X = X} (λ x → P) =  ∀' x ∈ X , P
syntax ∃∈-syntax {X = X} (λ x → P) =  ∃ x ∈ X , P
syntax ∀-syntax (λ x → P) =  ∀' x , P
syntax ∃-syntax (λ x → P) =  ∃ x , P

--------------------------------------------------------------------------------
-- ∧ :  Conjunction
-- ∨ :  Disjunction

infixr 7 _∧_
infixr 6 _∨_

_∧_ _∨_ :  Prop' ι →  Prop' ι →  Prop' ι
P ∧ Q =  ∀˙ (binary P Q)
P ∨ Q =  ∃˙ (binary P Q)

--------------------------------------------------------------------------------
-- ⊤' :  Truth
-- ⊥' :  Falsehood

⊤' ⊥' :  Prop' ι
⊤' =  ∀˙ absurd
⊥' =  ∃˙ absurd

--------------------------------------------------------------------------------
-- ⌜ ⌝∧, ⌜ ⌝→, ⌜ ⌝ :  Set embedding

infix 3 ⌜_⌝∧_ ⌜_⌝→_
⌜_⌝∧_ ⌜_⌝→_ :  Set₀ →  Prop' ι →  Prop' ι
⌜ X ⌝∧ P =  ∃ _ ∈ X , P
⌜ X ⌝→ P =  ∀' _ ∈ X , P

⌜_⌝ :  Set₀ →  Prop' ι
⌜ X ⌝ =  ⌜ X ⌝∧ ⊤'

--------------------------------------------------------------------------------
-- [∗] :  Iterated separating conjunction

[∗] :  List (Prop' ι) →  Prop' ι
[∗] [] =  ⊤'
[∗] (P ∷ Ps) =  P ∗ [∗] Ps

-- Syntax for [∗] $ᴸ / $ⁱᴸ

infix 8 [∗∈]-syntax [∗∈ⁱ]-syntax [∗∈ⁱ⟨⟩]-syntax
[∗∈] [∗∈]-syntax :  (X → Prop' ι) →  List X →  Prop' ι
[∗∈] P˙ xs =  [∗] $ P˙ $ᴸ xs
[∗∈]-syntax =  [∗∈]
[∗∈ⁱ] [∗∈ⁱ]-syntax :  (ℕ × X → Prop' ι) →  List X →  Prop' ι
[∗∈ⁱ] P˙ xs =  [∗] $ curry P˙ $ⁱᴸ xs
[∗∈ⁱ]-syntax =  [∗∈ⁱ]
[∗∈ⁱ⟨⟩] [∗∈ⁱ⟨⟩]-syntax :  (ℕ × X → Prop' ι) →  ℕ →  List X →  Prop' ι
[∗∈ⁱ⟨⟩] P˙ k xs =  [∗] $ curry P˙ $ⁱᴸ⟨ k ⟩ xs
[∗∈ⁱ⟨⟩]-syntax =  [∗∈ⁱ⟨⟩]
syntax [∗∈]-syntax (λ x → P) xs =  [∗ x ∈ xs ] P
syntax [∗∈ⁱ]-syntax (λ ix → P) xs =  [∗ ix ∈ⁱ xs ] P
syntax [∗∈ⁱ⟨⟩]-syntax (λ ix → P) k xs =  [∗ ix ∈ⁱ⟨ k ⟩ xs ] P

--------------------------------------------------------------------------------
-- Utility for [ ]ᴺ

-- [⊤]ᴺ :  Universal name set token

[⊤]ᴺ :  Prop' ι
[⊤]ᴺ =  [ ⊤ᶻ ]ᴺ

-- [^ ]ᴺ :  Name token

[^_]ᴺ :  Name →  Prop' ι
[^ nm ]ᴺ =  [ ^ᶻ nm ]ᴺ

abstract

  -- ^ᶻ-✔ for Name

  ^ᶻᴺ-✔ :  ✔ᶻ ^ᶻ nm
  ^ᶻᴺ-✔ =  ^ᶻ-✔

--------------------------------------------------------------------------------
-- Extend _↦⟨_⟩_

infix 9 _↦_ _↦ᴸ⟨_⟩_ _↦ᴸ_

-- Full points-to token
_↦_ :  Addr →  TyVal →  Prop' ι
θ ↦ ᵗv =  θ ↦⟨ 1ᴿ⁺ ⟩ ᵗv

-- Iterated points-to token
_↦ᴸ⟨_⟩_ :  Addr →  ℚ⁺ →  List TyVal →  Prop' ι
θ ↦ᴸ⟨ p ⟩ ᵗvs =  [∗ (i , ᵗv) ∈ⁱ ᵗvs ] θ ₒ i ↦⟨ p ⟩ ᵗv
_↦ᴸ_ :  Addr →  List TyVal →  Prop' ι
θ ↦ᴸ ᵗvs =  θ ↦ᴸ⟨ 1ᴿ⁺ ⟩ ᵗvs

--------------------------------------------------------------------------------
-- ↪⟨ ⟩ᴾ, ↪⟨ ⟩ᵀ[ ] :  Partial/total Hoare-triple precursor

infixr 5 _↪⟨_⟩ᴾ_ _↪⟨_⟩ᵀ[_]_

_↪⟨_⟩ᴾ_ :  Prop˂ ι →  Expr∞ T →  (Val T → Prop˂ ι) →  Prop' ι
P ↪⟨ e ⟩ᴾ Q˙ =  P ↪⟨ e ⟩[ par ] Q˙

_↪⟨_⟩ᵀ[_]_ :  Prop˂ ι →  Expr∞ T →  ℕ →  (Val T → Prop˂ ι) →  Prop' ι
P ↪⟨ e ⟩ᵀ[ i ] Q˙ =  P ↪⟨ e ⟩[ tot i ] Q˙

------------------------------------------------------------------------------
-- Static reference

static :  Name
static =  strnm "static"

-- ↦ⁱ :  Points-to token under an invariant

infix 9 _↦ⁱ_
_↦ⁱ_ :  Addr →  TyVal →  Prop' ι
θ ↦ⁱ ᵗv =  &ⁱ⟨ static ⟩ ¡ᴾ θ ↦ ᵗv

--------------------------------------------------------------------------------
-- [ ]ᴸ :  Full lifetime token

[_]ᴸ :  Lft →  Prop' ι
[ α ]ᴸ =  [ α ]ᴸ⟨ 1ᴿ⁺ ⟩

--------------------------------------------------------------------------------
-- Basic P :  P is basic, i.e., P doesn't contain impredicative connectives

data  Basic :  Prop∞ →  Set₁  where

  -- They are not instances, because unfortunately Agda can't search a
  -- universally quantified instance (∀ x → …)

  ∀-Basic :  (∀ x → Basic $ P˙ x) →  Basic $ ∀˙ P˙
  ∃-Basic :  (∀ x → Basic $ P˙ x) →  Basic $ ∃˙ P˙

  -- Instance data constructors
  instance

    →-Basic :  {{Basic P}} →  {{Basic Q}} →  Basic $ P →' Q
    ∗-Basic :  {{Basic P}} →  {{Basic Q}} →  Basic $ P ∗ Q
    -∗-Basic :  {{Basic P}} →  {{Basic Q}} →  Basic $ P -∗ Q
    ⤇-Basic :  {{Basic P}} →  Basic $ ⤇ P
    □-Basic :  {{Basic P}} →  Basic $ □ P
    []ᴺ-Basic :  Basic [ Nm ]ᴺ
    ↦⟨⟩-Basic :  Basic $ θ ↦⟨ p ⟩ ᵗv
    Free-Basic :  Basic $ Free n θ
    []ᴸ⟨⟩-Basic :  Basic [ α ]ᴸ⟨ p ⟩
    †ᴸ-Basic :  Basic $ †ᴸ α
    #ᵁᵇ-Basic :  Basic $ #ᵁᵇ⟨ o ⟩ n
    ≤ᵁᵇ-Basic :  Basic $ ≤ᵁᵇ⟨ o ⟩ n

instance

  -- For ∧/∨/⊤'/⊥'

  ∧-Basic :  {{Basic P}} →  {{Basic Q}} →  Basic $ P ∧ Q
  ∧-Basic =  ∀-Basic $ binary it it

  ∨-Basic :  {{Basic P}} →  {{Basic Q}} →  Basic $ P ∨ Q
  ∨-Basic =  ∃-Basic $ binary it it

  ⊤-Basic :  Basic ⊤'
  ⊤-Basic =  ∀-Basic absurd

  ⊥-Basic :  Basic ⊥'
  ⊥-Basic =  ∃-Basic absurd

  -- For ⌜ ⌝

  ⌜⌝-Basic :  Basic ⌜ X ⌝
  ⌜⌝-Basic =  ∃-Basic λ _ → ⊤-Basic
