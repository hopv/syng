--------------------------------------------------------------------------------
-- Proposition
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syng.Logic.Prop where

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
open import Syng.Lang.Expr using (Addr; _ₒ_; Type; Expr∞; Val; TyVal)
open import Syng.Lang.Ktxred using (Redex)

--------------------------------------------------------------------------------
-- HorKind :  Hoare kind

data  HorKind :  Set₀  where
  -- Partial
  par :  HorKind
  -- Total, with a level
  tot :  ℕ →  HorKind

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
-- SProp :  Separation-logic proposition

data  SProp (ι : 𝕊) :  Set₁

-- SProp˂ :  SProp under Thunk
SProp˂ :  𝕊 →  Set₁
SProp˂ ι =  Thunk SProp ι

-- Utility for ∞

SProp∞ SProp˂∞ :  Set₁
SProp∞ =  SProp ∞
SProp˂∞ =  SProp˂ ∞

private variable
  ι :  𝕊
  X :  Set₀
  P˙ :  X → SProp∞
  P Q :  SProp∞
  n o :  ℕ
  θ :  Addr
  p :  ℚ⁺
  ᵗv :  TyVal
  T :  Type
  Nm :  Name → Zoi
  nm :  Name
  α :  Lft

infix 3 ⤇_ _→'_ _-∗_
infixr 5 _⊸[_]⇛_ _⊸[_]ᵃ⟨_⟩_ _⊸⟨_⟩[_]_ _⊸[_]⟨_⟩∞
infixr 7 _∗_
infix 8 □_ ○_ †ᴸ_ &ⁱ⟨_⟩_ ⅋ⁱ⟨_⟩_ &ᵐ⟨_⟩_ ⅋ᵐ⟨_⟩_ ⟨†_⟩_ #ᵁᵇ⟨_⟩_ ≤ᵁᵇ⟨_⟩_
infix 9 _↦⟨_⟩_


data  SProp ι  where

  -- It is important that basic connectives are inductive
  -- If we relax it (in some way), we get the liar paradox (⇒⊥/¬ᶜ in
  -- Syng.Logic.Paradox)

  -- ∀˙, ∃˙ :  Universal/existential quantification over any type X in Set₀,
  --           which does not include SProp ι itself (predicativity)

  -- If we add impredicative quantification (as well as lifting of a judgment),
  -- a paradox arises ([^nm]ᴺ-no/∃ᴾ in Syng.Logic.Paradox)

  ∀˙ ∃˙ :  (X → SProp ι) →  SProp ι

  -- →' :  Implication
  _→'_ :  SProp ι →  SProp ι →  SProp ι

  -- ∗ :  Separating conjunction
  _∗_ :  SProp ι →  SProp ι →  SProp ι

  -- -∗ :  Magic wand
  _-∗_ :  SProp ι →  SProp ι →  SProp ι

  -- ⤇ :  Basic update modality
  ⤇_ :  SProp ι →  SProp ι

  -- □ :  Persistence modality
  □_ :  SProp ι →  SProp ι

  -- [ ]ᴺ :  Name set token
  [_]ᴺ :  (Name → Zoi) →  SProp ι

  -- ↦⟨ ⟩ :  Points-to token
  _↦⟨_⟩_ :  Addr →  ℚ⁺ →  TyVal →  SProp ι

  -- Free :  Freeing token
  Free :  ℕ →  Addr →  SProp ι

  -- ○ :  Indirection modality
  ○_ :  SProp˂ ι →  SProp ι

  -- ⊸[ ]⇛ :  Fancy update precursor, with a level
  _⊸[_]⇛_ :  SProp˂ ι →  ℕ →  SProp˂ ι →  SProp ι

  -- ⊸[ ]ᵃ⟨ ⟩ :  Atomic Hoare triple precursor, with a level
  _⊸[_]ᵃ⟨_⟩_ :  SProp˂ ι →  ℕ →  Redex T →  (Val T → SProp˂ ι) →  SProp ι

  -- ⊸⟨ ⟩[ ] :  Common Hoare triple precursor
  _⊸⟨_⟩[_]_ :  SProp˂ ι →  Expr∞ T →  HorKind →  (Val T → SProp˂ ι) →  SProp ι

  -- ⊸[ ]⟨ ⟩∞ :  Infinite Hoare triple precursor, with a level
  _⊸[_]⟨_⟩∞ :  SProp˂ ι →  ℕ →  Expr∞ T →  SProp ι

  -- &ⁱ⟨ ⟩ :  Invariant token
  &ⁱ⟨_⟩_ :  Name →  SProp˂ ι →  SProp ι

  -- ⅋ⁱ⟨ ⟩ :  Open invariant token
  ⅋ⁱ⟨_⟩_ :  Name →  SProp˂ ι →  SProp ι

  -- [ ]ᴸ⟨ ⟩ :  Lifetime token
  [_]ᴸ⟨_⟩ :  Lft →  ℚ⁺ →  SProp ι

  -- †ᴸ :  Dead lifetime token
  †ᴸ_ :  Lft →  SProp ι

  -- &ᵐ :  Mutable borrow token

  &ᵐ⟨_⟩_ :  Lft →  SProp˂ ι →  SProp ι

  -- ⅋ᵐ :  Open mutable borrow token

  ⅋ᵐ⟨_⟩_ :  Lft × ℚ⁺ →  SProp˂ ι →  SProp ι

  -- ⟨† ⟩ :  Lender token

  ⟨†_⟩_ :  Lft →  SProp˂ ι →  SProp ι

  -- Upper boundee token

  #ᵁᵇ⟨_⟩_ :  ℕ →  ℕ →  SProp ι

  -- Upper bound token

  ≤ᵁᵇ⟨_⟩_ :  ℕ →  ℕ →  SProp ι

-- ¡ᴾ :  SProp into SProp˂

infix 8 ¡ᴾ_
¡ᴾ_ :  SProp ι →  SProp˂ ι
(¡ᴾ P) .! =  P

--------------------------------------------------------------------------------
-- Utility for ∀/∃

∀∈-syntax ∃∈-syntax ∀-syntax ∃-syntax :  (X → SProp ι) →  SProp ι
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

_∧_ _∨_ :  SProp ι →  SProp ι →  SProp ι
P ∧ Q =  ∀˙ (binary P Q)
P ∨ Q =  ∃˙ (binary P Q)

--------------------------------------------------------------------------------
-- ⊤' :  Truth
-- ⊥' :  Falsehood

⊤' ⊥' :  SProp ι
⊤' =  ∀˙ absurd
⊥' =  ∃˙ absurd

-- ¬' :  Negation

infix 3 ¬'_
¬'_ :  SProp ι →  SProp ι
¬' P =  P →' ⊥'

--------------------------------------------------------------------------------
-- ⌜ ⌝∧, ⌜ ⌝→, ⌜ ⌝ :  Set embedding

infix 3 ⌜_⌝∧_ ⌜_⌝→_
⌜_⌝∧_ ⌜_⌝→_ :  Set₀ →  SProp ι →  SProp ι
⌜ X ⌝∧ P =  ∃ _ ∈ X , P
⌜ X ⌝→ P =  ∀' _ ∈ X , P

⌜_⌝ :  Set₀ →  SProp ι
⌜ X ⌝ =  ⌜ X ⌝∧ ⊤'

--------------------------------------------------------------------------------
-- [∗] :  Iterated separating conjunction

[∗] :  List (SProp ι) →  SProp ι
[∗] [] =  ⊤'
[∗] (P ∷ Ps) =  P ∗ [∗] Ps

-- Syntax for [∗] $ᴸ / $ⁱᴸ

infix 8 [∗∈]-syntax [∗∈ⁱ]-syntax [∗∈ⁱ⟨⟩]-syntax
[∗∈] [∗∈]-syntax :  (X → SProp ι) →  List X →  SProp ι
[∗∈] P˙ xs =  [∗] $ P˙ $ᴸ xs
[∗∈]-syntax =  [∗∈]
[∗∈ⁱ] [∗∈ⁱ]-syntax :  (ℕ × X → SProp ι) →  List X →  SProp ι
[∗∈ⁱ] P˙ xs =  [∗] $ curry P˙ $ⁱᴸ xs
[∗∈ⁱ]-syntax =  [∗∈ⁱ]
[∗∈ⁱ⟨⟩] [∗∈ⁱ⟨⟩]-syntax :  (ℕ × X → SProp ι) →  ℕ →  List X →  SProp ι
[∗∈ⁱ⟨⟩] P˙ k xs =  [∗] $ curry P˙ $ⁱᴸ⟨ k ⟩ xs
[∗∈ⁱ⟨⟩]-syntax =  [∗∈ⁱ⟨⟩]
syntax [∗∈]-syntax (λ x → P) xs =  [∗ x ∈ xs ] P
syntax [∗∈ⁱ]-syntax (λ ix → P) xs =  [∗ ix ∈ⁱ xs ] P
syntax [∗∈ⁱ⟨⟩]-syntax (λ ix → P) k xs =  [∗ ix ∈ⁱ⟨ k ⟩ xs ] P

--------------------------------------------------------------------------------
-- Utility for [ ]ᴺ

-- [⊤]ᴺ :  Universal name set token

[⊤]ᴺ :  SProp ι
[⊤]ᴺ =  [ ⊤ᶻ ]ᴺ

-- [^ ]ᴺ :  Name token

[^_]ᴺ :  Name →  SProp ι
[^ nm ]ᴺ =  [ ^ᶻ nm ]ᴺ

abstract

  -- ^ᶻ-✔ for Name

  ^ᶻᴺ-✔ :  ✔ᶻ ^ᶻ nm
  ^ᶻᴺ-✔ =  ^ᶻ-✔

--------------------------------------------------------------------------------
-- Extend _↦⟨_⟩_

infix 9 _↦_ _↦ᴸ⟨_⟩_ _↦ᴸ_

-- Full points-to token
_↦_ :  Addr →  TyVal →  SProp ι
θ ↦ ᵗv =  θ ↦⟨ 1ᴿ⁺ ⟩ ᵗv

-- Iterated points-to token
_↦ᴸ⟨_⟩_ :  Addr →  ℚ⁺ →  List TyVal →  SProp ι
θ ↦ᴸ⟨ p ⟩ ᵗvs =  [∗ (i , ᵗv) ∈ⁱ ᵗvs ] θ ₒ i ↦⟨ p ⟩ ᵗv
_↦ᴸ_ :  Addr →  List TyVal →  SProp ι
θ ↦ᴸ ᵗvs =  θ ↦ᴸ⟨ 1ᴿ⁺ ⟩ ᵗvs

--------------------------------------------------------------------------------
-- ⊸⟨ ⟩ᴾ, ⊸⟨ ⟩ᵀ[ ] :  Partial/total Hoare triple precursor

infixr 5 _⊸⟨_⟩ᴾ_ _⊸⟨_⟩ᵀ[_]_

_⊸⟨_⟩ᴾ_ :  SProp˂ ι →  Expr∞ T →  (Val T → SProp˂ ι) →  SProp ι
P ⊸⟨ e ⟩ᴾ Q˙ =  P ⊸⟨ e ⟩[ par ] Q˙

_⊸⟨_⟩ᵀ[_]_ :  SProp˂ ι →  Expr∞ T →  ℕ →  (Val T → SProp˂ ι) →  SProp ι
P ⊸⟨ e ⟩ᵀ[ i ] Q˙ =  P ⊸⟨ e ⟩[ tot i ] Q˙

--------------------------------------------------------------------------------
-- Static reference

static :  Name
static =  strnm "static"

-- ↦ⁱ :  Points-to token under an invariant

infix 9 _↦ⁱ_
_↦ⁱ_ :  Addr →  TyVal →  SProp ι
θ ↦ⁱ ᵗv =  &ⁱ⟨ static ⟩ ¡ᴾ θ ↦ ᵗv

--------------------------------------------------------------------------------
-- [ ]ᴸ :  Full lifetime token

[_]ᴸ :  Lft →  SProp ι
[ α ]ᴸ =  [ α ]ᴸ⟨ 1ᴿ⁺ ⟩

--------------------------------------------------------------------------------
-- Basic P :  P is basic, i.e., P doesn't contain propositional connectives

data  Basic :  SProp∞ →  Set₁  where

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
