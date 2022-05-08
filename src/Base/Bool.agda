--------------------------------------------------------------------------------
-- Booleans
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Bool where

open import Base.Level using (Level)
open import Base.Few using (⟨1⟩; ⟨0⟩)

--------------------------------------------------------------------------------
-- Bool: Boolean

open import Agda.Builtin.Bool public using (Bool)
  renaming (true to tt; false to ff)

private variable
  ℓ : Level
  A : Set ℓ
  b c d : Bool

-- Negation

not : Bool → Bool
not tt = ff
not ff = tt

-- Conjunction

infixr 6 _&&_
_&&_ : Bool → Bool → Bool
tt && b = b
ff && b = ff

-- Disjunction

infixr 5 _||_
_||_ : Bool → Bool → Bool
tt || b = tt
ff || b = b

-- Exclusive Or

infixr 5 _xor_
_xor_ : Bool → Bool → Bool
tt xor b = not b
ff xor b = b

-- If then else

infix 0 if_then_else_
if_then_else_ : Bool → A → A → A
if tt then aᵗ else aᶠ = aᵗ
if ff then aᵗ else aᶠ = aᶠ

-- Bool to Set

Tt : Bool → Set
Tt tt = ⟨1⟩
Tt ff = ⟨0⟩

--------------------------------------------------------------------------------
-- ≤ᵇ: Comparison of Booleans

infix 4 _≤ᵇ_
data _≤ᵇ_ : Bool → Bool → Set where
  ff≤tt : ff ≤ᵇ tt
  ≤ᵇ-refl : ∀ {b} → b ≤ᵇ b
open _≤ᵇ_ public

abstract

  -- ≤ᵇ is transitive

  ≤ᵇ-trans : b ≤ᵇ c → c ≤ᵇ d → b ≤ᵇ d
  ≤ᵇ-trans ≤ᵇ-refl c≤d = c≤d
  ≤ᵇ-trans ff≤tt ≤ᵇ-refl = ff≤tt
