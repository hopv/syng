----------------------------------------------------------------------
-- Resource Algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Shog.Model.RA.Base where

open import Level using (Level; _⊔_; suc)

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (∃-syntax; _×_)

----------------------------------------------------------------------
-- Resource algebra (Unital)
record RA ℓ ℓ≈ ℓ✓ : Set (suc (ℓ ⊔ ℓ≈ ⊔ ℓ✓)) where
  infix 4 _≈_
  infixl 7 _∙_
  infixr -1 _»ᵉ_ -- the same fixity with _$_
  field
    -- Carrier
    Car : Set ℓ
    ----------------------------------------------------------------------
    -- Equivalence
    _≈_ : Car → Car → Set ℓ≈
    -- Validity
    ✓ : Car → Set ℓ✓
    -- Product
    _∙_ : Car → Car → Car
    -- Unit
    ε : Car
    -- Core
    ⌞_⌟ : Car → Car
    ----------------------------------------------------------------------
    -- ≈ is reflexive, symmetric and transitive
    idᵉ : ∀ {a} → a ≈ a
    symm : ∀ {a b} → a ≈ b → b ≈ a
    _»ᵉ_ : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
    ----------------------------------------------------------------------
    -- ✓ respects ≈
    ✓-cong : ∀ {a b} → a ≈ b → ✓ a → ✓ b
    -- ✓ is kept after a resource is removed
    ✓-rem : ∀ {a b} → ✓ (b ∙ a) → ✓ a
    ----------------------------------------------------------------------
    -- ∙ preserves ≈
    ∙-cong₀ : ∀ {a b c} → a ≈ b → a ∙ c ≈ b ∙ c
    -- ∙ is unital w.r.t. ε, commutative and associative
    ∙-ε₀ : ∀ {a} → ε ∙ a ≈ a
    ∙-comm : ∀ {a b} → a ∙ b ≈ b ∙ a
    ∙-assoc₀ : ∀ {a b c} → (a ∙ b) ∙ c ≈ a ∙ (b ∙ c)
    ----------------------------------------------------------------------
    -- ⌞⌟ preserves ≈
    ⌞⌟-cong : ∀ {a b} → a ≈ b → ⌞ a ⌟ ≈ ⌞ b ⌟
    -- When ⌞⌟'s argument gets added, ⌞⌟'s result gets added
    ⌞⌟-add : ∀ {a b} → ∃[ b' ] b' ∙ ⌞ a ⌟ ≈ ⌞ b ∙ a ⌟
    -- ⌞ a ⌟ is absorbed by a
    ⌞⌟-unit₀ : ∀ {a} → ⌞ a ⌟ ∙ a ≈ a
    -- ⌞⌟ is idempotent
    ⌞⌟-idem : ∀ {a} → ⌞ ⌞ a ⌟ ⌟ ≈ ⌞ a ⌟
