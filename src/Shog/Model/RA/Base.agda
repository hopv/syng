----------------------------------------------------------------------
-- Resource Algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Model.RA.Base where

open import Level using (Level; _⊔_; suc)
open import Size using (Size; ∞)

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (∃-syntax; _×_)

----------------------------------------------------------------------
-- Resource algebra
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
    -- Core, partial
    ⌞_⌟ : Car → Maybe Car
    ----------------------------------------------------------------------
    -- ≈ is reflexive, symmetric and transitive
    idᵉ : ∀ {a} → a ≈ a
    symm : ∀ {a b} → a ≈ b → b ≈ a
    _»ᵉ_ : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
    ----------------------------------------------------------------------
    -- ✓ preserves ≈
    ✓-cong : ∀ {a b} → a ≈ b → ✓ a → ✓ b
    -- ✓ is kept after a resource is removed
    ✓-rem : ∀ {a b} → ✓ (b ∙ a) → ✓ a
    ----------------------------------------------------------------------
    -- ∙ preserves ≈ and is commutative and associative
    ∙-cong₀ : ∀ {a b c} → a ≈ b → a ∙ c ≈ b ∙ c
    ∙-comm : ∀ {a b} → a ∙ b ≈ b ∙ a
    ∙-assoc₀ : ∀ {a b c} → (a ∙ b) ∙ c ≈ a ∙ (b ∙ c)
    ----------------------------------------------------------------------
    -- ⌞⌟ preserves ≈
    ⌞⌟-cong : ∀ {a b a'} → a ≈ b →
      ⌞ a ⌟ ≡ just a' → ∃[ b' ] ⌞ b ⌟ ≡ just b' × a' ≈ b'
    -- When ⌞⌟'s argument gets added, ⌞⌟'s result gets added
    ⌞⌟-add : ∀ {a a' b} → ⌞ a ⌟ ≡ just a' →
      ∃[ c' ] ⌞ b ∙ a ⌟ ≡ just c' × ∃[ b' ] b' ∙ a' ≈ c'
    -- ⌞ a ⌟ is absorbed by a
    ⌞⌟-unit₀ : ∀ {a a'} → ⌞ a ⌟ ≡ just a' → a' ∙ a ≈ a
    -- ⌞⌟ is idempotent
    ⌞⌟-idem : ∀ {a a'} → ⌞ a ⌟ ≡ just a' → ⌞ a' ⌟ ≡ just a'
