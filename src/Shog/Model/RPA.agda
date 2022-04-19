----------------------------------------------------------------------
-- Resource pre-ordered Algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Model.RPA where

open import Level using (Level; _⊔_; suc)
open import Size using (Size; ∞)

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (∃-syntax; _×_)

----------------------------------------------------------------------
-- Resource pre-ordered algebra
record RPA ℓ ℓ≤ ℓ✓ : Set (suc (ℓ ⊔ ℓ≤ ⊔ ℓ✓)) where
  infix 6 _≤_
  infixl 7 _∙_
  infixr -1 _»ʳ_ -- the same fixity with _$_
  field
    -- carrier
    ⌞_⌟ : Set ℓ
    ----------------------------------------------------------------------
    -- pre-order
    _≤_ : ⌞_⌟ → ⌞_⌟ → Set ℓ≤
    -- validity
    ✓ : ⌞_⌟ → Set ℓ✓
    -- product
    _∙_ : ⌞_⌟ → ⌞_⌟ → ⌞_⌟
    -- core, partial
    ‖_‖ : ⌞_⌟ → Maybe ⌞_⌟
    ----------------------------------------------------------------------
    -- ≤ is reflexive and transitive
    idʳ : ∀ {a} → a ≤ a
    _»ʳ_ : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    ----------------------------------------------------------------------
    -- ✓, ∙ and ‖‖ are monotone
    ✓-mono : ∀ {a b} → b ≤ a → ✓ a → ✓ b
    ∙-mono₀ : ∀ {a b c} → a ≤ b → a ∙ c ≤ b ∙ c
    ‖‖-mono : ∀ {a b b'} → a ≤ b →
      ‖ b ‖ ≡ just b' → ∃[ a' ] ‖ a ‖ ≡ just a' × a' ≤ b'
    ----------------------------------------------------------------------
    -- ∙ is commutative and associative
    ∙-comm : ∀ {a b} → a ∙ b ≤ b ∙ a
    ∙-assoc₀ : ∀ {a b c} → (a ∙ b) ∙ c ≤ a ∙ (b ∙ c)
    -- ∙ is increasing
    ∙-incr : ∀ {a b} → a ≤ b ∙ a
    ----------------------------------------------------------------------
    -- ‖ a ‖ is unital with respect to a
    ‖‖-unit : ∀ {a a'} → ‖ a ‖ ≡ just a' → a' ∙ a ≤ a
    -- ‖ ‖ is idempotent
    ‖‖-idem : ∀ {a a'} → ‖ a ‖ ≡ just a' → ‖ a' ‖ ≡ just a'
