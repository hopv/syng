----------------------------------------------------------------------
-- Exclusive resource algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Shog.Model.RA.Excl {ℓ} (A : Set ℓ) where

open import Shog.Model.RA.Base using (RA)
open RA

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Function.Base using (id)
open import Data.Product using (_,_)

data Excl : Set ℓ where
  ?ˣ : Excl -- pending
  !ˣ : A → Excl -- exclusively register
  ↯ˣ : Excl -- invalid

data ✓ˣ : Excl → Set ℓ where
  ?ˣ-✓ : ✓ˣ ?ˣ
  !ˣ-✓ : ∀ {a} → ✓ˣ (!ˣ a)

private

  infixl 7 _∙ˣ_
  _∙ˣ_ : Excl → Excl → Excl
  ?ˣ ∙ˣ a = a
  ↯ˣ ∙ˣ a = ↯ˣ
  a ∙ˣ ?ˣ = a
  _ ∙ˣ _ = ↯ˣ

  ✓ˣ-rem : ∀ a b → ✓ˣ (b ∙ˣ a) → ✓ˣ a
  ✓ˣ-rem _ ?ˣ ✓a = ✓a
  ✓ˣ-rem ?ˣ (!ˣ _) _ = ?ˣ-✓

  ∙ˣ-comm : ∀ a b → a ∙ˣ b ≡ b ∙ˣ a
  ∙ˣ-comm ?ˣ ?ˣ = refl
  ∙ˣ-comm ?ˣ (!ˣ _) = refl
  ∙ˣ-comm ?ˣ ↯ˣ = refl
  ∙ˣ-comm (!ˣ _) ?ˣ = refl
  ∙ˣ-comm (!ˣ _) (!ˣ _) = refl
  ∙ˣ-comm (!ˣ _) ↯ˣ = refl
  ∙ˣ-comm ↯ˣ ?ˣ = refl
  ∙ˣ-comm ↯ˣ (!ˣ _) = refl
  ∙ˣ-comm ↯ˣ ↯ˣ = refl

  ∙ˣ-assoc₀ : ∀ a b c → (a ∙ˣ b) ∙ˣ c ≡ a ∙ˣ (b ∙ˣ c)
  ∙ˣ-assoc₀ ?ˣ _ _ = refl
  ∙ˣ-assoc₀ (!ˣ _) ?ˣ _ = refl
  ∙ˣ-assoc₀ (!ˣ _) (!ˣ _) ?ˣ = refl
  ∙ˣ-assoc₀ (!ˣ _) (!ˣ _) (!ˣ _) = refl
  ∙ˣ-assoc₀ (!ˣ _) (!ˣ _) ↯ˣ = refl
  ∙ˣ-assoc₀ (!ˣ _) ↯ˣ _ = refl
  ∙ˣ-assoc₀ ↯ˣ _ _ = refl

ExclRA : RA ℓ ℓ ℓ

ExclRA .Car = Excl
ExclRA ._≈_ = _≡_
ExclRA .✓ = ✓ˣ
ExclRA ._∙_ = _∙ˣ_
ExclRA .ε = ?ˣ
ExclRA .⌞_⌟ _ = ?ˣ
ExclRA .idᵉ = refl
ExclRA .symᵉ = sym
ExclRA ._»ᵉ_ = trans
ExclRA .✓-cong refl = id
ExclRA .✓-rem {a = a} {b = b} = ✓ˣ-rem a b
ExclRA .∙-cong₀ refl = refl
ExclRA .∙-ε₀ = refl
ExclRA .∙-comm {a = a} {b = b} = ∙ˣ-comm a b
ExclRA .∙-assoc₀ {a = a} {b = b} {c = c} = ∙ˣ-assoc₀ a b c
ExclRA .⌞⌟-cong _ = refl
ExclRA .⌞⌟-add = ?ˣ , refl
ExclRA .⌞⌟-unit₀ = refl
ExclRA .⌞⌟-idem = refl

open import Shog.Model.RA.Derived ExclRA public

!ˣ-~> : ∀{a b} → !ˣ a ~> !ˣ b
!ˣ-~> {c = ?ˣ} _ = !ˣ-✓
