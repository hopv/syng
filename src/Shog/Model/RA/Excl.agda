----------------------------------------------------------------------
-- Exclusive resource algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Shog.Model.RA.Excl where

open import Level using (Level)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Function.Base using (id)
open import Data.Product using (_,_)

open import Shog.Model.RA using (RA)
open RA

private variable
  ℓ : Level
  A : Set ℓ


----------------------------------------------------------------------
-- Excl A : ExclRA's carrier

data Excl {ℓ} (A : Set ℓ) : Set ℓ where
  -- pending
  ?ˣ : Excl A
  -- the value is exclusively set
  !ˣ : A → Excl A
  -- invalid
  ↯ˣ : Excl A

----------------------------------------------------------------------
-- ✓ˣ : ExclRA's validity

data ✓ˣ {A : Set ℓ} : Excl A → Set ℓ where
  ?ˣ-✓ : ✓ˣ ?ˣ
  !ˣ-✓ : ∀ {a} → ✓ˣ (!ˣ a)

----------------------------------------------------------------------
-- _∙ˣ_ : ExclRA's product

infixl 7 _∙ˣ_
_∙ˣ_ : Excl A → Excl A → Excl A
?ˣ ∙ˣ aˣ = aˣ
↯ˣ ∙ˣ aˣ = ↯ˣ
aˣ ∙ˣ ?ˣ = aˣ
_ ∙ˣ _ = ↯ˣ

----------------------------------------------------------------------
-- Non-trivial lemmas for ExclRA

private
  ✓ˣ-rem : ∀ (aˣ bˣ : Excl A) → ✓ˣ (bˣ ∙ˣ aˣ) → ✓ˣ aˣ
  ✓ˣ-rem _ ?ˣ ✓aˣ = ✓aˣ
  ✓ˣ-rem ?ˣ (!ˣ _) _ = ?ˣ-✓

  ∙ˣ-comm : ∀ (aˣ bˣ : Excl A) → aˣ ∙ˣ bˣ ≡ bˣ ∙ˣ aˣ
  ∙ˣ-comm ?ˣ ?ˣ = refl
  ∙ˣ-comm ?ˣ (!ˣ _) = refl
  ∙ˣ-comm ?ˣ ↯ˣ = refl
  ∙ˣ-comm (!ˣ _) ?ˣ = refl
  ∙ˣ-comm (!ˣ _) (!ˣ _) = refl
  ∙ˣ-comm (!ˣ _) ↯ˣ = refl
  ∙ˣ-comm ↯ˣ ?ˣ = refl
  ∙ˣ-comm ↯ˣ (!ˣ _) = refl
  ∙ˣ-comm ↯ˣ ↯ˣ = refl

  ∙ˣ-assoc₀ : ∀ (aˣ bˣ cˣ : Excl A) → (aˣ ∙ˣ bˣ) ∙ˣ cˣ ≡ aˣ ∙ˣ (bˣ ∙ˣ cˣ)
  ∙ˣ-assoc₀ ?ˣ _ _ = refl
  ∙ˣ-assoc₀ (!ˣ _) ?ˣ _ = refl
  ∙ˣ-assoc₀ (!ˣ _) (!ˣ _) ?ˣ = refl
  ∙ˣ-assoc₀ (!ˣ _) (!ˣ _) (!ˣ _) = refl
  ∙ˣ-assoc₀ (!ˣ _) (!ˣ _) ↯ˣ = refl
  ∙ˣ-assoc₀ (!ˣ _) ↯ˣ _ = refl
  ∙ˣ-assoc₀ ↯ˣ _ _ = refl

----------------------------------------------------------------------
-- ExclRA : Exclusive resource algebra

ExclRA : Set ℓ → RA ℓ ℓ ℓ

ExclRA A .Car = Excl A
ExclRA A ._≈_ = _≡_
ExclRA A .✓ = ✓ˣ
ExclRA A ._∙_ = _∙ˣ_
ExclRA A .ε = ?ˣ
ExclRA A .⌞_⌟ _ = ?ˣ
ExclRA A .idᵉ = refl
ExclRA A .symᵉ = sym
ExclRA A ._»ᵉ_ = trans
ExclRA A .✓-cong refl = id
ExclRA A .✓-rem {a = aˣ} {b = bˣ} = ✓ˣ-rem aˣ bˣ
ExclRA A .∙-cong₀ refl = refl
ExclRA A .∙-ε₀ = refl
ExclRA A .∙-comm {a = aˣ} {b = bˣ} = ∙ˣ-comm aˣ bˣ
ExclRA A .∙-assoc₀ {a = aˣ} {b = bˣ} {c = cˣ} = ∙ˣ-assoc₀ aˣ bˣ cˣ
ExclRA A .⌞⌟-cong _ = refl
ExclRA A .⌞⌟-add = ?ˣ , refl
ExclRA A .⌞⌟-unit₀ = refl
ExclRA A .⌞⌟-idem = refl

----------------------------------------------------------------------
-- Update on ExclRA

!ˣ-~> : ∀{a b : A} → _~>_ (ExclRA A) (!ˣ a) (!ˣ b)
!ˣ-~> {c = ?ˣ} _ = !ˣ-✓
