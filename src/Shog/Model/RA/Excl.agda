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

data Excl {ℓ} (A : Set ℓ) : Set ℓ where
  ?ˣ : Excl A -- pending
  !ˣ : A → Excl A -- exclusively register
  ↯ˣ : Excl A -- invalid

data ✓ˣ (A : Set ℓ) : Excl A → Set ℓ where
  ?ˣ-✓ : ✓ˣ A ?ˣ
  !ˣ-✓ : ∀ {a} → ✓ˣ A (!ˣ a)

infixl 7 _∙ˣ_
_∙ˣ_ : Excl A → Excl A → Excl A
?ˣ ∙ˣ aˣ = aˣ
↯ˣ ∙ˣ aˣ = ↯ˣ
aˣ ∙ˣ ?ˣ = aˣ
_ ∙ˣ _ = ↯ˣ

private
  ✓ˣ-rem : ∀ aˣ bˣ → ✓ˣ A (bˣ ∙ˣ aˣ) → ✓ˣ A aˣ
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

ExclRA : Set ℓ → RA ℓ ℓ ℓ

ExclRA A .Car = Excl A
ExclRA A ._≈_ = _≡_
ExclRA A .✓ = ✓ˣ A
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

!ˣ-~> : ∀{a b : A} → _~>_ (ExclRA A) (!ˣ a) (!ˣ b)
!ˣ-~> {c = ?ˣ} _ = !ˣ-✓
