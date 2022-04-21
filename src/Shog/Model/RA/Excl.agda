----------------------------------------------------------------------
-- Exclusive resource algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Shog.Model.RA.Excl where

open import Level using (Level; 0ℓ)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Function.Base using (id)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)

open import Shog.Model.RA using (RA)
open RA

private variable
  ℓ : Level
  A : Set ℓ
  a b : A

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

✓ˣ : Excl A → Set
✓ˣ ↯ˣ = ⊥
✓ˣ _ = ⊤

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
  ✓ˣ-rem _ ?ˣ = id
  ✓ˣ-rem ?ˣ (!ˣ _) = _

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

ExclRA : Set ℓ → RA ℓ ℓ 0ℓ

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
ExclRA A .✓-rem {aˣ} {bˣ} = ✓ˣ-rem aˣ bˣ
ExclRA A .∙-cong₀ refl = refl
ExclRA A .∙-ε₀ = refl
ExclRA A .∙-comm {aˣ} {bˣ} = ∙ˣ-comm aˣ bˣ
ExclRA A .∙-assoc₀ {aˣ} {bˣ} {cˣ} = ∙ˣ-assoc₀ aˣ bˣ cˣ
ExclRA A .⌞⌟-cong _ = refl
ExclRA A .⌞⌟-add = ?ˣ , refl
ExclRA A .⌞⌟-unit₀ = refl
ExclRA A .⌞⌟-idem = refl

----------------------------------------------------------------------
-- Update on ExclRA

!ˣ-~> : _~>_ (ExclRA A) (!ˣ a) (!ˣ b)
!ˣ-~> {c = ?ˣ} = _
