----------------------------------------------------------------------
-- Exclusive resource algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Shog.Model.RA.Ex where

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
-- Ex A : ExRA's carrier

data Ex {ℓ} (A : Set ℓ) : Set ℓ where
  -- pending
  ?ˣ : Ex A
  -- the value is exclusively set
  !ˣ : A → Ex A
  -- invalid
  ↯ˣ : Ex A

----------------------------------------------------------------------
-- ✓ˣ : ExRA's validity

✓ˣ : Ex A → Set
✓ˣ ↯ˣ = ⊥
✓ˣ _ = ⊤

----------------------------------------------------------------------
-- _∙ˣ_ : ExRA's product

infixl 7 _∙ˣ_
_∙ˣ_ : Ex A → Ex A → Ex A
?ˣ ∙ˣ aˣ = aˣ
↯ˣ ∙ˣ aˣ = ↯ˣ
aˣ ∙ˣ ?ˣ = aˣ
_ ∙ˣ _ = ↯ˣ

----------------------------------------------------------------------
-- Non-trivial lemmas for ExRA

private
  ✓ˣ-rem : ∀ (aˣ bˣ : Ex A) → ✓ˣ (bˣ ∙ˣ aˣ) → ✓ˣ aˣ
  ✓ˣ-rem _ ?ˣ = id
  ✓ˣ-rem ?ˣ (!ˣ _) = _

  ∙ˣ-comm : ∀ (aˣ bˣ : Ex A) → aˣ ∙ˣ bˣ ≡ bˣ ∙ˣ aˣ
  ∙ˣ-comm ?ˣ ?ˣ = refl
  ∙ˣ-comm ?ˣ (!ˣ _) = refl
  ∙ˣ-comm ?ˣ ↯ˣ = refl
  ∙ˣ-comm (!ˣ _) ?ˣ = refl
  ∙ˣ-comm (!ˣ _) (!ˣ _) = refl
  ∙ˣ-comm (!ˣ _) ↯ˣ = refl
  ∙ˣ-comm ↯ˣ ?ˣ = refl
  ∙ˣ-comm ↯ˣ (!ˣ _) = refl
  ∙ˣ-comm ↯ˣ ↯ˣ = refl

  ∙ˣ-assoc₀ : ∀ (aˣ bˣ cˣ : Ex A) → (aˣ ∙ˣ bˣ) ∙ˣ cˣ ≡ aˣ ∙ˣ (bˣ ∙ˣ cˣ)
  ∙ˣ-assoc₀ ?ˣ _ _ = refl
  ∙ˣ-assoc₀ (!ˣ _) ?ˣ _ = refl
  ∙ˣ-assoc₀ (!ˣ _) (!ˣ _) ?ˣ = refl
  ∙ˣ-assoc₀ (!ˣ _) (!ˣ _) (!ˣ _) = refl
  ∙ˣ-assoc₀ (!ˣ _) (!ˣ _) ↯ˣ = refl
  ∙ˣ-assoc₀ (!ˣ _) ↯ˣ _ = refl
  ∙ˣ-assoc₀ ↯ˣ _ _ = refl

----------------------------------------------------------------------
-- ExRA : Exclusive resource algebra

ExRA : Set ℓ → RA ℓ ℓ 0ℓ

ExRA A .Car = Ex A
ExRA A ._≈_ = _≡_
ExRA A .✓ = ✓ˣ
ExRA A ._∙_ = _∙ˣ_
ExRA A .ε = ?ˣ
ExRA A .⌞_⌟ _ = ?ˣ
ExRA A .idᵉ = refl
ExRA A .symᵉ = sym
ExRA A ._»ᵉ_ = trans
ExRA A .✓-cong refl = id
ExRA A .✓-rem {aˣ} {bˣ} = ✓ˣ-rem aˣ bˣ
ExRA A .∙-cong₀ refl = refl
ExRA A .∙-ε₀ = refl
ExRA A .∙-comm {aˣ} {bˣ} = ∙ˣ-comm aˣ bˣ
ExRA A .∙-assoc₀ {aˣ} {bˣ} {cˣ} = ∙ˣ-assoc₀ aˣ bˣ cˣ
ExRA A .⌞⌟-cong _ = refl
ExRA A .⌞⌟-add = ?ˣ , refl
ExRA A .⌞⌟-unit₀ = refl
ExRA A .⌞⌟-idem = refl

----------------------------------------------------------------------
-- Update on ExRA

!ˣ-~> : _~>_ (ExRA A) (!ˣ a) (!ˣ b)
!ˣ-~> {c = ?ˣ} = _
