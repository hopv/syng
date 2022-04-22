----------------------------------------------------------------------
-- Algebra utility
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

open import Relation.Binary using (Rel;
  IsEquivalence; Reflexive; Symmetric; Transitive)
open IsEquivalence
open import Algebra using (Op₂; RightCongruent; Congruent₂;
  LeftIdentity; Identity; Commutative; Associative;
  IsCommutativeMonoid; CommutativeMonoid)
open import Data.Product using (_,_)
open import Function.Base using (_$_)

module Shog.Base.Algebra where

private variable
  ℓ ℓ≈ : Level
  A : Set ℓ
  _≈_ : Rel A ℓ≈
  _∙_ : Op₂ A
  ε : A

equiv-comm-idˡ⇒id :
  IsEquivalence _≈_ → Commutative _≈_ _∙_ →
  LeftIdentity _≈_ ε _∙_ → Identity _≈_ ε _∙_
equiv-comm-idˡ⇒id record{ trans = trans } comm idˡ =
  idˡ , λ _ → trans (comm _ _) $ idˡ _

equiv-comm-congʳ⇒cong :
  IsEquivalence _≈_ → Commutative _≈_ _∙_ →
  RightCongruent _≈_ _∙_ → Congruent₂ _≈_ _∙_
equiv-comm-congʳ⇒cong record{ trans = trans } comm congʳ a≈b c≈d =
  trans (congʳ a≈b) $ trans (comm _ _) $ trans (congʳ c≈d) $ comm _ _

make-IsCommutativeMonoid :
  IsEquivalence _≈_ → RightCongruent _≈_ _∙_ →
  LeftIdentity _≈_ ε _∙_ → Commutative _≈_ _∙_ → Associative _≈_ _∙_ →
  IsCommutativeMonoid _≈_ _∙_ ε
make-IsCommutativeMonoid equiv congʳ idˡ comm assoc =
  record { comm = comm; isMonoid =
    record { identity = equiv-comm-idˡ⇒id equiv comm idˡ; isSemigroup =
      record { assoc = assoc; isMagma =
        record { ∙-cong = equiv-comm-congʳ⇒cong equiv comm congʳ;
          isEquivalence = equiv } } } }
