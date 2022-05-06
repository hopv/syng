----------------------------------------------------------------------
-- Algebra utility
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Algebra where

open import Base.Level using (Level)

open import Relation.Binary using (IsEquivalence)
open IsEquivalence
open import Algebra using (Congruent₂;
  LeftIdentity; Identity; Commutative; Associative;
  IsCommutativeMonoid; CommutativeMonoid)
open import Data.Product using (_,_)
open import Base.Function using (_$_)

-- Convenient names
open import Algebra renaming (
  RightCongruent to Congruentˡ; LeftCongruent to Congruentʳ;
  Identity to Unit; LeftIdentity to Unitˡ; RightIdentity to Unitʳ) public

private variable
  ℓ ℓ≈ : Level
  A : Set ℓ
  _≈_ : A → A → Set ℓ≈
  _∙_ : A → A → A
  ε : A

equiv-comm-unitˡ⇒unit :
  IsEquivalence _≈_ → Commutative _≈_ _∙_ →
  Unitˡ _≈_ ε _∙_ → Unit _≈_ ε _∙_
equiv-comm-unitˡ⇒unit record{ trans = trans } comm unitˡ =
  unitˡ , λ _ → trans (comm _ _) $ unitˡ _

equiv-comm-congʳ⇒cong :
  IsEquivalence _≈_ → Commutative _≈_ _∙_ →
  Congruentˡ _≈_ _∙_ → Congruent₂ _≈_ _∙_
equiv-comm-congʳ⇒cong record{ trans = trans } comm congˡ a≈b c≈d =
  trans (congˡ a≈b) $ trans (comm _ _) $ trans (congˡ c≈d) $ comm _ _

make-IsCommutativeMonoid :
  IsEquivalence _≈_ → Congruentˡ _≈_ _∙_ →
  Unitˡ _≈_ ε _∙_ → Commutative _≈_ _∙_ → Associative _≈_ _∙_ →
  IsCommutativeMonoid _≈_ _∙_ ε
make-IsCommutativeMonoid equiv congˡ unitˡ comm assoc =
  record { comm = comm; isMonoid =
    record { identity = equiv-comm-unitˡ⇒unit equiv comm unitˡ; isSemigroup =
      record { assoc = assoc; isMagma =
        record { ∙-cong = equiv-comm-congʳ⇒cong equiv comm congˡ;
          isEquivalence = equiv } } } }
