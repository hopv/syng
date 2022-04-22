----------------------------------------------------------------------
-- Exclusive resource algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)
module Shog.Model.RA.Ex {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) where
open Setoid S renaming (Carrier to Car)

open import Level using (Level; 0ℓ; Lift)

open import Algebra using (Op₂; RightCongruent; Commutative; Associative)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel; _Respects_;
  IsEquivalence; Reflexive; Symmetric; Transitive)
open import Function.Base using (id)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)

open import Shog.Base.Algebra using (make-IsCommutativeMonoid)

----------------------------------------------------------------------
-- Ex : ExRA's carrier

data Ex : Set ℓ where
  -- pending
  ?ˣ : Ex
  -- the value is exclusively set
  !ˣ : Car → Ex
  -- invalid
  ↯ˣ : Ex

private variable
  a b : Car
  aˣ bˣ : Ex

----------------------------------------------------------------------
-- ≈ˣ : Equivalence over Ex

infix 4 _≈ˣ_
_≈ˣ_ : Rel Ex ℓ≈
?ˣ ≈ˣ ?ˣ = Lift _ ⊤
↯ˣ ≈ˣ ↯ˣ = Lift _ ⊤
!ˣ a ≈ˣ !ˣ b = a ≈ b
_ ≈ˣ _ = Lift _ ⊥

-- ≈ˣ is reflexive, symmetric and transitive

≈ˣ-refl : Reflexive _≈ˣ_
≈ˣ-refl {?ˣ} = _
≈ˣ-refl {↯ˣ} = _
≈ˣ-refl { !ˣ _} = refl

≈ˣ-sym : Symmetric _≈ˣ_
≈ˣ-sym {?ˣ} {?ˣ} = _
≈ˣ-sym {↯ˣ} {↯ˣ} = _
≈ˣ-sym { !ˣ _} { !ˣ _} = sym

≈ˣ-trans : Transitive _≈ˣ_
≈ˣ-trans {?ˣ} {?ˣ} {?ˣ} = _
≈ˣ-trans {↯ˣ} {↯ˣ} {↯ˣ} = _
≈ˣ-trans { !ˣ _} { !ˣ _} { !ˣ _} = trans

module _ where
  open IsEquivalence
  ≈ˣ-equiv : IsEquivalence _≈ˣ_
  ≈ˣ-equiv .refl {aˣ} = ≈ˣ-refl {aˣ}
  ≈ˣ-equiv .sym {aˣ} {bˣ} = ≈ˣ-sym {aˣ} {bˣ}
  ≈ˣ-equiv .trans {aˣ} {bˣ} {cˣ} = ≈ˣ-trans {aˣ} {bˣ} {cˣ}

----------------------------------------------------------------------
-- ✓ˣ : ExRA's validity

✓ˣ : Pred Ex 0ℓ
✓ˣ ↯ˣ = ⊥
✓ˣ _ = ⊤

----------------------------------------------------------------------
-- _∙ˣ_ : ExRA's product

infixl 7 _∙ˣ_
_∙ˣ_ : Op₂ Ex
?ˣ ∙ˣ aˣ = aˣ
↯ˣ ∙ˣ aˣ = ↯ˣ
aˣ ∙ˣ ?ˣ = aˣ
_ ∙ˣ _ = ↯ˣ

----------------------------------------------------------------------
-- Non-trivial lemmas on ExRA's operations

∙ˣ-congʳ : RightCongruent _≈ˣ_ _∙ˣ_
∙ˣ-congʳ {aˣ} {?ˣ} {?ˣ} _ = ≈ˣ-refl {aˣ}
∙ˣ-congʳ {_} {↯ˣ} {↯ˣ} _ = _
∙ˣ-congʳ {?ˣ} { !ˣ _} { !ˣ _} b≈c = b≈c
∙ˣ-congʳ {↯ˣ} { !ˣ _} { !ˣ _} _ = _
∙ˣ-congʳ { !ˣ _} { !ˣ _} { !ˣ _} _ = _

∙ˣ-comm : Commutative _≈ˣ_ _∙ˣ_
∙ˣ-comm ?ˣ ?ˣ = _
∙ˣ-comm ?ˣ ↯ˣ = _
∙ˣ-comm ?ˣ (!ˣ _) = refl
∙ˣ-comm ↯ˣ ?ˣ = _
∙ˣ-comm ↯ˣ ↯ˣ = _
∙ˣ-comm ↯ˣ (!ˣ _) = _
∙ˣ-comm (!ˣ _) ?ˣ = refl
∙ˣ-comm (!ˣ _) ↯ˣ = _
∙ˣ-comm (!ˣ _) (!ˣ _) = _

∙ˣ-assoc : Associative _≈ˣ_ _∙ˣ_
∙ˣ-assoc ?ˣ aˣ bˣ = ≈ˣ-refl {aˣ ∙ˣ bˣ}
∙ˣ-assoc ↯ˣ _ _ = _
∙ˣ-assoc (!ˣ a) ?ˣ bˣ = ≈ˣ-refl { !ˣ a ∙ˣ bˣ}
∙ˣ-assoc (!ˣ _) ↯ˣ bˣ = _
∙ˣ-assoc (!ˣ _) (!ˣ _) ?ˣ = _
∙ˣ-assoc (!ˣ _) (!ˣ _) ↯ˣ = _
∙ˣ-assoc (!ˣ _) (!ˣ _) (!ˣ _) = _

✓ˣ-resp : ✓ˣ Respects _≈ˣ_
✓ˣ-resp {?ˣ} {?ˣ} _ _ = _
✓ˣ-resp { !ˣ _} { !ˣ _} _ _ = _

✓ˣ-rem : ∀ (aˣ bˣ : Ex) → ✓ˣ (bˣ ∙ˣ aˣ) → ✓ˣ aˣ
✓ˣ-rem _ ?ˣ = id
✓ˣ-rem ?ˣ (!ˣ _) = _

----------------------------------------------------------------------
-- ExRA : Exclusive resource algebra

open import Shog.Model.RA using (RA)
open RA

ExRA : RA ℓ ℓ≈ 0ℓ

ExRA .Carrier = Ex
ExRA ._≈_ = _≈ˣ_
ExRA .✓ = ✓ˣ
ExRA ._∙_ = _∙ˣ_
ExRA .ε = ?ˣ
ExRA .⌞_⌟ _ = ?ˣ
ExRA .isCommutativeMonoid = make-IsCommutativeMonoid
  ≈ˣ-equiv (λ {aˣ} {bˣ} {cˣ} → ∙ˣ-congʳ {aˣ} {bˣ} {cˣ})
  (λ aˣ → ≈ˣ-refl {aˣ}) ∙ˣ-comm ∙ˣ-assoc
ExRA .✓-resp = ✓ˣ-resp
ExRA .✓-rem = ✓ˣ-rem
ExRA .⌞⌟-cong _ = _
ExRA .⌞⌟-add _ _ = ?ˣ , _
ExRA .⌞⌟-unitˡ aˣ = ≈ˣ-refl {aˣ}
ExRA .⌞⌟-idem = _

open RA ExRA renaming (_~>_ to _~>ˣ_)

----------------------------------------------------------------------
-- Update on ExRA

!ˣ-~> : !ˣ a ~>ˣ !ˣ b
!ˣ-~> ?ˣ = _
