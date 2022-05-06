--------------------------------------------------------------------------------
-- Defining Ex and ExRA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)
module Shog.Model.RA.Ex.Base {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) where
open Setoid S renaming (Carrier to A)

open import Base.Level using (Level; 0ˡ)
open import Algebra using (Commutative; Associative)
open import Relation.Binary using (_Respects_; IsEquivalence)
open import Base.Function using (id)
open import Data.Product using (_,_)
open import Base.NElem using (⟨1⟩; ⟨0⟩)
open import Base.Algebra using (make-IsCommutativeMonoid)
open import Shog.Model.RA using (RA)

--------------------------------------------------------------------------------
-- Ex : ExRA's carrier

data Ex : Set ℓ where
  -- pending
  ?ˣ : Ex
  -- the value is exclusively set
  #ˣ : A → Ex
  -- invalid
  ↯ˣ : Ex

private

  ------------------------------------------------------------------------------
  -- Internal definitions

  -- Equivalence
  infix 4 _≈ˣ_
  _≈ˣ_ : Ex → Ex → Set ℓ≈
  ?ˣ ≈ˣ ?ˣ  =  ⟨1⟩
  ↯ˣ ≈ˣ ↯ˣ  =  ⟨1⟩
  #ˣ a ≈ˣ #ˣ b  =  a ≈ b
  _ ≈ˣ _  =  ⟨0⟩

  -- Validity
  ✓ˣ : Ex → Set 0ˡ
  ✓ˣ ↯ˣ  =  ⟨0⟩
  ✓ˣ _  =  ⟨1⟩

  -- Product
  infixl 7 _∙ˣ_
  _∙ˣ_ : Ex → Ex → Ex
  ?ˣ ∙ˣ aˣ  =  aˣ
  ↯ˣ ∙ˣ aˣ  =  ↯ˣ
  aˣ ∙ˣ ?ˣ  =  aˣ
  _ ∙ˣ _  =  ↯ˣ

  ------------------------------------------------------------------------------
  -- Non-trivial lemmas

  ≈ˣ-refl :  ∀ aˣ →  aˣ ≈ˣ aˣ
  ≈ˣ-refl ?ˣ  =  _
  ≈ˣ-refl ↯ˣ  =  _
  ≈ˣ-refl (#ˣ _)  =  refl

  ≈ˣ-sym :  ∀ aˣ bˣ →  aˣ ≈ˣ bˣ  →  bˣ ≈ˣ aˣ
  ≈ˣ-sym ?ˣ ?ˣ  =  _
  ≈ˣ-sym ↯ˣ ↯ˣ  =  _
  ≈ˣ-sym (#ˣ _) (#ˣ _)  =  sym

  ≈ˣ-trans :  ∀ aˣ bˣ cˣ →  aˣ ≈ˣ bˣ  →  bˣ ≈ˣ cˣ  →  aˣ ≈ˣ cˣ
  ≈ˣ-trans ?ˣ ?ˣ ?ˣ  =  _
  ≈ˣ-trans ↯ˣ ↯ˣ ↯ˣ  =  _
  ≈ˣ-trans (#ˣ _) (#ˣ _) (#ˣ _)  =  trans

  module _ where
    open IsEquivalence
    ≈ˣ-equiv : IsEquivalence _≈ˣ_
    ≈ˣ-equiv .refl {aˣ}  =  ≈ˣ-refl aˣ
    ≈ˣ-equiv .sym {aˣ} {bˣ}  =  ≈ˣ-sym aˣ bˣ
    ≈ˣ-equiv .trans {aˣ} {bˣ} {cˣ}  =  ≈ˣ-trans aˣ bˣ cˣ

  ∙ˣ-congˡ :  ∀ aˣ bˣ cˣ →  aˣ ≈ˣ bˣ  →  aˣ ∙ˣ cˣ  ≈ˣ  bˣ ∙ˣ cˣ
  ∙ˣ-congˡ ?ˣ ?ˣ cˣ _  =  ≈ˣ-refl cˣ
  ∙ˣ-congˡ ↯ˣ ↯ˣ _ _  =  _
  ∙ˣ-congˡ (#ˣ a) (#ˣ b) ?ˣ a≈b  =  a≈b
  ∙ˣ-congˡ (#ˣ _) (#ˣ _) ↯ˣ _  =  _
  ∙ˣ-congˡ (#ˣ _) (#ˣ _) (#ˣ _) _  =  _

  ∙ˣ-comm :  ∀ aˣ bˣ →  aˣ ∙ˣ bˣ  ≈ˣ  bˣ ∙ˣ aˣ
  ∙ˣ-comm ?ˣ ?ˣ  =  _
  ∙ˣ-comm ?ˣ ↯ˣ  =  _
  ∙ˣ-comm ?ˣ (#ˣ _)  =  refl
  ∙ˣ-comm ↯ˣ ?ˣ  =  _
  ∙ˣ-comm ↯ˣ ↯ˣ  =  _
  ∙ˣ-comm ↯ˣ (#ˣ _)  =  _
  ∙ˣ-comm (#ˣ _) ?ˣ  =  refl
  ∙ˣ-comm (#ˣ _) ↯ˣ  =  _
  ∙ˣ-comm (#ˣ _) (#ˣ _)  =  _

  ∙ˣ-assoc :  ∀ aˣ bˣ cˣ →  (aˣ ∙ˣ bˣ) ∙ˣ cˣ  ≈ˣ  aˣ ∙ˣ (bˣ ∙ˣ cˣ)
  ∙ˣ-assoc ?ˣ aˣ bˣ  =  ≈ˣ-refl (aˣ ∙ˣ bˣ)
  ∙ˣ-assoc ↯ˣ _ _  =  _
  ∙ˣ-assoc (#ˣ a) ?ˣ bˣ  =  ≈ˣ-refl (#ˣ a ∙ˣ bˣ)
  ∙ˣ-assoc (#ˣ _) ↯ˣ bˣ  =  _
  ∙ˣ-assoc (#ˣ _) (#ˣ _) ?ˣ  =  _
  ∙ˣ-assoc (#ˣ _) (#ˣ _) ↯ˣ  =  _
  ∙ˣ-assoc (#ˣ _) (#ˣ _) (#ˣ _)  =  _

  ✓ˣ-resp :  ∀ aˣ bˣ →  aˣ ≈ˣ bˣ  →  ✓ˣ aˣ  →  ✓ˣ bˣ
  ✓ˣ-resp ?ˣ ?ˣ _ _  =  _
  ✓ˣ-resp (#ˣ _) (#ˣ _) _ _  =  _

  ✓ˣ-rem :  ∀ aˣ bˣ →  ✓ˣ (bˣ ∙ˣ aˣ) → ✓ˣ aˣ
  ✓ˣ-rem _ ?ˣ  =  id
  ✓ˣ-rem ?ˣ (#ˣ _)  =  _

--------------------------------------------------------------------------------
-- ExRA : Exclusive resource algebra

open RA

ExRA : RA ℓ ℓ≈ 0ˡ
ExRA .Carrier  =  Ex
ExRA ._≈_  =  _≈ˣ_
ExRA .✓  =  ✓ˣ
ExRA ._∙_  =  _∙ˣ_
ExRA .ε  =  ?ˣ
ExRA .⌞_⌟ _  =  ?ˣ
ExRA .isCommutativeMonoid  =  make-IsCommutativeMonoid ≈ˣ-equiv
  (λ {cˣ} {aˣ} {bˣ} → ∙ˣ-congˡ aˣ bˣ cˣ) ≈ˣ-refl ∙ˣ-comm ∙ˣ-assoc
ExRA .✓-resp  =  ✓ˣ-resp _ _
ExRA .✓-rem {aˣ} {bˣ}  =  ✓ˣ-rem aˣ bˣ
ExRA .✓-ε  =  _
ExRA .⌞⌟-cong  =  _
ExRA .⌞⌟-add  =  ?ˣ , _
ExRA .⌞⌟-unitˡ {aˣ}  =  ≈ˣ-refl aˣ
ExRA .⌞⌟-idem  =  _
