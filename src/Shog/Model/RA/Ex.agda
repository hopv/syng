--------------------------------------------------------------------------------
-- Exclusive resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Setoid using (Setoid)
module Shog.Model.RA.Ex {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) {ℓ✓} where
open Setoid S renaming (Car to A)

open import Base.Level using (Level; 0ˡ)
open import Base.Func using (id)
open import Base.Prod using (_,_)
open import Base.Few using (⟨1⟩; ⟨0⟩)
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

--------------------------------------------------------------------------------
-- Internal definitions
private

  -- Equivalence
  infix 4 _≈ˣ_
  _≈ˣ_ : Ex → Ex → Set ℓ≈
  ?ˣ ≈ˣ ?ˣ  =  ⟨1⟩
  ↯ˣ ≈ˣ ↯ˣ  =  ⟨1⟩
  #ˣ a ≈ˣ #ˣ b  =  a ≈ b
  _ ≈ˣ _  =  ⟨0⟩

  -- Validity
  ✓ˣ : Ex → Set ℓ✓
  ✓ˣ ↯ˣ  =  ⟨0⟩
  ✓ˣ _  =  ⟨1⟩

  -- Product
  infixl 7 _∙ˣ_
  _∙ˣ_ : Ex → Ex → Ex
  ?ˣ ∙ˣ aˣ  =  aˣ
  ↯ˣ ∙ˣ aˣ  =  ↯ˣ
  aˣ ∙ˣ ?ˣ  =  aˣ
  _ ∙ˣ _  =  ↯ˣ

--------------------------------------------------------------------------------
-- Non-trivial lemmas
private abstract

  ≈ˣ-refl :  ∀ aˣ →  aˣ ≈ˣ aˣ
  ≈ˣ-refl ?ˣ  =  _
  ≈ˣ-refl ↯ˣ  =  _
  ≈ˣ-refl (#ˣ _)  =  refl˜

  ≈ˣ-sym :  ∀ aˣ bˣ →  aˣ ≈ˣ bˣ  →  bˣ ≈ˣ aˣ
  ≈ˣ-sym ?ˣ ?ˣ  =  _
  ≈ˣ-sym ↯ˣ ↯ˣ  =  _
  ≈ˣ-sym (#ˣ _) (#ˣ _)  =  sym˜

  ≈ˣ-trans :  ∀ aˣ bˣ cˣ →  aˣ ≈ˣ bˣ  →  bˣ ≈ˣ cˣ  →  aˣ ≈ˣ cˣ
  ≈ˣ-trans ?ˣ ?ˣ ?ˣ  =  _
  ≈ˣ-trans ↯ˣ ↯ˣ ↯ˣ  =  _
  ≈ˣ-trans (#ˣ _) (#ˣ _) (#ˣ _)  =  _»˜_

  ∙ˣ-congˡ :  ∀ aˣ bˣ cˣ →  aˣ ≈ˣ bˣ  →  aˣ ∙ˣ cˣ  ≈ˣ  bˣ ∙ˣ cˣ
  ∙ˣ-congˡ ?ˣ ?ˣ cˣ _  =  ≈ˣ-refl cˣ
  ∙ˣ-congˡ ↯ˣ ↯ˣ _ _  =  _
  ∙ˣ-congˡ (#ˣ a) (#ˣ b) ?ˣ a≈b  =  a≈b
  ∙ˣ-congˡ (#ˣ _) (#ˣ _) ↯ˣ _  =  _
  ∙ˣ-congˡ (#ˣ _) (#ˣ _) (#ˣ _) _  =  _

  ∙ˣ-comm :  ∀ aˣ bˣ →  aˣ ∙ˣ bˣ  ≈ˣ  bˣ ∙ˣ aˣ
  ∙ˣ-comm ?ˣ ?ˣ  =  _
  ∙ˣ-comm ?ˣ ↯ˣ  =  _
  ∙ˣ-comm ?ˣ (#ˣ _)  =  refl˜
  ∙ˣ-comm ↯ˣ ?ˣ  =  _
  ∙ˣ-comm ↯ˣ ↯ˣ  =  _
  ∙ˣ-comm ↯ˣ (#ˣ _)  =  _
  ∙ˣ-comm (#ˣ _) ?ˣ  =  refl˜
  ∙ˣ-comm (#ˣ _) ↯ˣ  =  _
  ∙ˣ-comm (#ˣ _) (#ˣ _)  =  _

  ∙ˣ-assocˡ :  ∀ aˣ bˣ cˣ →  (aˣ ∙ˣ bˣ) ∙ˣ cˣ  ≈ˣ  aˣ ∙ˣ (bˣ ∙ˣ cˣ)
  ∙ˣ-assocˡ ?ˣ aˣ bˣ  =  ≈ˣ-refl (aˣ ∙ˣ bˣ)
  ∙ˣ-assocˡ ↯ˣ _ _  =  _
  ∙ˣ-assocˡ (#ˣ a) ?ˣ bˣ  =  ≈ˣ-refl (#ˣ a ∙ˣ bˣ)
  ∙ˣ-assocˡ (#ˣ _) ↯ˣ bˣ  =  _
  ∙ˣ-assocˡ (#ˣ _) (#ˣ _) ?ˣ  =  _
  ∙ˣ-assocˡ (#ˣ _) (#ˣ _) ↯ˣ  =  _
  ∙ˣ-assocˡ (#ˣ _) (#ˣ _) (#ˣ _)  =  _

  ✓ˣ-resp :  ∀ aˣ bˣ →  aˣ ≈ˣ bˣ  →  ✓ˣ aˣ  →  ✓ˣ bˣ
  ✓ˣ-resp ?ˣ ?ˣ _ _  =  _
  ✓ˣ-resp (#ˣ _) (#ˣ _) _ _  =  _

  ✓ˣ-rem :  ∀ aˣ bˣ →  ✓ˣ (bˣ ∙ˣ aˣ) → ✓ˣ aˣ
  ✓ˣ-rem _ ?ˣ  =  id
  ✓ˣ-rem ?ˣ (#ˣ _)  =  _

--------------------------------------------------------------------------------
-- ExRA : Exclusive resource algebra

open RA

ExRA : RA ℓ ℓ≈ ℓ✓
ExRA .Car  =  Ex
ExRA ._≈_  =  _≈ˣ_
ExRA .✓  =  ✓ˣ
ExRA ._∙_  =  _∙ˣ_
ExRA .ε  =  ?ˣ
ExRA .⌞_⌟ _  =  ?ˣ
ExRA .refl˜ {aˣ}  =  ≈ˣ-refl aˣ
ExRA .sym˜ {aˣ}  =  ≈ˣ-sym aˣ _
ExRA ._»˜_ {aˣ}  =  ≈ˣ-trans aˣ _ _
ExRA .∙-congˡ {aˣ}  =  ∙ˣ-congˡ aˣ _ _
ExRA .∙-unitˡ {aˣ}  =  ≈ˣ-refl aˣ
ExRA .∙-comm {aˣ}  =  ∙ˣ-comm aˣ _
ExRA .∙-assocˡ {aˣ}  =  ∙ˣ-assocˡ aˣ _ _
ExRA .✓-resp  =  ✓ˣ-resp _ _
ExRA .✓-rem {aˣ} {bˣ}  =  ✓ˣ-rem aˣ bˣ
ExRA .✓-ε  =  _
ExRA .⌞⌟-cong  =  _
ExRA .⌞⌟-add  =  ?ˣ , _
ExRA .⌞⌟-unitˡ {aˣ}  =  ≈ˣ-refl aˣ
ExRA .⌞⌟-idem  =  _
