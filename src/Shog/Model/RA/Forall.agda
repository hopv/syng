----------------------------------------------------------------------
-- Dependent-function resource algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Shog.Model.RA.Forall where

open import Level using (_⊔_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary using (Decidable; IsEquivalence; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to refl≡)
open import Algebra using (Congruent₁)
open import Data.Product using (_,_; proj₁; proj₂)
open import Shog.Base.Algebra using (make-IsCommutativeMonoid)
open import Shog.Model.RA using (RA)

----------------------------------------------------------------------
-- ∀ᴿᴬ: Dependent-function resource algebra

module _ {ℓ' ℓ ℓ≈ ℓ✓} {A : Set ℓ'} (Ra˙ : A → RA ℓ ℓ≈ ℓ✓) where
  open IsEquivalence renaming (refl to refl'; sym to sym'; trans to trans')
  open RA

  ∀ᴿᴬ : RA (ℓ' ⊔ ℓ) (ℓ' ⊔ ℓ≈) (ℓ' ⊔ ℓ✓)
  ∀ᴿᴬ .Carrier = ∀ a → Ra˙ a .Carrier
  ∀ᴿᴬ ._≈_ x˙ y˙ = ∀ a → Ra˙ a ._≈_ (x˙ a) (y˙ a)
  ∀ᴿᴬ .✓ x˙ = ∀ a → Ra˙ a .✓ (x˙ a)
  ∀ᴿᴬ ._∙_ x˙ y˙ a = Ra˙ a ._∙_ (x˙ a) (y˙ a)
  ∀ᴿᴬ .ε a = Ra˙ a .ε
  ∀ᴿᴬ .⌞_⌟ x˙ a = Ra˙ a .⌞_⌟ (x˙ a)
  ∀ᴿᴬ .isCommutativeMonoid = make-IsCommutativeMonoid
    (λ{ .refl' a → Ra˙ a .refl; .sym' x˙≈y˙ a → Ra˙ a .sym (x˙≈y˙ a);
      .trans' x˙≈y˙ y˙≈z˙ a →  Ra˙ a .trans (x˙≈y˙ a) (y˙≈z˙ a) })
    (λ x˙≈y˙ a → ∙-congˡ (Ra˙ a) (x˙≈y˙ a)) (λ _ a → unitˡ (Ra˙ a))
    (λ _ _ a → comm (Ra˙ a)) (λ _ _ _ a → assocˡ (Ra˙ a))
  ∀ᴿᴬ .✓-resp x˙≈y˙ ✓x˙ a = Ra˙ a .✓-resp (x˙≈y˙ a) (✓x˙ a)
  ∀ᴿᴬ .✓-rem ✓y˙∙x˙ a = Ra˙ a .✓-rem (✓y˙∙x˙ a)
  ∀ᴿᴬ .⌞⌟-cong x˙≈y˙ a = Ra˙ a .⌞⌟-cong (x˙≈y˙ a)
  ∀ᴿᴬ .⌞⌟-add = (λ a → Ra˙ a .⌞⌟-add .proj₁) , λ a → Ra˙ a .⌞⌟-add .proj₂
  ∀ᴿᴬ .⌞⌟-unitˡ a = Ra˙ a .⌞⌟-unitˡ
  ∀ᴿᴬ .⌞⌟-idem a = Ra˙ a .⌞⌟-idem
  ∀ᴿᴬ .⌞⌟-ε a = Ra˙ a .⌞⌟-ε

----------------------------------------------------------------------
-- On ∀ᴿᴬ

module _ {ℓ' ℓ ℓ≈ ℓ✓} {A : Set ℓ'} {Ra˙ : A → RA ℓ ℓ≈ ℓ✓}
  (_≟_ : Decidable {A = A} _≡_) where

  open RA
  open RA (∀ᴿᴬ Ra˙) using () renaming (Carrier to Carrier∀; _≈_ to _≈∀_;
    _∙_ to _∙∀_; ε to ε∀; ⌞_⌟ to ⌞_⌟∀)

  --------------------------------------------------------------------
  -- Injecting an element of a component RA

  inj : ∀ a → Ra˙ a .Carrier → Carrier∀
  inj a x b with a ≟ b
  ... | yes refl≡ = x
  ... | no _ = Ra˙ b .ε

  --------------------------------------------------------------------
  -- On inj

  module _ {a : A} where

    open RA (Ra˙ a) using () renaming (Carrier to Carrierᵃ; _≈_ to _≈a_;
      _∙_ to _∙ᵃ_; ε to εᵃ; ⌞_⌟ to ⌞_⌟ᵃ; refl to reflᵃ)

    private variable
      x y : Carrierᵃ

    inj-cong : (inj a) Preserves _≈a_ ⟶ _≈∀_
    inj-cong x≈y b with a ≟ b
    ... | yes refl≡ = x≈y
    ... | no _ = Ra˙ b .refl

    inj-∙ : inj a x ∙∀ inj a y ≈∀ inj a (x ∙ᵃ y)
    inj-∙ b with a ≟ b
    ... | yes refl≡ = reflᵃ
    ... | no _ = unitˡ (Ra˙ b)

    inj-ε : inj a εᵃ ≈∀ ε∀
    inj-ε b with a ≟ b
    ... | yes refl≡ = reflᵃ
    ... | no _ = refl (Ra˙ b)

    inj-⌞⌟ : ⌞ inj a x ⌟∀ ≈∀ inj a ⌞ x ⌟ᵃ
    inj-⌞⌟ b with a ≟ b
    ... | yes refl≡ = reflᵃ
    ... | no _ = Ra˙ b .⌞⌟-ε
