----------------------------------------------------------------------
-- Dependent-function resource algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Shog.Model.RA using (RA)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
module Shog.Model.RA.Forall {ℓ' ℓ ℓ≈ ℓ✓} {A : Set ℓ'}
  (_=?=_ : Decidable {A = A} _≡_)
  (Ra˙ : A → RA ℓ ℓ≈ ℓ✓) where

open import Level using (_⊔_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using ()
  renaming (refl to refl≡)
open import Algebra.Construct.DirectProduct using ()
  renaming (commutativeMonoid to ×-CommutativeMonoid)
open import Data.Product using (_,_; proj₁; proj₂)
open import Shog.Base.Algebra using (make-IsCommutativeMonoid)

----------------------------------------------------------------------
-- ∀ᴿᴬ: Dependent-function resource algebra

module _ where
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
