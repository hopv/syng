----------------------------------------------------------------------
-- Defining ∀ᴿᴬ
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Shog.Model.RA using (RA)
module Shog.Model.RA.Forall.Base {ℓ' ℓ ℓ≈ ℓ✓} {I : Set ℓ'}
  (Ra˙ : I → RA ℓ ℓ≈ ℓ✓) where

open import Level using (_⊔_)
open import Relation.Binary using (IsEquivalence)
open import Data.Product using (_,_; proj₁; proj₂)
open import Shog.Base.Algebra using (make-IsCommutativeMonoid)

----------------------------------------------------------------------
-- ∀ᴿᴬ: Dependent-function resource algebra

open IsEquivalence renaming (refl to refl'; sym to sym'; trans to trans')
open RA

∀ᴿᴬ : RA (ℓ' ⊔ ℓ) (ℓ' ⊔ ℓ≈) (ℓ' ⊔ ℓ✓)
∀ᴿᴬ .Carrier = ∀ i → Ra˙ i .Carrier
∀ᴿᴬ ._≈_ a˙ b˙ = ∀ i → Ra˙ i ._≈_ (a˙ i) (b˙ i)
∀ᴿᴬ .✓ a˙ = ∀ i → Ra˙ i .✓ (a˙ i)
∀ᴿᴬ ._∙_ a˙ b˙ i = Ra˙ i ._∙_ (a˙ i) (b˙ i)
∀ᴿᴬ .ε i = Ra˙ i .ε
∀ᴿᴬ .⌞_⌟ a˙ i = Ra˙ i .⌞_⌟ (a˙ i)
∀ᴿᴬ .isCommutativeMonoid = make-IsCommutativeMonoid
  (λ{ .refl' i → Ra˙ i .refl; .sym' a˙≈b˙ i → Ra˙ i .sym (a˙≈b˙ i);
    .trans' a˙≈b˙ b˙≈c˙ i → Ra˙ i .trans (a˙≈b˙ i) (b˙≈c˙ i) })
  (λ a˙≈b˙ i → ∙-congˡ (Ra˙ i) (a˙≈b˙ i)) (λ _ i → unitˡ (Ra˙ i))
  (λ _ _ i → comm (Ra˙ i)) (λ _ _ _ i → assocˡ (Ra˙ i))
∀ᴿᴬ .✓-resp a˙≈b˙ ✓a˙ i = Ra˙ i .✓-resp (a˙≈b˙ i) (✓a˙ i)
∀ᴿᴬ .✓-rem ✓b˙∙a˙ i = Ra˙ i .✓-rem (✓b˙∙a˙ i)
∀ᴿᴬ .⌞⌟-cong a˙≈b˙ i = Ra˙ i .⌞⌟-cong (a˙≈b˙ i)
∀ᴿᴬ .⌞⌟-add = (λ i → Ra˙ i .⌞⌟-add .proj₁) , λ i → Ra˙ i .⌞⌟-add .proj₂
∀ᴿᴬ .⌞⌟-unitˡ i = Ra˙ i .⌞⌟-unitˡ
∀ᴿᴬ .⌞⌟-idem i = Ra˙ i .⌞⌟-idem
∀ᴿᴬ .⌞⌟-ε i = Ra˙ i .⌞⌟-ε
