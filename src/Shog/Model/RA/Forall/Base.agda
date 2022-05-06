--------------------------------------------------------------------------------
-- Defining ∀ᴿᴬ
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Shog.Model.RA using (RA)
module Shog.Model.RA.Forall.Base {ℓ' ℓ ℓ≈ ℓ✓} {I : Set ℓ'}
  (Ra˙ : I → RA ℓ ℓ≈ ℓ✓) where

open import Base.Level using (_⊔ˡ_)
open import Relation.Binary using (IsEquivalence)
open import Base.Prod using (_,_; proj₀; proj₁)
open import Base.Algebra using (make-IsCommutativeMonoid)

--------------------------------------------------------------------------------
-- ∀ᴿᴬ: Dependent-function resource algebra

open IsEquivalence renaming (refl to refl'; sym to sym'; trans to trans')
open RA

∀ᴿᴬ : RA (ℓ' ⊔ˡ ℓ) (ℓ' ⊔ˡ ℓ≈) (ℓ' ⊔ˡ ℓ✓)
∀ᴿᴬ .Carrier  =  ∀ i → Ra˙ i .Carrier
∀ᴿᴬ ._≈_ a˙ b˙  =  ∀ i → Ra˙ i ._≈_ (a˙ i) (b˙ i)
∀ᴿᴬ .✓ a˙  =  ∀ i → Ra˙ i .✓ (a˙ i)
∀ᴿᴬ ._∙_ a˙ b˙ i  =  Ra˙ i ._∙_ (a˙ i) (b˙ i)
∀ᴿᴬ .ε i  =  Ra˙ i .ε
∀ᴿᴬ .⌞_⌟ a˙ i  =  Ra˙ i .⌞_⌟ (a˙ i)
∀ᴿᴬ .isCommutativeMonoid  =  make-IsCommutativeMonoid
  (λ{ .refl' i → refl (Ra˙ i) ; .sym' a˙≈b˙ i → sym (Ra˙ i) (a˙≈b˙ i);
    .trans' a˙≈b˙ b˙≈c˙ i → trans (Ra˙ i) (a˙≈b˙ i) (b˙≈c˙ i) })
  (λ a˙≈b˙ i → ∙-congˡ (Ra˙ i) (a˙≈b˙ i)) (λ _ i → unitˡ (Ra˙ i))
  (λ _ _ i → comm (Ra˙ i)) (λ _ _ _ i → assocˡ (Ra˙ i))
∀ᴿᴬ .✓-resp a˙≈b˙ ✓a˙ i  =  Ra˙ i .✓-resp (a˙≈b˙ i) (✓a˙ i)
∀ᴿᴬ .✓-rem ✓b˙∙a˙ i  =  Ra˙ i .✓-rem (✓b˙∙a˙ i)
∀ᴿᴬ .✓-ε i  =  Ra˙ i .✓-ε
∀ᴿᴬ .⌞⌟-cong a˙≈b˙ i  =  Ra˙ i .⌞⌟-cong (a˙≈b˙ i)
∀ᴿᴬ .⌞⌟-add  =  (λ i → Ra˙ i .⌞⌟-add .proj₀) , λ i → Ra˙ i .⌞⌟-add .proj₁
∀ᴿᴬ .⌞⌟-unitˡ i  =  Ra˙ i .⌞⌟-unitˡ
∀ᴿᴬ .⌞⌟-idem i  =  Ra˙ i .⌞⌟-idem
