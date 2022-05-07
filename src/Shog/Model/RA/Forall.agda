--------------------------------------------------------------------------------
-- Dependent-function resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Shog.Model.RA using (RA)
module Shog.Model.RA.Forall {ℓ' ℓ ℓ≈ ℓ✓} {I : Set ℓ'}
  (Ra˙ : I → RA ℓ ℓ≈ ℓ✓) where

open import Base.Level using (_⊔ˡ_)
open import Base.Prod using (_,_; proj₀; proj₁)

open RA

--------------------------------------------------------------------------------
-- ∀ᴿᴬ: Dependent-function resource algebra

∀ᴿᴬ : RA (ℓ' ⊔ˡ ℓ) (ℓ' ⊔ˡ ℓ≈) (ℓ' ⊔ˡ ℓ✓)
∀ᴿᴬ .Car  =  ∀ i → Ra˙ i .Car
∀ᴿᴬ ._≈_ a˙ b˙  =  ∀ i → Ra˙ i ._≈_ (a˙ i) (b˙ i)
∀ᴿᴬ .✓ a˙  =  ∀ i → Ra˙ i .✓ (a˙ i)
∀ᴿᴬ ._∙_ a˙ b˙ i  =  Ra˙ i ._∙_ (a˙ i) (b˙ i)
∀ᴿᴬ .ε i  =  Ra˙ i .ε
∀ᴿᴬ .⌞_⌟ a˙ i  =  Ra˙ i .⌞_⌟ (a˙ i)
∀ᴿᴬ .refl˜ i  =  Ra˙ i .refl˜
∀ᴿᴬ .sym˜ a˙≈b˙ i  =  Ra˙ i .sym˜ (a˙≈b˙ i)
∀ᴿᴬ ._»˜_ a˙≈b˙ b˙≈c˙ i  =  Ra˙ i ._»˜_ (a˙≈b˙ i) (b˙≈c˙ i)
∀ᴿᴬ .∙-congˡ a˙≈b˙ i  =  Ra˙ i .∙-congˡ (a˙≈b˙ i)
∀ᴿᴬ .∙-unitˡ i  =  Ra˙ i .∙-unitˡ
∀ᴿᴬ .∙-comm i  =  Ra˙ i .∙-comm
∀ᴿᴬ .∙-assocˡ i  =  Ra˙ i .∙-assocˡ
∀ᴿᴬ .✓-resp a˙≈b˙ ✓a˙ i  =  Ra˙ i .✓-resp (a˙≈b˙ i) (✓a˙ i)
∀ᴿᴬ .✓-rem ✓b˙∙a˙ i  =  Ra˙ i .✓-rem (✓b˙∙a˙ i)
∀ᴿᴬ .✓-ε i  =  Ra˙ i .✓-ε
∀ᴿᴬ .⌞⌟-cong a˙≈b˙ i  =  Ra˙ i .⌞⌟-cong (a˙≈b˙ i)
∀ᴿᴬ .⌞⌟-add  =  (λ i → Ra˙ i .⌞⌟-add .proj₀) , λ i → Ra˙ i .⌞⌟-add .proj₁
∀ᴿᴬ .⌞⌟-unitˡ i  =  Ra˙ i .⌞⌟-unitˡ
∀ᴿᴬ .⌞⌟-idem i  =  Ra˙ i .⌞⌟-idem
