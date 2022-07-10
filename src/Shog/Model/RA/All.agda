--------------------------------------------------------------------------------
-- Dependent-function resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Shog.Model.RA using (RA)
module Shog.Model.RA.All {ℓ' ℓ ℓ≈ ℓ✓} {I : Set ℓ'} (Ra˙ : I → RA ℓ ℓ≈ ℓ✓) where

open import Base.Level using (_⌴_)
open import Base.Prod using (_,_; proj₀; proj₁)

open RA

--------------------------------------------------------------------------------
-- Allᴿᴬ: Dependent-function resource algebra

Allᴿᴬ :  RA (ℓ' ⌴ ℓ) (ℓ' ⌴ ℓ≈) (ℓ' ⌴ ℓ✓)
Allᴿᴬ .Car =  ∀ i →  Ra˙ i .Car
Allᴿᴬ ._≈_ a˙ b˙ =  ∀ i →  Ra˙ i ._≈_ (a˙ i) (b˙ i)
Allᴿᴬ .✓_ a˙ =  ∀ i →  Ra˙ i .✓_ (a˙ i)
Allᴿᴬ ._∙_ a˙ b˙ i =  Ra˙ i ._∙_ (a˙ i) (b˙ i)
Allᴿᴬ .ε i =  Ra˙ i .ε
Allᴿᴬ .⌞_⌟ a˙ i =  Ra˙ i .⌞_⌟ (a˙ i)
Allᴿᴬ .refl˜ i =  Ra˙ i .refl˜
Allᴿᴬ .sym˜ a˙≈b˙ i =  Ra˙ i .sym˜ (a˙≈b˙ i)
Allᴿᴬ ._»˜_ a˙≈b˙ b˙≈c˙ i =  Ra˙ i ._»˜_ (a˙≈b˙ i) (b˙≈c˙ i)
Allᴿᴬ .∙-congˡ a˙≈b˙ i =  Ra˙ i .∙-congˡ (a˙≈b˙ i)
Allᴿᴬ .∙-unitˡ i =  Ra˙ i .∙-unitˡ
Allᴿᴬ .∙-comm i =  Ra˙ i .∙-comm
Allᴿᴬ .∙-assocˡ i =  Ra˙ i .∙-assocˡ
Allᴿᴬ .✓-resp a˙≈b˙ ✓a˙ i =  Ra˙ i .✓-resp (a˙≈b˙ i) (✓a˙ i)
Allᴿᴬ .✓-rem ✓a˙∙b˙ i =  Ra˙ i .✓-rem (✓a˙∙b˙ i)
Allᴿᴬ .✓-ε i =  Ra˙ i .✓-ε
Allᴿᴬ .⌞⌟-cong a˙≈b˙ i =  Ra˙ i .⌞⌟-cong (a˙≈b˙ i)
Allᴿᴬ .⌞⌟-add =  (λ i → Ra˙ i .⌞⌟-add .proj₀) , λ i → Ra˙ i .⌞⌟-add .proj₁
Allᴿᴬ .⌞⌟-unitˡ i =  Ra˙ i .⌞⌟-unitˡ
Allᴿᴬ .⌞⌟-idem i =  Ra˙ i .⌞⌟-idem
