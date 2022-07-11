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
-- AllRA: Dependent-function resource algebra

AllRA :  RA (ℓ' ⌴ ℓ) (ℓ' ⌴ ℓ≈) (ℓ' ⌴ ℓ✓)
AllRA .Car =  ∀ i →  Ra˙ i .Car
AllRA ._≈_ a˙ b˙ =  ∀ i →  Ra˙ i ._≈_ (a˙ i) (b˙ i)
AllRA .✓_ a˙ =  ∀ i →  Ra˙ i .✓_ (a˙ i)
AllRA ._∙_ a˙ b˙ i =  Ra˙ i ._∙_ (a˙ i) (b˙ i)
AllRA .ε i =  Ra˙ i .ε
AllRA .⌞_⌟ a˙ i =  Ra˙ i .⌞_⌟ (a˙ i)
AllRA .refl˜ i =  Ra˙ i .refl˜
AllRA .◠˜_ a˙≈b˙ i =  Ra˙ i .◠˜_ (a˙≈b˙ i)
AllRA ._◇˜_ a˙≈b˙ b˙≈c˙ i =  Ra˙ i ._◇˜_ (a˙≈b˙ i) (b˙≈c˙ i)
AllRA .∙-congˡ a˙≈b˙ i =  Ra˙ i .∙-congˡ (a˙≈b˙ i)
AllRA .∙-unitˡ i =  Ra˙ i .∙-unitˡ
AllRA .∙-comm i =  Ra˙ i .∙-comm
AllRA .∙-assocˡ i =  Ra˙ i .∙-assocˡ
AllRA .✓-resp a˙≈b˙ ✓a˙ i =  Ra˙ i .✓-resp (a˙≈b˙ i) (✓a˙ i)
AllRA .✓-rem ✓a˙∙b˙ i =  Ra˙ i .✓-rem (✓a˙∙b˙ i)
AllRA .✓-ε i =  Ra˙ i .✓-ε
AllRA .⌞⌟-cong a˙≈b˙ i =  Ra˙ i .⌞⌟-cong (a˙≈b˙ i)
AllRA .⌞⌟-add =  (λ i → Ra˙ i .⌞⌟-add .proj₀) , λ i → Ra˙ i .⌞⌟-add .proj₁
AllRA .⌞⌟-unitˡ i =  Ra˙ i .⌞⌟-unitˡ
AllRA .⌞⌟-idem i =  Ra˙ i .⌞⌟-idem
