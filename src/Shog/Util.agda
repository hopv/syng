module Shog.Util where

open import Level

-- For binary and nullary things

data Two ℓ : Set ℓ where
  zero₂ one₂ : Two ℓ

data Zero ℓ : Set ℓ where

private variable
  ℓ ℓ' : Level

binary : ∀{F : Two ℓ → Set ℓ'} → F zero₂ → F one₂ → ∀ x → F x
binary a _ zero₂ = a
binary _ b one₂ = b

nullary : ∀{F : Zero ℓ → Set ℓ'} → ∀ x → F x
nullary ()
