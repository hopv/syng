module Shog.Util where

open import Level

-- For binary and nullary things

data Two ℓ : Set ℓ where
  zero₂ one₂ : Two ℓ

data Zero ℓ : Set ℓ where

private variable
  ℓ : Level
  A : Set ℓ

binary : A → A → Two ℓ → A
binary a _ zero₂ = a
binary _ b one₂ = b

binary-dep : ∀{F : Two ℓ → Set (suc ℓ)} →
                 F zero₂ → F one₂ → ∀ x → F x
binary-dep a _ zero₂ = a
binary-dep _ b one₂ = b

nullary : Zero ℓ → A
nullary ()

nullary-dep : ∀{F : Zero ℓ → Set (suc ℓ)} → ∀ x → F x
nullary-dep ()
