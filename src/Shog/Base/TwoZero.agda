------------------------------------------------------------------------
-- Two and Zero -- Level-polymorphic 2/0-element set
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Shog.Base.TwoZero where

open import Level using (Level)

private variable
  ℓ ℓ' : Level

data Two ℓ : Set ℓ where
  zero₂ one₂ : Two ℓ

data Zero ℓ : Set ℓ where

-- Function from Two/Zero

binary : ∀{F : Two ℓ → Set ℓ'} → F zero₂ → F one₂ → ∀ two → F two
binary a _ zero₂ = a
binary _ b one₂ = b

nullary : ∀{F : Zero ℓ → Set ℓ'} → ∀ zero → F zero
nullary ()
