--------------------------------------------------------------------------------
-- Accessibility
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Acc where

open import Base.Level using (Level; _⊔ᴸ_)

private variable
  ł ł' :  Level
  A :  Set ł
  a :  A

--------------------------------------------------------------------------------
-- Acc _≺_ a :  a is accessible with respect to ≺, or every descending chain
--              from a terminates

data  Acc {A : Set ł} (_≺_ : A → A → Set ł') :  A →  Set (ł ⊔ᴸ ł')  where
  acc :  (∀{b} →  b ≺ a →  Acc _≺_ b) →  Acc _≺_ a
