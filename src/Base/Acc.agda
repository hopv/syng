--------------------------------------------------------------------------------
-- Accessibility
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Acc where

open import Base.Level using (Level; _⊔ᴸ_)

private variable
  ł ł' :  Level
  A B :  Set ł
  a :  A
  f :  A → B
  _≺_ _≺'_ :  A → A → Set ł

--------------------------------------------------------------------------------
-- Acc _≺_ a :  a is accessible w.r.t. ≺, i.e., every descending chain from a
--              terminates

data  Acc {A : Set ł} (_≺_ : A → A → Set ł') :  A →  Set (ł ⊔ᴸ ł')  where
  acc :  (∀{b} →  b ≺ a →  Acc _≺_ b) →  Acc _≺_ a

abstract

  -- If f a is accessible w.r.t. ≺' and ≺ is a sub-relation of f - ≺' f - ,
  -- then a is accessible w.r.t. ≺

  acc-sub :  (∀{a b} →  a ≺ b →  f a ≺' f b) →  Acc _≺'_ (f a) →  Acc _≺_ a
  acc-sub ≺⇒f≺' (acc ≺'fa⇒acc) =
    acc λ b≺a → acc-sub ≺⇒f≺' (≺'fa⇒acc (≺⇒f≺' b≺a))
