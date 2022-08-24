--------------------------------------------------------------------------------
-- Map over natural numbers
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Nmap where

open import Base.Level using (Level)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using (yes; no)
open import Base.Nat using (ℕ; _≡ᵇ_; _≡?_)
open import Base.Bool using (tt; ff)

private variable
  ł :  Level
  A :  Set ł
  A˙ :  ℕ → Set ł

--------------------------------------------------------------------------------
-- updⁿᵐ, updᵈⁿᵐ :  Update a map at an index

updⁿᵐ :  ℕ →  A →  (ℕ → A) →  (ℕ → A)
updⁿᵐ i a f j  with j ≡ᵇ i
... | ff =  f j
... | tt =  a

-- Variant with the return type dependent on the index

updᵈⁿᵐ :  ∀ i →  A˙ i →  (∀ j →  A˙ j) →  (∀ j →  A˙ j)
updᵈⁿᵐ i a f j  with j ≡? i
... | no _ =  f j
... | yes refl =  a
