--------------------------------------------------------------------------------
-- Map over natural numbers
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Nmap where

open import Base.Level using (Level)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using (yes; no)
open import Base.Bool using (tt; ff)
open import Base.Nat using (ℕ; _≡ᵇ_; _≡?_)

private variable
  ł :  Level
  A :  Set ł
  A˙ :  ℕ → Set ł

--------------------------------------------------------------------------------
-- updᴺᴹ, updᴰᴺᴹ :  Update a map at an index

updᴺᴹ :  ℕ →  A →  (ℕ → A) →  (ℕ → A)
updᴺᴹ i a f j  with j ≡ᵇ i
… | ff =  f j
… | tt =  a

-- Variant with the return type dependent on the index

updᴰᴺᴹ :  ∀ i →  A˙ i →  (∀ j →  A˙ j) →  (∀ j →  A˙ j)
updᴰᴺᴹ i a f j  with j ≡? i
… | no _ =  f j
… | yes refl =  a
