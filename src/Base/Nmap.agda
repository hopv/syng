--------------------------------------------------------------------------------
-- Map over natural numbers
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Nmap where

open import Base.Level using (Level)
open import Base.Eq using (_≡_; refl)
open import Base.Nat using (ℕ; _≡ᵇ_)
open import Base.Bool using (tt; ff)

private variable
  ℓ :  Level
  A :  Set ℓ

--------------------------------------------------------------------------------
-- updⁿᵐ :  Update a map at an index

updⁿᵐ :  ℕ →  A →  (ℕ → A) →  (ℕ → A)
updⁿᵐ i a f j  with i ≡ᵇ j
... | ff =  f j
... | tt =  a

abstract

  -- Abstract version of updⁿᵐ

  updaⁿᵐ :  ℕ →  A →  (ℕ → A) →  (ℕ → A)
  updaⁿᵐ =  updⁿᵐ

  updaⁿᵐ-eq :  ∀{A : Set ℓ} →  updaⁿᵐ {A = A} ≡ updⁿᵐ
  updaⁿᵐ-eq =  refl
