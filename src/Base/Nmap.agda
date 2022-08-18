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
  Λ :  Level
  A :  Set Λ
  A˙ :  ℕ → Set Λ

--------------------------------------------------------------------------------
-- updⁿᵐ, dupdⁿᵐ :  Update a map at an index

updⁿᵐ :  ℕ →  A →  (ℕ → A) →  (ℕ → A)
updⁿᵐ i a f j  with i ≡ᵇ j
... | ff =  f j
... | tt =  a

-- Return type dependent on the index

updᵈⁿᵐ :  ∀ i →  A˙ i →  (∀ j →  A˙ j) →  (∀ j →  A˙ j)
updᵈⁿᵐ i a f j  with i ≡? j
... | no _ =  f j
... | yes refl =  a

abstract

  -- Abstract version of updⁿᵐ & updᵈⁿᵐ

  updaⁿᵐ :  ℕ →  A →  (ℕ → A) →  (ℕ → A)
  updaⁿᵐ =  updⁿᵐ

  updaᵈⁿᵐ :  ∀ i →  A˙ i →  (∀ j →  A˙ j) →  (∀ i →  A˙ i)
  updaᵈⁿᵐ =  updᵈⁿᵐ

  updaⁿᵐ-eq :  ∀{A : Set Λ} →  updaⁿᵐ {A = A} ≡ updⁿᵐ
  updaⁿᵐ-eq =  refl

  updaᵈⁿᵐ-eq :  ∀{A˙ : ℕ → Set Λ} →  updaᵈⁿᵐ {A˙ = A˙} ≡ updᵈⁿᵐ
  updaᵈⁿᵐ-eq =  refl
