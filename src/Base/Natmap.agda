--------------------------------------------------------------------------------
-- Map over natural numbers
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Natmap where

open import Base.Level using (Level)
open import Base.Func using (_$_)
open import Base.Few using (absurd)
open import Base.Eq using (_≡_; _≢_; refl; _≡˙_)
open import Base.Prod using (∑-syntax; _,_; π₀; π₁)
open import Base.Dec using (yes; no; _≡?_; ≡?-refl; upd˙)
open import Base.Nat using (ℕ; ṡ_; _≥_; _⊔_; <-irrefl; ⊔≤-introˡ; ⊔≤-introʳ)

private variable
  ł :  Level
  A :  Set ł
  A˙ :  ℕ → Set ł
  F :  ∀ i →  A˙ i →  Set ł
  f :  ∀ i →  A˙ i
  i :  ℕ
  a :  A

--------------------------------------------------------------------------------
-- Cofinite property

-- Cofin F f : F (f i) holds for every i but a finite number of exceptions

Cofin :  (∀ i → A˙ i → Set ł) →  (∀ i → A˙ i) →  Set ł
Cofin F f =  ∑ n ,  ∀ i →  i ≥ n →  F i (f i)

abstract

  -- Cofin holds if there is no exception

  ∀⇒Cofin :  (∀ i → F i (f i)) →  Cofin F f
  ∀⇒Cofin Ffi =  0 , λ _ _ → Ffi _

  -- Cofin is preserved by upd˙

  Cofin-upd˙ :  Cofin F f →  Cofin F (upd˙ i a f)
  Cofin-upd˙ {i = i} (n , _) .π₀ =  ṡ i ⊔ n
  Cofin-upd˙ {i = i} (n , i≥n⇒Ffi) .π₁ j ṡi⊔n≥j  with j ≡? i
  … | no _ =  i≥n⇒Ffi _ $ ⊔≤-introʳ {ṡ _} ṡi⊔n≥j
  … | yes refl =  absurd $ <-irrefl $ ⊔≤-introˡ {m = n} ṡi⊔n≥j
