--------------------------------------------------------------------------------
-- Map over natural numbers
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Natmap where

open import Base.Level using (Level)
open import Base.Func using (_$_)
open import Base.Few using (absurd)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using (yes; no)
open import Base.Prod using (∑-syntax; _,_; proj₀; proj₁)
open import Base.Bool using (tt; ff)
open import Base.Nat using (ℕ; ṡ_; _≡ᵇ_; _≡?_; _≥_; _⊔_; ᵇ⇒≡; <-irrefl;
  ⊔≤-introˡ; ⊔≤-introʳ)

private variable
  ł :  Level
  A :  Set ł
  A˙ :  ℕ → Set ł
  F :  A → Set ł
  f :  ∀ i →  A˙ i
  a :  A
  i :  ℕ

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

--------------------------------------------------------------------------------
-- Cofinite property

-- Cofin F f : F (f i) holds for every i but a finite number of exceptions

Cofin :  (A → Set ł) →  (ℕ → A) →  Set ł
Cofin F f =  ∑ n ,  ∀ i →  i ≥ n →  F (f i)

abstract

  -- Cofin holds if there is no exception

  ∀⇒Cofin :  (∀ i → F (f i)) →  Cofin F f
  ∀⇒Cofin Ffi =  0 , λ _ _ → Ffi _

  -- Cofin is preserved by updᴺᴹ

  Cofin-updᴺᴹ :  Cofin F f →  Cofin F (updᴺᴹ i a f)
  Cofin-updᴺᴹ {i = i} (n , _) .proj₀ =  ṡ i ⊔ n
  Cofin-updᴺᴹ {i = i} (n , i≥n⇒Ffi) .proj₁ j ṡi⊔n≥j
    with j ≡ᵇ i | ᵇ⇒≡ {j} {i}
  … | ff | _ =  i≥n⇒Ffi _ $ ⊔≤-introʳ {ṡ _} ṡi⊔n≥j
  … | tt | ⇒j≡i  rewrite ⇒j≡i _ =
    absurd $ <-irrefl $ ⊔≤-introˡ {m = n} ṡi⊔n≥j
