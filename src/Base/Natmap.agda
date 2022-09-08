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
open import Base.Dec using (yes; no; _≡?_; ≡?-refl)
open import Base.Nat using (ℕ; ṡ_; _≥_; _⊔_; <-irrefl; ⊔≤-introˡ;
  ⊔≤-introʳ)

private variable
  ł :  Level
  A :  Set ł
  A˙ :  ℕ → Set ł
  F :  ∀ i →  A˙ i →  Set ł
  f g :  ∀ i →  A˙ i
  a b :  A
  i j :  ℕ

--------------------------------------------------------------------------------
-- updᴺᴹ :  Update a map at an index

updᴺᴹ :  ∀ i →  A˙ i →  (∀ j →  A˙ j) →  (∀ j →  A˙ j)
updᴺᴹ i a f j  with j ≡? i
… | no _ =  f j
… | yes refl =  a

abstract

  -- Congruence on updᴺᴹ

  updᴺᴹ-cong :  f ≡˙ g →  updᴺᴹ i a f  ≡˙  updᴺᴹ i a g
  updᴺᴹ-cong {i = i} f≡g j  with j ≡? i
  … | yes refl =  refl
  … | no _ =  f≡g j

  -- Self updᴺᴹ

  updᴺᴹ-self :  updᴺᴹ i (f i) f  ≡˙  f
  updᴺᴹ-self {i} j  with j ≡? i
  … | yes refl =  refl
  … | no _ =  refl

  -- Double updᴺᴹ

  updᴺᴹ-2 :  updᴺᴹ i a (updᴺᴹ i b f)  ≡˙  updᴺᴹ i a f
  updᴺᴹ-2 {i} j  with j ≡? i
  … | yes refl =  refl
  … | no j≢i  with j ≡? i
  …   | yes refl =  absurd $ j≢i refl
  …   | no _ =  refl

  -- Swap updᴺᴹ on different indices

  updᴺᴹ-swap :  i ≢ j →
    updᴺᴹ i a (updᴺᴹ j b f) ≡˙ updᴺᴹ j b (updᴺᴹ i a f)
  updᴺᴹ-swap {i} {j} i≢j k  with k ≡? i
  … | yes refl  with k ≡? j
  …   | yes refl =  absurd $ i≢j refl
  …   | no _  rewrite ≡?-refl {a = k} =  refl
  updᴺᴹ-swap {i} {j} _ k | no k≢i  with k ≡? j
  …   | yes refl  with k ≡? i
  …     | yes refl =  absurd $ k≢i refl
  …     | no _ =  refl
  updᴺᴹ-swap {i} _ k | no k≢i | no _  with k ≡? i
  …     | yes refl =  absurd $ k≢i refl
  …     | no _ =  refl

--------------------------------------------------------------------------------
-- Cofinite property

-- Cofin F f : F (f i) holds for every i but a finite number of exceptions

Cofin :  (∀ i → A˙ i → Set ł) →  (∀ i → A˙ i) →  Set ł
Cofin F f =  ∑ n ,  ∀ i →  i ≥ n →  F i (f i)

abstract

  -- Cofin holds if there is no exception

  ∀⇒Cofin :  (∀ i → F i (f i)) →  Cofin F f
  ∀⇒Cofin Ffi =  0 , λ _ _ → Ffi _

  -- Cofin is preserved by updᴺᴹ

  Cofin-updᴺᴹ :  Cofin F f →  Cofin F (updᴺᴹ i a f)
  Cofin-updᴺᴹ {i = i} (n , _) .π₀ =  ṡ i ⊔ n
  Cofin-updᴺᴹ {i = i} (n , i≥n⇒Ffi) .π₁ j ṡi⊔n≥j  with j ≡? i
  … | no _ =  i≥n⇒Ffi _ $ ⊔≤-introʳ {ṡ _} ṡi⊔n≥j
  … | yes refl =  absurd $ <-irrefl $ ⊔≤-introˡ {m = n} ṡi⊔n≥j
