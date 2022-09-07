--------------------------------------------------------------------------------
-- Map over natural numbers
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Natmap where

open import Base.Level using (Level)
open import Base.Func using (_$_)
open import Base.Few using (absurd)
open import Base.Eq using (_≡_; _≢_; refl; _≡˙_)
open import Base.Dec using (yes; no)
open import Base.Prod using (∑-syntax; _,_; π₀; π₁)
open import Base.Bool using (tt; ff)
open import Base.Nat using (ℕ; ṡ_; _≡ᵇ_; _≡?_; _≥_; _⊔_; ᵇ⇒≡; ≡?-refl; <-irrefl;
  ⊔≤-introˡ; ⊔≤-introʳ)

private variable
  ł :  Level
  A :  Set ł
  A˙ :  ℕ → Set ł
  F :  A → Set ł
  f g :  ∀ i →  A˙ i
  a b :  A
  i j :  ℕ

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

abstract

  -- Congruence on updᴰᴺᴹ

  updᴰᴺᴹ-cong :  f ≡˙ g →  updᴰᴺᴹ i a f  ≡˙  updᴰᴺᴹ i a g
  updᴰᴺᴹ-cong {i = i} f≡g j  with j ≡? i
  … | yes refl =  refl
  … | no _ =  f≡g j

  -- Self updᴰᴺᴹ

  updᴰᴺᴹ-self :  updᴰᴺᴹ i (f i) f  ≡˙  f
  updᴰᴺᴹ-self {i} j  with j ≡? i
  … | yes refl =  refl
  … | no _ =  refl

  -- Double updᴰᴺᴹ

  updᴰᴺᴹ-2 :  updᴰᴺᴹ i a (updᴰᴺᴹ i b f)  ≡˙  updᴰᴺᴹ i a f
  updᴰᴺᴹ-2 {i} j  with j ≡? i
  … | yes refl =  refl
  … | no j≢i  with j ≡? i
  …   | yes refl =  absurd $ j≢i refl
  …   | no _ =  refl

  -- Swap updᴰᴺᴹ on different indices

  updᴰᴺᴹ-swap :  i ≢ j →
    updᴰᴺᴹ i a (updᴰᴺᴹ j b f) ≡˙ updᴰᴺᴹ j b (updᴰᴺᴹ i a f)
  updᴰᴺᴹ-swap {i} {j} i≢j k  with k ≡? i
  … | yes refl  with k ≡? j
  …   | yes refl =  absurd $ i≢j refl
  …   | no _  rewrite ≡?-refl {k} =  refl
  updᴰᴺᴹ-swap {i} {j} _ k | no k≢i  with k ≡? j
  …   | yes refl  with k ≡? i
  …     | yes refl =  absurd $ k≢i refl
  …     | no _ =  refl
  updᴰᴺᴹ-swap {i} _ k | no k≢i | no _  with k ≡? i
  …     | yes refl =  absurd $ k≢i refl
  …     | no _ =  refl

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
  Cofin-updᴺᴹ {i = i} (n , _) .π₀ =  ṡ i ⊔ n
  Cofin-updᴺᴹ {i = i} (n , i≥n⇒Ffi) .π₁ j ṡi⊔n≥j
    with j ≡ᵇ i | ᵇ⇒≡ {j} {i}
  … | ff | _ =  i≥n⇒Ffi _ $ ⊔≤-introʳ {ṡ _} ṡi⊔n≥j
  … | tt | ⇒j≡i  rewrite ⇒j≡i _ =
    absurd $ <-irrefl $ ⊔≤-introˡ {m = n} ṡi⊔n≥j
