--------------------------------------------------------------------------------
-- Finite map over natural numbers
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Finmap {ℓ ℓ'} (A : Set ℓ) (null : A → Set ℓ') where

open import Base.Level using (Level; _⌴_)
open import Base.Prod using (∑-syntax; _,_; proj₀; proj₁)
open import Base.Func using (_$_)
open import Base.Eq using (_≡_; refl)
open import Base.Few using (absurd)
open import Base.Nat using (ℕ; suc; _≤_; _≡ᵇ_; _⊔_; ≤-trans; ᵇ⇒≡; ⊔≤-introˡ;
  ⊔≤-introʳ; <-irrefl)
open import Base.Bool using (tt; ff)

--------------------------------------------------------------------------------
-- Finmap : Finite map over natural numbers

-- Finᶠᵐ mapᶠᵐ n : mapᶠᵐ i is null for every i ≥ n
Finᶠᵐ :  (ℕ → A) →  ℕ →  Set ℓ'
Finᶠᵐ mapᶠᵐ n =  ∀ {i} → n ≤ i → null (mapᶠᵐ i)

infix 5 _|ᶠᵐ_
record  Finmap :  Set (ℓ ⌴ ℓ')  where
  constructor _|ᶠᵐ_
  field
    -- Main map
    mapᶠᵐ :  ℕ → A
    -- mapᶠᵐ i is null for every i ≥ n for some n
    finᶠᵐ :  ∑ n , Finᶠᵐ mapᶠᵐ n
open Finmap public

--------------------------------------------------------------------------------
-- Various operations on Finmap

-- Finmap that constantly returns a null value

initᶠᵐ :  ∀ a →  null a →  Finmap
initᶠᵐ a _ .mapᶠᵐ _ =  a
initᶠᵐ _ nulla .finᶠᵐ =  0 , λ _ → nulla

-- Update a finmap at an index

updᶠᵐ :  ℕ →  A →  Finmap →  Finmap
updᶠᵐ i a (f |ᶠᵐ _) .mapᶠᵐ j  with i ≡ᵇ j
... | ff =  f j
... | tt =  a
updᶠᵐ i a M@(_ |ᶠᵐ (n , fi)) .finᶠᵐ =  suc i ⊔ n , proof
 where abstract
  proof :  Finᶠᵐ (updᶠᵐ i a M .mapᶠᵐ) (suc i ⊔ n)
  proof {j} si⊔n≤j  with i ≡ᵇ j | ᵇ⇒≡ {i} {j}
  ... | ff | _ =  fi $ ⊔≤-introʳ {suc _} si⊔n≤j
  ... | tt | ⇒i≡j  with ⇒i≡j _
  ...   | refl =  absurd $ <-irrefl $ ⊔≤-introˡ {m = n} si⊔n≤j

abstract

  -- Abstract version of updᶠᵐ

  updaᶠᵐ :  ℕ →  A →  Finmap →  Finmap
  updaᶠᵐ =  updᶠᵐ

  updaᶠᵐ-eq :  updaᶠᵐ ≡ updᶠᵐ
  updaᶠᵐ-eq =  refl

-- Merge finmaps using a merge operation _∙_

mergeᶠᵐ :  ∀ (_∙_ : A → A → A) →  (∀{a b} → null a → null b → null (a ∙ b)) →
           Finmap →  Finmap →  Finmap
mergeᶠᵐ _∙_ _ (f |ᶠᵐ _) (g |ᶠᵐ _) .mapᶠᵐ i =  f i ∙ g i
mergeᶠᵐ _∙_ null∙ (f |ᶠᵐ (m , fi)) (g |ᶠᵐ (n , fi')) .finᶠᵐ =  m ⊔ n , proof
 where abstract
  proof :  Finᶠᵐ (λ i → f i ∙ g i) (m ⊔ n)
  proof m⊔n≤j =  null∙ (fi $ ⊔≤-introˡ m⊔n≤j) (fi' $ ⊔≤-introʳ {m} m⊔n≤j)
