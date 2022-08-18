--------------------------------------------------------------------------------
-- Finite map over natural numbers
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Finmap {Λ Λ'} (A : Set Λ) (null : A → Set Λ') where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.Prod using (∑-syntax; _,_; proj₀; proj₁)
open import Base.Func using (_$_)
open import Base.Eq using (_≡_; refl)
open import Base.Few using (absurd)
open import Base.Nat using (ℕ; suc; _≤_; _≡ᵇ_; _⊔_; ≤-trans; ᵇ⇒≡; ⊔≤-introˡ;
  ⊔≤-introʳ; <-irrefl; <⇒≤)
open import Base.Bool using (tt; ff)
open import Base.Nmap using (updⁿᵐ)

--------------------------------------------------------------------------------
-- Finmap : Finite map over natural numbers

-- Finᶠᵐ !ᶠᵐ n : !ᶠᵐ i is null for every i ≥ n
Finᶠᵐ :  (ℕ → A) →  ℕ →  Set Λ'
Finᶠᵐ !ᶠᵐ n =  ∀ {i} → n ≤ i → null (!ᶠᵐ i)

infix 5 _|ᶠᵐ_
record  Finmap :  Set (Λ ⊔ᴸ Λ')  where
  constructor _|ᶠᵐ_
  field
    -- Main map
    !ᶠᵐ :  ℕ → A
    -- !ᶠᵐ i is null for every i ≥ n for some n
    finᶠᵐ :  ∑ n , Finᶠᵐ !ᶠᵐ n
open Finmap public

--------------------------------------------------------------------------------
-- Various operations on Finmap

-- Null bound

boundᶠᵐ :  Finmap →  ℕ
boundᶠᵐ (_ |ᶠᵐ (n , _)) =  n

-- Finmap that constantly returns a null value

initᶠᵐ :  ∀ a →  null a →  Finmap
initᶠᵐ a _ .!ᶠᵐ _ =  a
initᶠᵐ _ nulla .finᶠᵐ =  0 , λ _ → nulla

-- Add a new element to the bound

addᶠᵐ :  A →  Finmap →  Finmap
addᶠᵐ a (f |ᶠᵐ (n , _)) .!ᶠᵐ =  updⁿᵐ n a f
addᶠᵐ a (f |ᶠᵐ (n , fi)) .finᶠᵐ =  suc n , proof
 where abstract
  proof :  Finᶠᵐ (updⁿᵐ n a f) (suc n)
  proof {j} n<j  with n ≡ᵇ j | ᵇ⇒≡ {n} {j}
  ... | ff | _ =  fi (<⇒≤ n<j)
  ... | tt | ⇒n≡j  with ⇒n≡j _
  ...   | refl =  absurd (<-irrefl n<j)

-- Update a finmap at an index

updᶠᵐ :  ℕ →  A →  Finmap →  Finmap
updᶠᵐ i a (f |ᶠᵐ _) .!ᶠᵐ =  updⁿᵐ i a f
updᶠᵐ i a (f |ᶠᵐ (n , fi)) .finᶠᵐ =  suc i ⊔ n , proof
 where abstract
  proof :  Finᶠᵐ (updⁿᵐ i a f) (suc i ⊔ n)
  proof {j} si⊔n≤j  with i ≡ᵇ j | ᵇ⇒≡ {i} {j}
  ... | ff | _ =  fi $ ⊔≤-introʳ {suc _} si⊔n≤j
  ... | tt | ⇒i≡j  with ⇒i≡j _
  ...   | refl =  absurd $ <-irrefl $ ⊔≤-introˡ {m = n} si⊔n≤j

-- Merge finmaps using a merge operation _∙_

mergeᶠᵐ :  ∀ (_∙_ : A → A → A) →  (∀{a b} → null a → null b → null (a ∙ b)) →
           Finmap →  Finmap →  Finmap
mergeᶠᵐ _∙_ _ (f |ᶠᵐ _) (g |ᶠᵐ _) .!ᶠᵐ i =  f i ∙ g i
mergeᶠᵐ _∙_ null∙ (f |ᶠᵐ (m , fi)) (g |ᶠᵐ (n , fi')) .finᶠᵐ =  m ⊔ n , proof
 where abstract
  proof :  Finᶠᵐ (λ i → f i ∙ g i) (m ⊔ n)
  proof m⊔n≤j =  null∙ (fi $ ⊔≤-introˡ m⊔n≤j) (fi' $ ⊔≤-introʳ {m} m⊔n≤j)
