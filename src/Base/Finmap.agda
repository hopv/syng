--------------------------------------------------------------------------------
-- Finite map over natural numbers
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Finmap {ł ł'} (A : Set ł) (null : A → Set ł') where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.Func using (_$_)
open import Base.Few using (absurd)
open import Base.Prod using (∑-syntax; _,_; proj₀; proj₁)
open import Base.Bool using (tt; ff)
open import Base.Nat using (ℕ; suc; _≤_; _≡ᵇ_; _⊔_; ᵇ⇒≡; <-irrefl; ⊔≤-introˡ;
  ⊔≤-introʳ)
open import Base.Nmap using (updⁿᵐ)

--------------------------------------------------------------------------------
-- Finmap : Finite map over natural numbers

-- Finᶠᵐ !ᶠᵐ n : !ᶠᵐ i is null for every i ≥ n
Finᶠᵐ :  (ℕ → A) →  ℕ →  Set ł'
Finᶠᵐ !ᶠᵐ n =  ∀{i} → n ≤ i → null (!ᶠᵐ i)

infix 5 _|ᶠᵐ_
record  Finmap :  Set (ł ⊔ᴸ ł')  where
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

bndᶠᵐ :  Finmap →  ℕ
bndᶠᵐ (_ |ᶠᵐ (n , _)) =  n

-- Finmap that constantly returns a null value

initᶠᵐ :  ∀ a →  null a →  Finmap
initᶠᵐ a _ .!ᶠᵐ _ =  a
initᶠᵐ _ nulla .finᶠᵐ =  0 , λ _ → nulla

-- Update a finmap at an index

updᶠᵐ :  ℕ →  A →  Finmap →  Finmap
updᶠᵐ i a (f |ᶠᵐ _) .!ᶠᵐ =  updⁿᵐ i a f
updᶠᵐ i a (f |ᶠᵐ (n , fi)) .finᶠᵐ =  suc i ⊔ n , proof
 where abstract
  proof :  Finᶠᵐ (updⁿᵐ i a f) (suc i ⊔ n)
  proof {j} si⊔n≤j  with j ≡ᵇ i | ᵇ⇒≡ {j} {i}
  ... | ff | _ =  fi $ ⊔≤-introʳ {suc _} si⊔n≤j
  ... | tt | ⇒j≡i  rewrite ⇒j≡i _ =
    absurd $ <-irrefl $ ⊔≤-introˡ {m = n} si⊔n≤j

-- Merge finmaps using a merge operation _∙_

mergeᶠᵐ :  ∀(_∙_ : A → A → A) →  (∀{a b} → null a → null b → null (a ∙ b)) →
           Finmap →  Finmap →  Finmap
mergeᶠᵐ _∙_ _ (f |ᶠᵐ _) (g |ᶠᵐ _) .!ᶠᵐ i =  f i ∙ g i
mergeᶠᵐ _∙_ null∙ (f |ᶠᵐ (m , fi)) (g |ᶠᵐ (n , fi')) .finᶠᵐ =  m ⊔ n , proof
 where abstract
  proof :  Finᶠᵐ (λ i → f i ∙ g i) (m ⊔ n)
  proof m⊔n≤j =  null∙ (fi $ ⊔≤-introˡ m⊔n≤j) (fi' $ ⊔≤-introʳ {m} m⊔n≤j)
