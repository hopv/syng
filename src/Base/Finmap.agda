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

Mostnull :  (ℕ → A) →  ℕ →  Set ℓ'
Mostnull mapfin boundfin =  ∀ {i} → boundfin ≤ i → null (mapfin i)

record  Finmap :  Set (ℓ ⌴ ℓ')  where
  constructor finmap
  field
    -- Main map
    mapfin :  ℕ → A
    -- finmap i is null for every i ≥ boundfin
    boundfin :  ℕ
    mostnull :  Mostnull mapfin boundfin
open Finmap public

-- Finmap that constantly returns a null value

initᶠᵐ :  ∀ a →  null a →  Finmap
initᶠᵐ a _ .mapfin _ =  a
initᶠᵐ _ _ .boundfin =  0
initᶠᵐ _ nulla .mostnull _ =  nulla

-- Update a finmap at an index

updᶠᵐ :  ℕ →  A →  Finmap →  Finmap
updᶠᵐ i a (finmap f _ _) .mapfin j  with i ≡ᵇ j
... | ff =  f j
... | tt =  a
updᶠᵐ i _ (finmap _ n _) .boundfin =  suc i ⊔ n
updᶠᵐ i a M@(finmap _ n monu) .mostnull =  proof
 where abstract
  proof :  Mostnull (updᶠᵐ i a M .mapfin) (suc i ⊔ n)
  proof {j} si⊔n≤j  with i ≡ᵇ j | ᵇ⇒≡ {i} {j}
  ... | ff | _ =  monu $ ⊔≤-introʳ {suc _} si⊔n≤j
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
mergeᶠᵐ _∙_ _ (finmap f _ _) (finmap g _ _) .mapfin i =  f i ∙ g i
mergeᶠᵐ _ _ (finmap _ m _) (finmap _ n _) .boundfin =  m ⊔ n
mergeᶠᵐ _∙_ null∙ (finmap f m monuf) (finmap g n monug) .mostnull =  proof
 where abstract
  proof :  Mostnull (λ i → f i ∙ g i) (m ⊔ n)
  proof m⊔n≤j =  null∙ (monuf $ ⊔≤-introˡ m⊔n≤j) (monug $ ⊔≤-introʳ {m} m⊔n≤j)
