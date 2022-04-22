----------------------------------------------------------------------
-- Setoid utility
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)
module Shog.Base.Setoid {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) where
open Setoid S renaming (Carrier to Car)

open import Level using (Level; _⊔_)
open import Relation.Binary using (REL; Reflexive)
open import Relation.Unary using (Pred; _∈_)
open import Data.Product using (_×_; ∃-syntax; _,_)

private variable
  ℓA ℓB ℓC : Level
  A : Pred Car ℓA
  B : Pred Car ℓB
  C : Pred Car ℓC

----------------------------------------------------------------------
-- ⊆≈ : Set inclusion relaxed with ≈

infix 4 _⊆≈_

_⊆≈_ : REL (Pred Car ℓA) (Pred Car ℓB) (ℓ ⊔ ℓ≈ ⊔ ℓA ⊔ ℓB)
A ⊆≈ B = ∀ {a} → a ∈ A → ∃[ b ] a ≈ b × b ∈ B


-- ⊆≈ is reflexive

⊆≈-refl : Reflexive (_⊆≈_ {ℓA})
⊆≈-refl {a = a} a∈A = a , refl , a∈A

-- ⊆≈ is transitive
-- We don't use Transitive to achieve better level polymorphism

⊆≈-trans : A ⊆≈ B → B ⊆≈ C → A ⊆≈ C
⊆≈-trans A⊆≈B B⊆≈C a∈A with A⊆≈B a∈A
... | b , a≈b , b∈B with B⊆≈C b∈B
...   | c , b≈c , c∈C = c , trans a≈b b≈c , c∈C
