----------------------------------------------------------------------
-- Setoid utility
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)
module Base.Setoid {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) where
open Setoid S renaming (Carrier to X)

open import Base.Level using (Level; _⊔ˡ_)
open import Base.Function using (_∈_)
open import Data.Product using (_×_; ∃-syntax; _,_)

private variable
  ℓA ℓB ℓC : Level
  A : X → Set ℓA
  B : X → Set ℓB
  C : X → Set ℓC

----------------------------------------------------------------------
-- ⊆≈ : Set inclusion relaxed with ≈

infix 4 _⊆≈_

_⊆≈_ : (X → Set ℓA) → (X → Set ℓB) → Set (ℓ ⊔ˡ ℓ≈ ⊔ˡ ℓA ⊔ˡ ℓB)
A ⊆≈ B  = ∀ {a} →  a ∈ A  →  ∃[ b ]  a ≈ b  ×  b ∈ B

-- ⊆≈ is reflexive

⊆≈-refl : A ⊆≈ A
⊆≈-refl {a = a} a∈A = a , refl , a∈A

-- ⊆≈ is transitive

⊆≈-trans : A ⊆≈ B → B ⊆≈ C → A ⊆≈ C
⊆≈-trans A⊆≈B B⊆≈C a∈A with A⊆≈B a∈A
... | b , a≈b , b∈B with B⊆≈C b∈B
...   | c , b≈c , c∈C = c , trans a≈b b≈c , c∈C
