----------------------------------------------------------------------
-- Shog definitions and lemams for lists
----------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Logic.List where

open import Level using (Level)
open import Size using (Size; ∞)
open import Function.Base using (_$_; _∘_; it)

open import Data.List.Base using (List; []; _∷_; foldr; map; _++_)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise; []; _∷_)

open import Shog.Logic.Prop
open import Shog.Logic.Sequent

private variable
  ℓ ℓ' : Level
  i : Size
  A : Set ℓ'
  Ps Qs : List (Propₛ ℓ ∞)

----------------------------------------------------------------------
-- Iterated separating conjunction

[∗] : List (Propₛ ℓ i) → Propₛ ℓ i
[∗] = foldr _∗_ ⊤ₛ

[∗]-map : (A → Propₛ ℓ i) → List A → Propₛ ℓ i
[∗]-map Pf as = [∗] $ map Pf as

syntax [∗]-map (λ a → P) as = [∗] a ∈ as , P

----------------------------------------------------------------------
-- On [∗]

[∗]-++-in : ∀ Ps → [∗] Ps ∗ [∗] Qs ⊢[ i ] [∗] (Ps ++ Qs)
[∗]-++-in [] = ∗-elim₁
[∗]-++-in (_ ∷ Ps) = ∗-assoc₀ » ∗-mono₁ ([∗]-++-in Ps)

[∗]-++-out : ∀ Ps → [∗] (Ps ++ Qs) ⊢[ i ] [∗] Ps ∗ [∗] Qs
[∗]-++-out [] = ⊤∗-intro
[∗]-++-out (_ ∷ Ps) = ∗-mono₁ ([∗]-++-out Ps) » ∗-assoc₁

[∗]-mono : Pointwise _⊢[ i ]_ Ps Qs → [∗] Ps ⊢[ i ] [∗] Qs
[∗]-mono [] = reflₛ
[∗]-mono (P⊢Q ∷ Ps⊢Qs) = ∗-mono P⊢Q ([∗]-mono Ps⊢Qs)
