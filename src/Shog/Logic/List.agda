----------------------------------------------------------------------
-- Shog definitions and lemams for lists
----------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Logic.List where

open import Level using (Level)
open import Size using (Size; ∞)
open import Function.Base using (_$_; _∘_; it)

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise; []; _∷_)

open import Shog.Logic.Prop using ([∗]; _∗_)
open import Shog.Logic.Basic

private variable
  ℓ ℓ' : Level
  i : Size
  A : Set ℓ'
  Ps Qs : List (Propˢ ℓ ∞)

----------------------------------------------------------------------
-- On [∗]

[∗]-++-in : ∀ Ps → [∗] Ps ∗ [∗] Qs ⊢[ i ] [∗] (Ps ++ Qs)
[∗]-++-in [] = ∗-elim₁
[∗]-++-in (_ ∷ Ps) = ∗-assoc₀ » ∗-mono₁ ([∗]-++-in Ps)

[∗]-++-out : ∀ Ps → [∗] (Ps ++ Qs) ⊢[ i ] [∗] Ps ∗ [∗] Qs
[∗]-++-out [] = ⊤∗-intro
[∗]-++-out (_ ∷ Ps) = ∗-mono₁ ([∗]-++-out Ps) » ∗-assoc₁

[∗]-mono : Pointwise _⊢[ i ]_ Ps Qs → [∗] Ps ⊢[ i ] [∗] Qs
[∗]-mono [] = idˢ
[∗]-mono (P⊢Q ∷ Ps⊢Qs) = ∗-mono P⊢Q ([∗]-mono Ps⊢Qs)
