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
open import Shog.Logic.Core

private variable
  ℓ ℓ' : Level
  i : Size
  A : Set ℓ'
  Ps Qs : List (Propˢ ℓ ∞)

----------------------------------------------------------------------
-- On [∗]

-- [∗] is monotone

[∗]-mono : Pointwise _⊢[ i ]_ Ps Qs → [∗] Ps ⊢[ i ] [∗] Qs
[∗]-mono [] = idˢ
[∗]-mono (P⊢Q ∷ Ps⊢Qs) = ∗-mono P⊢Q ([∗]-mono Ps⊢Qs)

-- ++ can get inside and outside [∗]

[∗]-++-in : [∗] Ps ∗ [∗] Qs ⊢[ i ] [∗] (Ps ++ Qs)
[∗]-++-in {Ps = []} = ∗-elim₁
[∗]-++-in {Ps = _ ∷ Ps} = ∗-assoc₀ » ∗-mono₁ ([∗]-++-in {Ps = Ps})

[∗]-++-out : [∗] (Ps ++ Qs) ⊢[ i ] [∗] Ps ∗ [∗] Qs
[∗]-++-out {Ps = []} = ⊤∗-intro
[∗]-++-out {Ps = _ ∷ Ps} = ∗-mono₁ ([∗]-++-out {Ps = Ps}) » ∗-assoc₁
