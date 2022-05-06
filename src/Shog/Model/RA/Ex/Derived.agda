--------------------------------------------------------------------------------
-- On ExRA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)
module Shog.Model.RA.Ex.Derived {ℓ ℓ≈} {S : Setoid ℓ ℓ≈} {ℓ✓} where
open Setoid S renaming (Carrier to A)

open import Shog.Model.RA using (RA)
open import Shog.Model.RA.Ex.Base S {ℓ✓} using (ExRA; #ˣ; ?ˣ)
open RA ExRA using (_↝_)

private variable
  a b : A

abstract

  -- Update on #ˣ

  #ˣ-↝ :  #ˣ a  ↝  #ˣ b
  #ˣ-↝ ?ˣ = _
  -- the frame cˣ can only be ?ˣ; otherwise ✓ (cˣ ∙ #ˣ a) does not hold
