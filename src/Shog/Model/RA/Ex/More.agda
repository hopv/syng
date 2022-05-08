--------------------------------------------------------------------------------
-- On ExRA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Setoid using (Setoid)
module Shog.Model.RA.Ex.More {ℓ ℓ≈} {S : Setoid ℓ ℓ≈} {ℓ✓} where
open Setoid S renaming (Car to A)

open import Shog.Model.RA using (RA)
open import Shog.Model.RA.Ex S {ℓ✓} using (ExRA; #ˣ; ?ˣ)
open RA ExRA using (_↝_)

private variable
  a b : A

abstract

  -- Update on #ˣ

  #ˣ-↝ :  #ˣ a  ↝  #ˣ b
  #ˣ-↝ ?ˣ = _
  -- The frame cˣ can only be ?ˣ; otherwise ✓ (cˣ ∙ #ˣ a) does not hold
