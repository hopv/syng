--------------------------------------------------------------------------------
-- On AgRA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Setoid using (Setoid)
module Shog.Model.RA.Ag.More {ℓ ℓ≈} {S : Setoid ℓ ℓ≈} where
open Setoid S using () renaming (Car to A)

open import Base.List.Set S using (homo-agree)
open import Shog.Model.RA using (RA)
open import Shog.Model.RA.Ag S using (ag; AgRA)
open RA AgRA using (_∙_; ✓_)

private variable
  a b :  A

abstract

  -- Agreement
  agree :  ✓ ag a ∙ ag b →  a ≈ b
  agree =  homo-agree
