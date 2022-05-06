--------------------------------------------------------------------------------
-- On AgRA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)
module Shog.Model.RA.Ag.Derived {ℓ ℓ≈} {S : Setoid ℓ ℓ≈} where
open Setoid S renaming (Carrier to A)

open import Base.List using (List; [_])
open import Base.List.Set S using (homo-heads2-≈)
open import Shog.Model.RA using (RA)
open import Shog.Model.RA.Ag.Base S using (AgRA)
open RA AgRA using (_∙_; ✓)

private variable
  a b : A

ag : A → List A
ag a = [ a ]

abstract

  agree :  ✓ (ag a ∙ ag b)  →  a ≈ b
  agree = homo-heads2-≈
