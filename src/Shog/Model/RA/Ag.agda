----------------------------------------------------------------------
-- Exclusive resource algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)
module Shog.Model.RA.Ag {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) where
open Setoid S renaming (Carrier to Car)

open import Level using (_⊔_)
open import Data.Product using (_,_)
open import Function.Base using (id; _$_)
open import Data.List.Base using (List; []; [_]; _++_)
open import Data.List.Membership.Setoid S using (_∈_)
open import Shog.Base.ListSet S using (_≈ˢ_; homo;
  ≈ˢ-refl; ++-⊆-introʳ; ++-≈ˢ-isCommutativeMonoid; ++-≈ˢ-idem;
  homo-⊆-resp; homo-≈ˢ-resp; homo-heads2-≈)
open import Shog.Model.RA using (RA)

----------------------------------------------------------------------
-- AgRA : Agreement resource algebra

module _ where
  open RA

  AgRA : RA ℓ (ℓ ⊔ ℓ≈) (ℓ ⊔ ℓ≈)
  AgRA .Carrier = List Car
  AgRA ._≈_ = _≈ˢ_
  AgRA .✓ = homo
  AgRA ._∙_ = _++_
  AgRA .ε = []
  AgRA .⌞_⌟ = id
  AgRA .isCommutativeMonoid = ++-≈ˢ-isCommutativeMonoid
  AgRA .✓-resp = homo-≈ˢ-resp
  AgRA .✓-rem = homo-⊆-resp ++-⊆-introʳ
  AgRA .⌞⌟-cong = id
  AgRA .⌞⌟-add = _ , ≈ˢ-refl
  AgRA .⌞⌟-unitˡ = ++-≈ˢ-idem _
  AgRA .⌞⌟-idem = ≈ˢ-refl

open RA AgRA using (_∙_; ✓) renaming (Carrier to AgCar)

private variable
  a b : Car

----------------------------------------------------------------------
-- On AgRA

ag : Car → AgCar
ag a = [ a ]

agree : ✓ (ag a ∙ ag b) → a ≈ b
agree = homo-heads2-≈
