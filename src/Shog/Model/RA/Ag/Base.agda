----------------------------------------------------------------------
-- Defining AgRA
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)
module Shog.Model.RA.Ag.Base {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) where
open Setoid S renaming (Carrier to A)

open import Level using (_⊔_)
open import Data.Product using (_,_)
open import Function.Base using (id; _$_)
open import Data.List.Base using (List; []; _++_)
open import Data.List.Membership.Setoid S using (_∈_)
open import Shog.Base.ListSet S using (_≈ˢ_; homo;
  ≈ˢ-refl; ++-⊆-introʳ; ++-≈ˢ-isCommutativeMonoid; ++-≈ˢ-idem;
  homo-⊆-resp; homo-≈ˢ-resp)
open import Shog.Model.RA using (RA)

open RA

----------------------------------------------------------------------
-- AgRA : Agreement resource algebra

AgRA : RA ℓ (ℓ ⊔ ℓ≈) (ℓ ⊔ ℓ≈)
AgRA .Carrier = List A
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
AgRA .⌞⌟-ε = ≈ˢ-refl
