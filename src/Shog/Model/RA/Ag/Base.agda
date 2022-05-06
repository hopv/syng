--------------------------------------------------------------------------------
-- Defining AgRA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)
module Shog.Model.RA.Ag.Base {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) where
open Setoid S renaming (Carrier to A)

open import Base.Level using (_⊔ˡ_)
open import Base.Prod using (_,_)
open import Base.Func using (id; _$_)
open import Base.List using (List; []; _++_)
open import Base.List.Set S using (_≈ˡ_; homo;
  ≈ˡ-refl; ++-⊆ˡ-introʳ; ++-≈ˡ-isCommutativeMonoid; ++-≈ˡ-idem;
  homo-[]; homo-⊆ˡ-resp; homo-≈ˡ-resp)
open import Shog.Model.RA using (RA)

open RA

--------------------------------------------------------------------------------
-- AgRA : Agreement resource algebra

AgRA : RA ℓ (ℓ ⊔ˡ ℓ≈) (ℓ ⊔ˡ ℓ≈)
AgRA .Carrier  =  List A
AgRA ._≈_  =  _≈ˡ_
AgRA .✓  =  homo
AgRA ._∙_  =  _++_
AgRA .ε  =  []
AgRA .⌞_⌟  =  id
AgRA .isCommutativeMonoid  =  ++-≈ˡ-isCommutativeMonoid
AgRA .✓-resp  =  homo-≈ˡ-resp
AgRA .✓-rem  =  homo-⊆ˡ-resp ++-⊆ˡ-introʳ
AgRA .✓-ε  =  homo-[]
AgRA .⌞⌟-cong  =  id
AgRA .⌞⌟-add  =  _ , ≈ˡ-refl
AgRA .⌞⌟-unitˡ  =  ++-≈ˡ-idem
AgRA .⌞⌟-idem  =  ≈ˡ-refl
