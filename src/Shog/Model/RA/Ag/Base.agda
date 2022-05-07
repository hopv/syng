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
open import Base.List.Set S using (_≈ᴸ_; homo;
  ≈ᴸ-refl; ++-⊆ᴸ-introʳ; ++-isCommutativeMonoid; ++-idem;
  homo-[]; homo-mono; homo-resp)
open import Shog.Model.RA using (RA)

open RA

--------------------------------------------------------------------------------
-- AgRA : Agreement resource algebra

AgRA : RA ℓ (ℓ ⊔ˡ ℓ≈) (ℓ ⊔ˡ ℓ≈)
AgRA .Carrier  =  List A
AgRA ._≈_  =  _≈ᴸ_
AgRA .✓  =  homo
AgRA ._∙_  =  _++_
AgRA .ε  =  []
AgRA .⌞_⌟  =  id
AgRA .isCommutativeMonoid  =  ++-isCommutativeMonoid
AgRA .✓-resp  =  homo-resp
AgRA .✓-rem  =  homo-mono ++-⊆ᴸ-introʳ
AgRA .✓-ε  =  homo-[]
AgRA .⌞⌟-cong  =  id
AgRA .⌞⌟-add  =  _ , ≈ᴸ-refl
AgRA .⌞⌟-unitˡ  =  ++-idem
AgRA .⌞⌟-idem  =  ≈ᴸ-refl
