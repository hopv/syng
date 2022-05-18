--------------------------------------------------------------------------------
-- Agreement resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Setoid using (Setoid)
module Shog.Model.RA.Ag {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) where
open Setoid S using () renaming (Car to A)

open import Base.Level using (_⊔ˡ_)
open import Base.Prod using (_,_)
open import Base.Func using (id; _$_)
open import Base.List using (List; []; _++_; [_]; ++-assocˡ)
open import Base.List.Set S using (_≈ᴸ_; homo; ≈ᴸ-refl; ≈ᴸ-sym; ≈ᴸ-trans; ≡⇒≈ᴸ;
  ++-congˡ; ++-comm; ++-idem; ++-⊆ᴸ-introʳ; homo-[]; homo-mono; homo-resp)
open import Shog.Model.RA using (RA)

open RA

--------------------------------------------------------------------------------
-- ag: Lifting A to AgRA's carrier

ag :  A →  List A
ag a =  [ a ]

--------------------------------------------------------------------------------
-- AgRA : Agreement resource algebra

AgRA :  RA ℓ (ℓ ⊔ˡ ℓ≈) (ℓ ⊔ˡ ℓ≈)
AgRA .Car =  List A
AgRA ._≈_ =  _≈ᴸ_
AgRA .✓_ =  homo
AgRA ._∙_ =  _++_
AgRA .ε =  []
AgRA .⌞_⌟ =  id
AgRA .refl˜ =  ≈ᴸ-refl
AgRA .sym˜ =  ≈ᴸ-sym
AgRA ._»˜_ =  ≈ᴸ-trans
AgRA .∙-congˡ =  ++-congˡ
AgRA .∙-unitˡ =  ≈ᴸ-refl
AgRA .∙-comm {as} =  ++-comm {as}
AgRA .∙-assocˡ {as} =  ≡⇒≈ᴸ (++-assocˡ {as = as})
AgRA .✓-resp =  homo-resp
AgRA .✓-rem =  homo-mono ++-⊆ᴸ-introʳ
AgRA .✓-ε =  homo-[]
AgRA .⌞⌟-cong =  id
AgRA .⌞⌟-add =  _ , ≈ᴸ-refl
AgRA .⌞⌟-unitˡ =  ++-idem
AgRA .⌞⌟-idem =  ≈ᴸ-refl
