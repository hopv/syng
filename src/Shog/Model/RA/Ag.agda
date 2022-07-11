--------------------------------------------------------------------------------
-- Agreement resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Setoid using (Setoid)
module Shog.Model.RA.Ag {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) where
open Setoid S using (_≈_) renaming (Car to A)

open import Base.Level using (_⌴_)
open import Base.Prod using (_,_)
open import Base.Func using (id; _$_)
open import Base.List using (List; []; _++_; [_]; ++-assocˡ)
open import Base.List.Set S using (_≈ᴸ_; homo; ≈ᴸ-refl; ≈ᴸ-sym; ≈ᴸ-trans; ≡⇒≈ᴸ;
  ++-congˡ; ++-comm; ++-idem; ++-⊆ᴸ-introʳ; homo-[]; homo-mono; homo-resp;
  homo-[?]; homo-agree)
open import Shog.Model.RA using (RA)

--------------------------------------------------------------------------------
-- ag: Lifting A to AgRA's carrier

ag :  A →  List A
ag a =  [ a ]

--------------------------------------------------------------------------------
-- AgRA : Agreement resource algebra

module _ where
  open RA

  AgRA :  RA ℓ (ℓ ⌴ ℓ≈) (ℓ ⌴ ℓ≈)
  AgRA .Car =  List A
  AgRA ._≈_ =  _≈ᴸ_
  AgRA .✓_ =  homo
  AgRA ._∙_ =  _++_
  AgRA .ε =  []
  AgRA .⌞_⌟ =  id
  AgRA .refl˜ =  ≈ᴸ-refl
  AgRA .◠˜_ =  ≈ᴸ-sym
  AgRA ._◇˜_ =  ≈ᴸ-trans
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

open RA AgRA using (✓_; _∙_)

private variable
  a b :  A

--------------------------------------------------------------------------------
-- Lemmas

abstract

  -- ag a is valid
  ✓-ag :  ✓ ag a
  ✓-ag =  homo-[?]

  -- Agreement
  agree :  ✓ ag a ∙ ag b →  a ≈ b
  agree =  homo-agree
