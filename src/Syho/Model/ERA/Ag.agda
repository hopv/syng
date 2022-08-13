--------------------------------------------------------------------------------
-- Agreement resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Setoid using (Setoid)
module Syho.Model.ERA.Ag {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) where
open Setoid S using (_≈_) renaming (Car to A)

open import Base.Level using (_⊔ᴸ_)
open import Base.Prod using (_,_)
open import Base.Func using (id; _$_)
open import Base.List using (List; []; _++_; [_]; ++-assocˡ)
open import Base.List.Set S using (_≈ᴸ_; homo; ≈ᴸ-refl; ≈ᴸ-sym; ≈ᴸ-trans; ≡⇒≈ᴸ;
  ++-congˡ; ++-comm; ++-idem; ++-⊆ᴸ-introʳ; homo-[]; homo-mono; homo-resp;
  homo-[?]; homo-agree)
open import Syho.Model.ERA using (ERA)

open ERA renaming (_≈_ to _≈'_) using (Car; ✓_; _∙_; ε; ⌞_⌟; refl˜; ◠˜_; _◇˜_;
  ∙-congˡ; ∙-unitˡ; ∙-comm; ∙-assocˡ; ✓-resp; ✓-rem; ✓-ε; ⌞⌟-cong; ⌞⌟-add;
  ⌞⌟-unitˡ; ⌞⌟-idem)

--------------------------------------------------------------------------------
-- ag :  Lifting A to AgRA's carrier

ag :  A →  List A
ag a =  [ a ]

--------------------------------------------------------------------------------
-- AgRA : Agreement resource algebra

AgRA :  ERA ℓ (ℓ ⊔ᴸ ℓ≈) (ℓ ⊔ᴸ ℓ≈)
AgRA .Car =  List A
AgRA ._≈'_ =  _≈ᴸ_
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

open ERA AgRA using () renaming (✓_ to ✓⁺_; _∙_ to _∙⁺_)

private variable
  a b :  A

--------------------------------------------------------------------------------
-- Lemmas

abstract

  -- ag a is valid
  ✓-ag :  ✓⁺ ag a
  ✓-ag =  homo-[?]

  -- Agreement
  agree :  ✓⁺ ag a ∙⁺ ag b →  a ≈ b
  agree =  homo-agree
