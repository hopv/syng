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
-- ag: Lifting A to Agᴿᴬ's carrier

ag :  A →  List A
ag a =  [ a ]

--------------------------------------------------------------------------------
-- Agᴿᴬ : Agreement resource algebra

module _ where
  open RA

  Agᴿᴬ :  RA ℓ (ℓ ⌴ ℓ≈) (ℓ ⌴ ℓ≈)
  Agᴿᴬ .Car =  List A
  Agᴿᴬ ._≈_ =  _≈ᴸ_
  Agᴿᴬ .✓_ =  homo
  Agᴿᴬ ._∙_ =  _++_
  Agᴿᴬ .ε =  []
  Agᴿᴬ .⌞_⌟ =  id
  Agᴿᴬ .refl˜ =  ≈ᴸ-refl
  Agᴿᴬ .◠˜_ =  ≈ᴸ-sym
  Agᴿᴬ ._◇˜_ =  ≈ᴸ-trans
  Agᴿᴬ .∙-congˡ =  ++-congˡ
  Agᴿᴬ .∙-unitˡ =  ≈ᴸ-refl
  Agᴿᴬ .∙-comm {as} =  ++-comm {as}
  Agᴿᴬ .∙-assocˡ {as} =  ≡⇒≈ᴸ (++-assocˡ {as = as})
  Agᴿᴬ .✓-resp =  homo-resp
  Agᴿᴬ .✓-rem =  homo-mono ++-⊆ᴸ-introʳ
  Agᴿᴬ .✓-ε =  homo-[]
  Agᴿᴬ .⌞⌟-cong =  id
  Agᴿᴬ .⌞⌟-add =  _ , ≈ᴸ-refl
  Agᴿᴬ .⌞⌟-unitˡ =  ++-idem
  Agᴿᴬ .⌞⌟-idem =  ≈ᴸ-refl

open RA Agᴿᴬ using (✓_; _∙_)

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
