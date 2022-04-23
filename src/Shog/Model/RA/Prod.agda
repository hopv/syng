----------------------------------------------------------------------
-- Product resource algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Shog.Model.RA using (RA)
module Shog.Model.RA.Prod {ℓˡ ℓ≈ˡ ℓ✓ˡ ℓʳ ℓ≈ʳ ℓ✓ʳ}
  (Raˡ : RA ℓˡ ℓ≈ˡ ℓ✓ˡ) (Raʳ : RA ℓʳ ℓ≈ʳ ℓ✓ʳ) where

open RA Raˡ using () renaming (Carrier to Carrierˡ;
  _≈_ to _≈ˡ_; ✓ to ✓ˡ; _∙_ to _∙ˡ_; ε to εˡ; ⌞_⌟ to ⌞_⌟ˡ;
  refl to reflˡ; sym to symˡ; trans to transˡ; ∙-congˡ to ∙ˡ-congˡ;
  unitˡ to ˡunitˡ; comm to ˡcomm; assocˡ to ˡassocˡ;
  ✓-resp to ✓ˡ-resp; ✓-rem to ✓ˡ-rem; ⌞⌟-cong to ⌞⌟ˡ-cong;
  ⌞⌟-add to ⌞⌟ˡ-add; ⌞⌟-unitˡ to ⌞⌟ˡ-unitˡ; ⌞⌟-idem to ⌞⌟ˡ-idem;
  _~>_ to _~>ˡ_; ~>-refl to ~>ˡ-refl)
open RA Raʳ using () renaming (Carrier to Carrierʳ;
  _≈_ to _≈ʳ_; ✓ to ✓ʳ; _∙_ to _∙ʳ_; ε to εʳ; ⌞_⌟ to ⌞_⌟ʳ;
  refl to reflʳ; sym to symʳ; trans to transʳ; ∙-congˡ to ∙ʳ-congˡ;
  unitˡ to ʳunitˡ; comm to ʳcomm; assocˡ to ʳassocˡ;
  ✓-resp to ✓ʳ-resp; ✓-rem to ✓ʳ-rem; ⌞⌟-cong to ⌞⌟ʳ-cong;
  ⌞⌟-add to ⌞⌟ʳ-add; ⌞⌟-unitˡ to ⌞⌟ʳ-unitˡ; ⌞⌟-idem to ⌞⌟ʳ-idem;
  _~>_ to _~>ʳ_; ~>-refl to ~>ʳ-refl)

open import Level using (_⊔_)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel; IsEquivalence)
open import Algebra using (Op₂; Op₁)
open import Data.Product using (_×_; _,_)
open import Shog.Base.Algebra using (make-IsCommutativeMonoid)

----------------------------------------------------------------------
-- _×ᴿᴬ_: Product resource algebra

module _ where
  open IsEquivalence renaming (refl to refl'; sym to sym'; trans to trans')
  open RA

  _×ᴿᴬ_ : RA (ℓˡ ⊔ ℓʳ) (ℓ≈ˡ ⊔ ℓ≈ʳ) (ℓ✓ˡ ⊔ ℓ✓ʳ)
  _×ᴿᴬ_ .Carrier = Carrierˡ × Carrierʳ
  _×ᴿᴬ_ ._≈_ (a , x) (b , y) = (a ≈ˡ b) × (x ≈ʳ y)
  _×ᴿᴬ_ .✓ (a , x) = ✓ˡ a × ✓ʳ x
  _×ᴿᴬ_ ._∙_ (a , x) (b , y) = a ∙ˡ b , x ∙ʳ y
  _×ᴿᴬ_ .ε = εˡ , εʳ
  _×ᴿᴬ_ .⌞_⌟ (a , x) = ⌞ a ⌟ˡ , ⌞ x ⌟ʳ
  _×ᴿᴬ_ .isCommutativeMonoid = make-IsCommutativeMonoid
    (λ{ .refl' → reflˡ , reflʳ; .sym' (a≈b , x≈y) → symˡ a≈b , symʳ x≈y;
      .trans' (a≈b , x≈y) (b≈c , y≈z) → transˡ a≈b b≈c , transʳ x≈y y≈z })
    (λ (a≈b , x≈y) → ∙ˡ-congˡ a≈b , ∙ʳ-congˡ x≈y) (λ _ → ˡunitˡ , ʳunitˡ)
    (λ _ _ → ˡcomm , ʳcomm) (λ _ _ _ → ˡassocˡ , ʳassocˡ)
  _×ᴿᴬ_ .✓-resp (a≈b , x≈y) (✓a , ✓x) = ✓ˡ-resp a≈b ✓a , ✓ʳ-resp x≈y ✓x
  _×ᴿᴬ_ .✓-rem (✓b∙a , ✓y∙x) = ✓ˡ-rem ✓b∙a , ✓ʳ-rem ✓y∙x
  _×ᴿᴬ_ .⌞⌟-cong (a≈b , x≈y) = ⌞⌟ˡ-cong a≈b , ⌞⌟ʳ-cong x≈y
  _×ᴿᴬ_ .⌞⌟-add with ⌞⌟ˡ-add | ⌞⌟ʳ-add
  ... | b' , b'∙⌞a⌟≈⌞b∙a⌟ | y' , y'∙⌞x⌟≈⌞y∙x⌟  =
    (b' , y') , (b'∙⌞a⌟≈⌞b∙a⌟ , y'∙⌞x⌟≈⌞y∙x⌟)
  _×ᴿᴬ_ .⌞⌟-unitˡ = ⌞⌟ˡ-unitˡ , ⌞⌟ʳ-unitˡ
  _×ᴿᴬ_ .⌞⌟-idem = ⌞⌟ˡ-idem , ⌞⌟ʳ-idem

private variable
  a b : Carrierˡ
  x y : Carrierʳ

open RA _×ᴿᴬ_

----------------------------------------------------------------------
-- Injection from a component RA's element

×-injˡ : Carrierˡ → Carrier
×-injˡ a = a , εʳ

×-injʳ : Carrierʳ → Carrier
×-injʳ x = εˡ , x

----------------------------------------------------------------------
-- Congruence on a pair

×-congˡ : a ≈ˡ b → (a , x) ≈ (b , x)
×-congˡ a≈b = a≈b , reflʳ

×-congʳ : x ≈ʳ y → (a , x) ≈ (a , y)
×-congʳ x≈y = reflˡ , x≈y

----------------------------------------------------------------------
-- Update on _×ᴿᴬ_

×-~>-lift :  a ~>ˡ b  →  x ~>ʳ y  →  (a , x) ~> (b , y)
×-~>-lift a~>b x~>y _ (✓c∙a , ✓z∙x) = a~>b _ ✓c∙a , x~>y _ ✓z∙x

×-~>-liftˡ :  a ~>ˡ b  →  (a , x) ~> (b , x)
×-~>-liftˡ a~>b = ×-~>-lift a~>b ~>ʳ-refl

×-~>-liftʳ :  x ~>ʳ y  →  (a , x) ~> (a , y)
×-~>-liftʳ x~>y = ×-~>-lift ~>ˡ-refl x~>y
