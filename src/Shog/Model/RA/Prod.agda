--------------------------------------------------------------------------------
-- Product resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Shog.Model.RA using (RA)
module Shog.Model.RA.Prod {ℓˡ ℓ≈ˡ ℓ✓ˡ ℓʳ ℓ≈ʳ ℓ✓ʳ}
  (Raˡ : RA ℓˡ ℓ≈ˡ ℓ✓ˡ) (Raʳ : RA ℓʳ ℓ≈ʳ ℓ✓ʳ) where

open import Base.Level using (_⊔ˡ_)
open import Base.Prod using (_×_; _,_)

open RA Raˡ using () renaming (Car to A; _≈_ to _≈ˡ_; ✓_ to ✓ˡ_; _∙_ to _∙ˡ_;
  ε to εˡ; ⌞_⌟ to ⌞_⌟ˡ; _↝_ to _↝ˡ_; refl˜ to reflˡ; ↝-refl to ↝ˡ-refl)
open RA Raʳ using () renaming (Car to X; _≈_ to _≈ʳ_; ✓_ to ✓ʳ_; _∙_ to _∙ʳ_;
  ε to εʳ; ⌞_⌟ to ⌞_⌟ʳ; _↝_ to _↝ʳ_; refl˜ to reflʳ; ↝-refl to ↝ʳ-refl)

private variable
  a b :  A
  x y :  X

--------------------------------------------------------------------------------
-- Injecting an element of a component RA

×-injˡ :  A →  A × X
×-injˡ a =  a , εʳ

×-injʳ :  X →  A × X
×-injʳ x =  εˡ , x

--------------------------------------------------------------------------------
-- Prodᴿᴬ: Product resource algebra

module _ where
  open RA

  Prodᴿᴬ :  RA (ℓˡ ⊔ˡ ℓʳ) (ℓ≈ˡ ⊔ˡ ℓ≈ʳ) (ℓ✓ˡ ⊔ˡ ℓ✓ʳ)
  Prodᴿᴬ .Car =  A × X
  Prodᴿᴬ ._≈_ (a , x) (b , y) =  (a ≈ˡ b) × (x ≈ʳ y)
  Prodᴿᴬ .✓_ (a , x) =  ✓ˡ a × ✓ʳ x
  Prodᴿᴬ ._∙_ (a , x) (b , y) =  a ∙ˡ b , x ∙ʳ y
  Prodᴿᴬ .ε =  εˡ , εʳ
  Prodᴿᴬ .⌞_⌟ (a , x) =  ⌞ a ⌟ˡ , ⌞ x ⌟ʳ
  Prodᴿᴬ .refl˜ =  Raˡ .refl˜ , Raʳ .refl˜
  Prodᴿᴬ .sym˜ (a≈b , x≈y) =  Raˡ .sym˜ a≈b , Raʳ .sym˜ x≈y
  Prodᴿᴬ ._»˜_ (a≈b , x≈y) (b≈c , y≈z) =  Raˡ ._»˜_ a≈b b≈c , Raʳ ._»˜_ x≈y y≈z
  Prodᴿᴬ .∙-congˡ (a≈b , x≈y) =  Raˡ .∙-congˡ a≈b , Raʳ .∙-congˡ x≈y
  Prodᴿᴬ .∙-unitˡ =  Raˡ .∙-unitˡ , Raʳ .∙-unitˡ
  Prodᴿᴬ .∙-comm =  Raˡ .∙-comm , Raʳ .∙-comm
  Prodᴿᴬ .∙-assocˡ =  Raˡ .∙-assocˡ , Raʳ .∙-assocˡ
  Prodᴿᴬ .✓-resp (a≈b , x≈y) (✓a , ✓x) =  Raˡ .✓-resp a≈b ✓a , Raʳ .✓-resp x≈y ✓x
  Prodᴿᴬ .✓-rem (✓a∙b , ✓x∙y) =  Raˡ .✓-rem ✓a∙b , Raʳ .✓-rem ✓x∙y
  Prodᴿᴬ .✓-ε =  Raˡ .✓-ε , Raʳ .✓-ε
  Prodᴿᴬ .⌞⌟-cong (a≈b , x≈y) =  Raˡ .⌞⌟-cong a≈b , Raʳ .⌞⌟-cong x≈y
  Prodᴿᴬ .⌞⌟-add with Raˡ .⌞⌟-add | Raʳ .⌞⌟-add
  ... | b' , b'∙⌞a⌟≈⌞b∙a⌟ | y' , y'∙⌞x⌟≈⌞y∙x⌟  =
    (b' , y') , (b'∙⌞a⌟≈⌞b∙a⌟ , y'∙⌞x⌟≈⌞y∙x⌟)
  Prodᴿᴬ .⌞⌟-unitˡ =  Raˡ .⌞⌟-unitˡ , Raʳ .⌞⌟-unitˡ
  Prodᴿᴬ .⌞⌟-idem =  Raˡ .⌞⌟-idem , Raʳ .⌞⌟-idem

open RA Prodᴿᴬ using (_≈_; _↝_) renaming (Car to AX)

--------------------------------------------------------------------------------
-- Lemmas

abstract

  -- Congruence on a pair

  ×-congˡ :  a ≈ˡ b →  (a , x) ≈ (b , x)
  ×-congˡ a≈b =  a≈b , reflʳ

  ×-congʳ :  x ≈ʳ y →  (a , x) ≈ (a , y)
  ×-congʳ x≈y =  reflˡ , x≈y

  -- Update on Prodᴿᴬ

  ×-↝-lift :  a ↝ˡ b →  x ↝ʳ y →  (a , x) ↝ (b , y)
  ×-↝-lift a↝b x↝y _ (✓c∙a , ✓z∙x) =  a↝b _ ✓c∙a , x↝y _ ✓z∙x

  ×-↝-liftˡ :  a ↝ˡ b →  (a , x) ↝ (b , x)
  ×-↝-liftˡ a↝b =  ×-↝-lift a↝b ↝ʳ-refl

  ×-↝-liftʳ :  x ↝ʳ y →  (a , x) ↝ (a , y)
  ×-↝-liftʳ x↝y =  ×-↝-lift ↝ˡ-refl x↝y
