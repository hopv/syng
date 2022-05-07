--------------------------------------------------------------------------------
-- Defining ×ᴿᴬ
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Shog.Model.RA using (RA)
module Shog.Model.RA.Prod {ℓˡ ℓ≈ˡ ℓ✓ˡ ℓʳ ℓ≈ʳ ℓ✓ʳ}
  (Raˡ : RA ℓˡ ℓ≈ˡ ℓ✓ˡ) (Raʳ : RA ℓʳ ℓ≈ʳ ℓ✓ʳ) where

open import Base.Level using (_⊔ˡ_)
open import Base.Prod using (_×_; _,_)

open RA
open RA Raˡ using () renaming (Car to A; _≈_ to _≈ˡ_; ✓ to ✓ˡ; _∙_ to _∙ˡ_;
  ε to εˡ; ⌞_⌟ to ⌞_⌟ˡ)
open RA Raʳ using () renaming (Car to X; _≈_ to _≈ʳ_; ✓ to ✓ʳ; _∙_ to _∙ʳ_;
  ε to εʳ; ⌞_⌟ to ⌞_⌟ʳ)

--------------------------------------------------------------------------------
-- _×ᴿᴬ_: Product resource algebra

infixr 2 _×ᴿᴬ_
_×ᴿᴬ_ : RA (ℓˡ ⊔ˡ ℓʳ) (ℓ≈ˡ ⊔ˡ ℓ≈ʳ) (ℓ✓ˡ ⊔ˡ ℓ✓ʳ)
_×ᴿᴬ_ .Car  =  A × X
_×ᴿᴬ_ ._≈_ (a , x) (b , y)  =  (a ≈ˡ b) × (x ≈ʳ y)
_×ᴿᴬ_ .✓ (a , x)  =  ✓ˡ a × ✓ʳ x
_×ᴿᴬ_ ._∙_ (a , x) (b , y)  =  a ∙ˡ b , x ∙ʳ y
_×ᴿᴬ_ .ε  =  εˡ , εʳ
_×ᴿᴬ_ .⌞_⌟ (a , x)  =  ⌞ a ⌟ˡ , ⌞ x ⌟ʳ
_×ᴿᴬ_ .refl˜  =  Raˡ .refl˜ , Raʳ .refl˜
_×ᴿᴬ_ .sym˜ (a≈b , x≈y)  =  Raˡ .sym˜ a≈b , Raʳ .sym˜ x≈y
_×ᴿᴬ_ ._»˜_ (a≈b , x≈y) (b≈c , y≈z) =  Raˡ ._»˜_ a≈b b≈c , Raʳ ._»˜_ x≈y y≈z
_×ᴿᴬ_ .∙-congˡ (a≈b , x≈y)  =  Raˡ .∙-congˡ a≈b , Raʳ .∙-congˡ x≈y
_×ᴿᴬ_ .∙-unitˡ  =  Raˡ .∙-unitˡ , Raʳ .∙-unitˡ
_×ᴿᴬ_ .∙-comm  =  Raˡ .∙-comm , Raʳ .∙-comm
_×ᴿᴬ_ .∙-assocˡ  =  Raˡ .∙-assocˡ , Raʳ .∙-assocˡ
_×ᴿᴬ_ .✓-resp (a≈b , x≈y) (✓a , ✓x)  =  Raˡ .✓-resp a≈b ✓a , Raʳ .✓-resp x≈y ✓x
_×ᴿᴬ_ .✓-rem (✓b∙a , ✓y∙x)  =  Raˡ .✓-rem ✓b∙a , Raʳ .✓-rem ✓y∙x
_×ᴿᴬ_ .✓-ε  =  Raˡ .✓-ε , Raʳ .✓-ε
_×ᴿᴬ_ .⌞⌟-cong (a≈b , x≈y)  =  Raˡ .⌞⌟-cong a≈b , Raʳ .⌞⌟-cong x≈y
_×ᴿᴬ_ .⌞⌟-add with Raˡ .⌞⌟-add | Raʳ .⌞⌟-add
... | b' , b'∙⌞a⌟≈⌞b∙a⌟ | y' , y'∙⌞x⌟≈⌞y∙x⌟  =
  (b' , y') , (b'∙⌞a⌟≈⌞b∙a⌟ , y'∙⌞x⌟≈⌞y∙x⌟)
_×ᴿᴬ_ .⌞⌟-unitˡ  =  Raˡ .⌞⌟-unitˡ , Raʳ .⌞⌟-unitˡ
_×ᴿᴬ_ .⌞⌟-idem  =  Raˡ .⌞⌟-idem , Raʳ .⌞⌟-idem
