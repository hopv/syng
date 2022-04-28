----------------------------------------------------------------------
-- Defining ×ᴿᴬ
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Shog.Model.RA using (RA)
module Shog.Model.RA.Prod.Base {ℓˡ ℓ≈ˡ ℓ✓ˡ ℓʳ ℓ≈ʳ ℓ✓ʳ}
  (Raˡ : RA ℓˡ ℓ≈ˡ ℓ✓ˡ) (Raʳ : RA ℓʳ ℓ≈ʳ ℓ✓ʳ) where

open RA Raˡ using () renaming (Carrier to Aˡ;
  _≈_ to _≈ˡ_; ✓ to ✓ˡ; _∙_ to _∙ˡ_; ε to εˡ; ⌞_⌟ to ⌞_⌟ˡ;
  commutativeMonoid to commutativeMonoidˡ; ✓-resp to ✓ˡ-resp; ✓-rem to ✓ˡ-rem;
  ✓-ε to ✓ˡ-ε; ⌞⌟-cong to ⌞⌟ˡ-cong; ⌞⌟-add to ⌞⌟ˡ-add; ⌞⌟-unitˡ to ⌞⌟ˡ-unitˡ;
  ⌞⌟-idem to ⌞⌟ˡ-idem)
open RA Raʳ using () renaming (Carrier to Aʳ;
  _≈_ to _≈ʳ_; ✓ to ✓ʳ; _∙_ to _∙ʳ_; ε to εʳ; ⌞_⌟ to ⌞_⌟ʳ;
  commutativeMonoid to commutativeMonoidʳ; ✓-resp to ✓ʳ-resp; ✓-rem to ✓ʳ-rem;
  ✓-ε to ✓ʳ-ε; ⌞⌟-cong to ⌞⌟ʳ-cong; ⌞⌟-add to ⌞⌟ʳ-add; ⌞⌟-unitˡ to ⌞⌟ʳ-unitˡ;
  ⌞⌟-idem to ⌞⌟ʳ-idem)

open import Level using (_⊔_)
open import Relation.Binary using (IsEquivalence)
open import Algebra using (CommutativeMonoid)
open CommutativeMonoid using ()
  renaming (isCommutativeMonoid to isCommutativeMonoid')
open import Algebra.Construct.DirectProduct using ()
  renaming (commutativeMonoid to ×-CommutativeMonoid)
open import Data.Product using (_×_; _,_)

----------------------------------------------------------------------
-- _×ᴿᴬ_: Product resource algebra

open IsEquivalence renaming (refl to refl'; sym to sym'; trans to trans')
open RA

infixr 2 _×ᴿᴬ_
_×ᴿᴬ_ : RA (ℓˡ ⊔ ℓʳ) (ℓ≈ˡ ⊔ ℓ≈ʳ) (ℓ✓ˡ ⊔ ℓ✓ʳ)
_×ᴿᴬ_ .Carrier  =  Aˡ × Aʳ
_×ᴿᴬ_ ._≈_ (a , x) (b , y)  =  (a ≈ˡ b) × (x ≈ʳ y)
_×ᴿᴬ_ .✓ (a , x)  =  ✓ˡ a × ✓ʳ x
_×ᴿᴬ_ ._∙_ (a , x) (b , y)  =  a ∙ˡ b , x ∙ʳ y
_×ᴿᴬ_ .ε  =  εˡ , εʳ
_×ᴿᴬ_ .⌞_⌟ (a , x)  =  ⌞ a ⌟ˡ , ⌞ x ⌟ʳ
_×ᴿᴬ_ .isCommutativeMonoid  =  ×-CommutativeMonoid
  commutativeMonoidˡ commutativeMonoidʳ .isCommutativeMonoid'
_×ᴿᴬ_ .✓-resp (a≈b , x≈y) (✓a , ✓x)  =  ✓ˡ-resp a≈b ✓a , ✓ʳ-resp x≈y ✓x
_×ᴿᴬ_ .✓-rem (✓b∙a , ✓y∙x)  =  ✓ˡ-rem ✓b∙a , ✓ʳ-rem ✓y∙x
_×ᴿᴬ_ .✓-ε  =  ✓ˡ-ε , ✓ʳ-ε
_×ᴿᴬ_ .⌞⌟-cong (a≈b , x≈y)  =  ⌞⌟ˡ-cong a≈b , ⌞⌟ʳ-cong x≈y
_×ᴿᴬ_ .⌞⌟-add with ⌞⌟ˡ-add | ⌞⌟ʳ-add
... | b' , b'∙⌞a⌟≈⌞b∙a⌟ | y' , y'∙⌞x⌟≈⌞y∙x⌟  =
  (b' , y') , (b'∙⌞a⌟≈⌞b∙a⌟ , y'∙⌞x⌟≈⌞y∙x⌟)
_×ᴿᴬ_ .⌞⌟-unitˡ  =  ⌞⌟ˡ-unitˡ , ⌞⌟ʳ-unitˡ
_×ᴿᴬ_ .⌞⌟-idem  =  ⌞⌟ˡ-idem , ⌞⌟ʳ-idem
