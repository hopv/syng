--------------------------------------------------------------------------------
-- On ×ᴿᴬ
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Shog.Model.RA using (RA)
module Shog.Model.RA.Prod.Derived {ℓˡ ℓ≈ˡ ℓ✓ˡ ℓʳ ℓ≈ʳ ℓ✓ʳ}
  {Raˡ : RA ℓˡ ℓ≈ˡ ℓ✓ˡ} {Raʳ : RA ℓʳ ℓ≈ʳ ℓ✓ʳ} where

open import Base.Prod using (_×_; _,_)
open import Shog.Model.RA.Prod.Base Raˡ Raʳ using (_×ᴿᴬ_)

open RA Raˡ using () renaming (Car to A; _≈_ to _≈ˡ_; ✓ to ✓ˡ; _∙_ to _∙ˡ_;
  ε to εˡ; ⌞_⌟ to ⌞_⌟ˡ; _↝_ to _↝ˡ_; refl˜ to refl˜ˡ; ↝-refl to ↝ˡ-refl)
open RA Raʳ using () renaming (Car to X; _≈_ to _≈ʳ_; ✓ to ✓ʳ; _∙_ to _∙ʳ_;
  ε to εʳ; ⌞_⌟ to ⌞_⌟ʳ; _↝_ to _↝ʳ_; refl˜ to refl˜ʳ; ↝-refl to ↝ʳ-refl)
open RA _×ᴿᴬ_ using (_≈_; _↝_) renaming (Car to AX)

private variable
  a b : A
  x y : X

abstract

  -- Congruence on a pair

  ×-congˡ :  a ≈ˡ b  →  (a , x) ≈ (b , x)
  ×-congˡ a≈b = a≈b , refl˜ʳ

  ×-congʳ :  x ≈ʳ y  →  (a , x) ≈ (a , y)
  ×-congʳ x≈y = refl˜ˡ , x≈y

  -- Injecting an element of a component RA

  ×-injˡ : A → AX
  ×-injˡ a = a , εʳ

  ×-injʳ : X → AX
  ×-injʳ x = εˡ , x

  -- Update on _×ᴿᴬ_

  ×-↝-lift :  a ↝ˡ b  →  x ↝ʳ y  →  (a , x) ↝ (b , y)
  ×-↝-lift a↝b x↝y _ (✓c∙a , ✓z∙x) = a↝b _ ✓c∙a , x↝y _ ✓z∙x

  ×-↝-liftˡ :  a ↝ˡ b  →  (a , x) ↝ (b , x)
  ×-↝-liftˡ a↝b = ×-↝-lift a↝b ↝ʳ-refl

  ×-↝-liftʳ :  x ↝ʳ y  →  (a , x) ↝ (a , y)
  ×-↝-liftʳ x↝y = ×-↝-lift ↝ˡ-refl x↝y
