----------------------------------------------------------------------
-- Injection on ∀ᴿᴬ
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Shog.Model.RA using (RA)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
module Shog.Model.RA.Forall.Inj {ℓ' ℓ ℓ≈ ℓ✓} {I : Set ℓ'}
  {Ra˙ : I → RA ℓ ℓ≈ ℓ✓} (_≟_ : Decidable {A = I} _≡_) where

open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality renaming (refl to refl≡)
open import Shog.Model.RA.Forall.Base Ra˙ using (∀ᴿᴬ)

open RA
open RA ∀ᴿᴬ using () renaming (Carrier to A∀; _≈_ to _≈∀_;
  _∙_ to _∙∀_; ε to ε∀; ⌞_⌟ to ⌞_⌟∀; _~>_ to _~>∀_)

----------------------------------------------------------------------
-- Injecting an element of i component RA

∀-inj : ∀ i → Ra˙ i .Carrier → A∀
∀-inj i a j with i ≟ j
... | yes refl≡ = a
... | no _ = Ra˙ j .ε

----------------------------------------------------------------------
-- On ∀-inj

module _ {i : I} where

  open RA (Ra˙ i) using () renaming (Carrier to Aⁱ; _≈_ to _≈ⁱ_; _∙_ to _∙ⁱ_;
    ε to εⁱ; ⌞_⌟ to ⌞_⌟ⁱ; refl to reflⁱ; _~>_ to _~>ⁱ_)

  private variable
    a b : Aⁱ

  -- ∀-inj preserves ≈/∙/ε/⌞⌟/~>

  ∀-inj-cong : a ≈ⁱ b → ∀-inj i a ≈∀ ∀-inj i b
  ∀-inj-cong a≈b j with i ≟ j
  ... | yes refl≡ = a≈b
  ... | no _ = Ra˙ j .refl

  ∀-inj-∙ : ∀-inj i a ∙∀ ∀-inj i b ≈∀ ∀-inj i (a ∙ⁱ b)
  ∀-inj-∙ j with i ≟ j
  ... | yes refl≡ = reflⁱ
  ... | no _ = unitˡ (Ra˙ j)

  ∀-inj-ε : ∀-inj i εⁱ ≈∀ ε∀
  ∀-inj-ε j with i ≟ j
  ... | yes refl≡ = reflⁱ
  ... | no _ = refl (Ra˙ j)

  ∀-inj-⌞⌟ : ⌞ ∀-inj i a ⌟∀ ≈∀ ∀-inj i ⌞ a ⌟ⁱ
  ∀-inj-⌞⌟ j with i ≟ j
  ... | yes refl≡ = reflⁱ
  ... | no _ = Ra˙ j .⌞⌟-ε

  ∀-inj-~> :  a ~>ⁱ b  →  ∀-inj i a ~>∀ ∀-inj i b
  ∀-inj-~> a~>ⁱb c˙ ✓c˙∙ia j with i ≟ j | ✓c˙∙ia j
  ... | yes refl≡ | ✓c˙i∙a = a~>ⁱb (c˙ i) ✓c˙i∙a
  ... | no _ | ✓c˙j∙ε = ✓c˙j∙ε
