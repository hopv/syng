----------------------------------------------------------------------
-- Injection on ∀ᴿᴬ
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Shog.Model.RA using (RA)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
module Shog.Model.RA.Forall.Point {ℓ' ℓ ℓ≈ ℓ✓} {I : Set ℓ'}
  {Ra˙ : I → RA ℓ ℓ≈ ℓ✓} (_≟_ : Decidable {A = I} _≡_) where

open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality renaming (refl to refl≡)
open import Data.Empty using (⊥-elim)
open import Shog.Model.RA.Forall.Base Ra˙ using (∀ᴿᴬ)

open RA
open RA ∀ᴿᴬ using () renaming (Carrier to A∀; _≈_ to _≈∀_; ✓ to ✓∀; _∙_ to _∙∀_;
  ε to ε∀; ⌞_⌟ to ⌞_⌟∀; _↝_ to _↝∀_; refl to refl∀; _»_ to _»∀_;
  unitˡ to unitˡ∀; ✓-ε to ✓∀-ε; ⌞⌟-ε to ⌞⌟∀-ε)

----------------------------------------------------------------------
-- Updating an element at some index

∀-upd : ∀ i → Ra˙ i .Carrier → A∀ → A∀
∀-upd i a b˙ j with i ≟ j
... | yes refl≡ = a
... | no _ = b˙ j

-- Injecting an element of a component RA

∀-inj : ∀ i → Ra˙ i .Carrier → A∀
∀-inj i a = ∀-upd i a ε∀

----------------------------------------------------------------------
-- Various properties

module _ {i : I} where

  open RA (Ra˙ i) using () renaming (Carrier to Aⁱ; _≈_ to _≈ⁱ_; ✓ to ✓ⁱ;
    _∙_ to _∙ⁱ_; ε to εⁱ; ⌞_⌟ to ⌞_⌟ⁱ; refl to reflⁱ; _↝_ to _↝ⁱ_)

  private variable
    a b : Aⁱ
    b˙ c˙ d˙ : A∀

  --------------------------------------------------------------------
  -- ∀-upd preserves ≈/✓/∙/⌞⌟/↝

  ∀-upd-cong : a ≈ⁱ b → c˙ ≈∀ d˙ → ∀-upd i a c˙ ≈∀ ∀-upd i b d˙
  ∀-upd-cong a≈b c˙≈d˙ j with i ≟ j
  ... | yes refl≡ = a≈b
  ... | no _ = c˙≈d˙ j

  ∀-upd-✓ : ✓ⁱ a → ✓∀ b˙ → ✓∀ (∀-upd i a b˙)
  ∀-upd-✓ ✓a ✓b˙ j with i ≟ j
  ... | yes refl≡ = ✓a
  ... | no _ = ✓b˙ j

  ∀-upd-∙ : ∀-upd i a c˙ ∙∀ ∀-upd i b d˙ ≈∀ ∀-upd i (a ∙ⁱ b) (c˙ ∙∀ d˙)
  ∀-upd-∙ j with i ≟ j
  ... | yes refl≡ = reflⁱ
  ... | no _ = refl (Ra˙ j)

  ∀-upd-⌞⌟ : ⌞ ∀-upd i a b˙ ⌟∀ ≈∀ ∀-upd i ⌞ a ⌟ⁱ ⌞ b˙ ⌟∀
  ∀-upd-⌞⌟ j with i ≟ j
  ... | yes refl≡ = reflⁱ
  ... | no _ = refl (Ra˙ j)

  ∀-upd-↝ :  a ↝ⁱ b  →  ∀-upd i a c˙ ↝∀ ∀-upd i b c˙
  ∀-upd-↝ a↝ⁱb d˙ ✓d˙∙ia j with i ≟ j | ✓d˙∙ia j
  ... | yes refl≡ | ✓d˙i∙a = a↝ⁱb (d˙ i) ✓d˙i∙a
  ... | no _ | ✓d˙j∙ε = ✓d˙j∙ε

  -- Double updates

  ∀-upd-upd : ∀-upd i a (∀-upd i b c˙) ≈∀ ∀-upd i a c˙
  ∀-upd-upd j with i ≟ j
  ... | yes refl≡ = reflⁱ
  ... | no i≢j with i ≟ j -- We need it to simplify ∀-upd i b c˙ j
  ...   | yes i≡j = ⊥-elim (i≢j i≡j)
  ...   | no _ = refl (Ra˙ j)

  --------------------------------------------------------------------
  -- ∀-inj preserves ≈/✓/∙/ε/⌞⌟/↝

  ∀-inj-cong : a ≈ⁱ b → ∀-inj i a ≈∀ ∀-inj i b
  ∀-inj-cong a≈b = ∀-upd-cong a≈b refl∀

  ∀-inj-✓ : ✓ⁱ a → ✓∀ (∀-inj i a)
  ∀-inj-✓ ✓a = ∀-upd-✓ ✓a ✓∀-ε

  ∀-inj-∙ : ∀-inj i a ∙∀ ∀-inj i b ≈∀ ∀-inj i (a ∙ⁱ b)
  ∀-inj-∙ = ∀-upd-∙ »∀ ∀-upd-cong reflⁱ unitˡ∀

  ∀-inj-ε : ∀-inj i εⁱ ≈∀ ε∀
  ∀-inj-ε j with i ≟ j
  ... | yes refl≡ = reflⁱ
  ... | no _ = refl (Ra˙ j)

  ∀-inj-⌞⌟ : ⌞ ∀-inj i a ⌟∀ ≈∀ ∀-inj i ⌞ a ⌟ⁱ
  ∀-inj-⌞⌟ = ∀-upd-⌞⌟ »∀ ∀-upd-cong reflⁱ ⌞⌟∀-ε

  ∀-inj-↝ :  a ↝ⁱ b  →  ∀-inj i a ↝∀ ∀-inj i b
  ∀-inj-↝ = ∀-upd-↝
