--------------------------------------------------------------------------------
-- Injection on ∀ᴿᴬ
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Shog.Model.RA using (RA)
open import Base.Eq using (_≡_)
open import Base.Dec using (Dec²)
module Shog.Model.RA.Forall.Point {ℓ' ℓ ℓ≈ ℓ✓} {I : Set ℓ'}
  {Ra˙ : I → RA ℓ ℓ≈ ℓ✓} (_≟_ : Dec² _≡_) where

open import Base.Eq using (refl⁼)
open import Base.Dec using (yes; no)
open import Base.NElem using (0-ary)
open import Shog.Model.RA.Forall.Base Ra˙ using (∀ᴿᴬ)

open RA
open RA ∀ᴿᴬ using () renaming (Car to Aᴬ; _≈_ to _≈ᴬ_; ✓ to ✓ᴬ; _∙_ to _∙ᴬ_;
  ε to εᴬ; ⌞_⌟ to ⌞_⌟ᴬ; _↝_ to _↝ᴬ_; refl to reflᴬ; _»_ to _»ᴬ_;
  unitˡ to unitˡᴬ; ✓-ε to ✓ᴬ-ε; ⌞⌟-ε to ⌞⌟ᴬ-ε)

--------------------------------------------------------------------------------
-- Updating an element at some index

∀-upd : ∀ i → Ra˙ i .Car → Aᴬ → Aᴬ
∀-upd i a b˙ j with i ≟ j
... | yes refl⁼ = a
... | no _ = b˙ j

-- Injecting an element of a component RA

∀-inj : ∀ i → Ra˙ i .Car → Aᴬ
∀-inj i a = ∀-upd i a εᴬ

--------------------------------------------------------------------------------
-- Various properties

module _ {i : I} where

  open RA (Ra˙ i) using () renaming (Car to Aⁱ; _≈_ to _≈ⁱ_; ✓ to ✓ⁱ;
    _∙_ to _∙ⁱ_; ε to εⁱ; ⌞_⌟ to ⌞_⌟ⁱ; refl to reflⁱ; _↝_ to _↝ⁱ_)

  private variable
    a b : Aⁱ
    b˙ c˙ d˙ : Aᴬ

  abstract

    -- ∀-upd preserves ≈/✓/∙/⌞⌟/↝

    ∀-upd-cong :  a ≈ⁱ b  →  c˙ ≈ᴬ d˙  →  ∀-upd i a c˙ ≈ᴬ ∀-upd i b d˙
    ∀-upd-cong a≈b c˙≈d˙ j with i ≟ j
    ... | yes refl⁼ = a≈b
    ... | no _ = c˙≈d˙ j

    ∀-upd-✓ :  ✓ⁱ a  →  ✓ᴬ b˙  →  ✓ᴬ (∀-upd i a b˙)
    ∀-upd-✓ ✓a ✓b˙ j with i ≟ j
    ... | yes refl⁼ = ✓a
    ... | no _ = ✓b˙ j

    ∀-upd-∙ :  ∀-upd i a c˙ ∙ᴬ ∀-upd i b d˙  ≈ᴬ  ∀-upd i (a ∙ⁱ b) (c˙ ∙ᴬ d˙)
    ∀-upd-∙ j with i ≟ j
    ... | yes refl⁼ = reflⁱ
    ... | no _ = refl (Ra˙ j)

    ∀-upd-⌞⌟ :  ⌞ ∀-upd i a b˙ ⌟ᴬ  ≈ᴬ  ∀-upd i ⌞ a ⌟ⁱ ⌞ b˙ ⌟ᴬ
    ∀-upd-⌞⌟ j with i ≟ j
    ... | yes refl⁼ = reflⁱ
    ... | no _ = refl (Ra˙ j)

    ∀-upd-↝ :  a ↝ⁱ b  →  ∀-upd i a c˙ ↝ᴬ ∀-upd i b c˙
    ∀-upd-↝ a↝ⁱb d˙ ✓d˙∙ia j with i ≟ j | ✓d˙∙ia j
    ... | yes refl⁼ | ✓d˙i∙a = a↝ⁱb (d˙ i) ✓d˙i∙a
    ... | no _ | ✓d˙j∙ε = ✓d˙j∙ε

    -- Double updates

    ∀-upd-upd : ∀-upd i a (∀-upd i b c˙) ≈ᴬ ∀-upd i a c˙
    ∀-upd-upd j with i ≟ j
    ... | yes refl⁼ = reflⁱ
    ... | no i≢j with i ≟ j -- We need it to simplify ∀-upd i b c˙ j
    ...   | yes i≡j = 0-ary (i≢j i≡j)
    ...   | no _ = refl (Ra˙ j)

    -- ∀-inj preserves ≈/✓/∙/ε/⌞⌟/↝

    ∀-inj-cong :  a ≈ⁱ b  →  ∀-inj i a  ≈ᴬ  ∀-inj i b
    ∀-inj-cong a≈b = ∀-upd-cong a≈b reflᴬ

    ∀-inj-✓ :  ✓ⁱ a  →  ✓ᴬ (∀-inj i a)
    ∀-inj-✓ ✓a = ∀-upd-✓ ✓a ✓ᴬ-ε

    ∀-inj-∙ :  ∀-inj i a ∙ᴬ ∀-inj i b  ≈ᴬ  ∀-inj i (a ∙ⁱ b)
    ∀-inj-∙ = ∀-upd-∙ »ᴬ ∀-upd-cong reflⁱ unitˡᴬ

    ∀-inj-ε : ∀-inj i εⁱ ≈ᴬ εᴬ
    ∀-inj-ε j with i ≟ j
    ... | yes refl⁼ = reflⁱ
    ... | no _ = refl (Ra˙ j)

    ∀-inj-⌞⌟ :  ⌞ ∀-inj i a ⌟ᴬ  ≈ᴬ  ∀-inj i ⌞ a ⌟ⁱ
    ∀-inj-⌞⌟ = ∀-upd-⌞⌟ »ᴬ ∀-upd-cong reflⁱ ⌞⌟ᴬ-ε

    ∀-inj-↝ :  a ↝ⁱ b  →  ∀-inj i a ↝ᴬ ∀-inj i b
    ∀-inj-↝ = ∀-upd-↝
