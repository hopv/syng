--------------------------------------------------------------------------------
-- Index-specific operations on Allᴿᴬ
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Shog.Model.RA using (RA)
open import Base.Eq using (_≡_)
open import Base.Dec using (Dec²)
module Shog.Model.RA.All.Point {ℓ' ℓ ℓ≈ ℓ✓} {I : Set ℓ'}
  (Ra˙ : I → RA ℓ ℓ≈ ℓ✓) (_≟_ : Dec² _≡_) where

open import Base.Eq using (refl⁼)
open import Base.Dec using (yes; no)
open import Base.Few using (absurd)
open import Shog.Model.RA.All Ra˙ using (Allᴿᴬ)

open RA
open RA Allᴿᴬ using () renaming (Car to Aᴬ; _≈_ to _≈ᴬ_; ✓_ to ✓ᴬ_;
  _∙_ to _∙ᴬ_; ε to εᴬ; ⌞_⌟ to ⌞_⌟ᴬ; _↝_ to _↝ᴬ_; refl˜ to reflᴬ; _»˜_ to _»ᴬ_;
  ∙-unitˡ to ∙-unitˡᴬ; ✓-ε to ✓ᴬ-ε; ⌞⌟-ε to ⌞⌟ᴬ-ε)

--------------------------------------------------------------------------------
-- updᴬ: Updating an element at an index

updᴬ :  ∀ i →  Ra˙ i .Car →  Aᴬ →  Aᴬ
updᴬ i a b˙ j with i ≟ j
... | yes refl⁼ =  a
... | no _ =  b˙ j

--------------------------------------------------------------------------------
-- injᴬ: Injecting an element at an index

injᴬ :  ∀ i →  Ra˙ i .Car →  Aᴬ
injᴬ i a =  updᴬ i a εᴬ

module _ {i : I} where

  open RA (Ra˙ i) using () renaming (Car to Aⁱ; _≈_ to _≈ⁱ_; ✓_ to ✓ⁱ_;
    _∙_ to _∙ⁱ_; ε to εⁱ; ⌞_⌟ to ⌞_⌟ⁱ; refl˜ to reflⁱ; _↝_ to _↝ⁱ_)

  private variable
    a b :  Aⁱ
    b˙ c˙ d˙ :  Aᴬ

  ------------------------------------------------------------------------------
  -- On updᴬ

  abstract

    -- updᴬ preserves ≈/✓/∙/⌞⌟/↝

    updᴬ-cong :  a ≈ⁱ b →  c˙ ≈ᴬ d˙ →  updᴬ i a c˙ ≈ᴬ updᴬ i b d˙
    updᴬ-cong a≈b c˙≈d˙ j with i ≟ j
    ... | yes refl⁼ =  a≈b
    ... | no _ =  c˙≈d˙ j

    updᴬ-✓ :  ✓ⁱ a →  ✓ᴬ b˙ →  ✓ᴬ updᴬ i a b˙
    updᴬ-✓ ✓a ✓b˙ j with i ≟ j
    ... | yes refl⁼ =  ✓a
    ... | no _ =  ✓b˙ j

    updᴬ-∙ :  updᴬ i a c˙ ∙ᴬ updᴬ i b d˙  ≈ᴬ  updᴬ i (a ∙ⁱ b) (c˙ ∙ᴬ d˙)
    updᴬ-∙ j with i ≟ j
    ... | yes refl⁼ =  reflⁱ
    ... | no _ =  Ra˙ j .refl˜

    updᴬ-⌞⌟ :  ⌞ updᴬ i a b˙ ⌟ᴬ  ≈ᴬ  updᴬ i ⌞ a ⌟ⁱ ⌞ b˙ ⌟ᴬ
    updᴬ-⌞⌟ j with i ≟ j
    ... | yes refl⁼ =  reflⁱ
    ... | no _ =  Ra˙ j .refl˜

    updᴬ-↝ :  a ↝ⁱ b →  updᴬ i a c˙ ↝ᴬ updᴬ i b c˙
    updᴬ-↝ a↝ⁱb d˙ ✓d˙∙ia j with i ≟ j | ✓d˙∙ia j
    ... | yes refl⁼ | ✓d˙i∙a =  a↝ⁱb (d˙ i) ✓d˙i∙a
    ... | no _ | ✓d˙j∙ε =  ✓d˙j∙ε

    -- Double update

    updᴬ-2 :  updᴬ i a (updᴬ i b c˙) ≈ᴬ updᴬ i a c˙
    updᴬ-2 j with i ≟ j
    ... | yes refl⁼ =  reflⁱ
    ... | no i≢j with i ≟ j  -- We need this to simplify updᴬ i b c˙ j
    ...   | yes i≡j =  absurd (i≢j i≡j)
    ...   | no _ =  Ra˙ j .refl˜

  ------------------------------------------------------------------------------
  -- On injᴬ

  abstract

    -- injᴬ preserves ≈/✓/∙/ε/⌞⌟/↝

    injᴬ-cong :  a ≈ⁱ b →  injᴬ i a  ≈ᴬ  injᴬ i b
    injᴬ-cong a≈b =  updᴬ-cong a≈b reflᴬ

    injᴬ-✓ :  ✓ⁱ a →  ✓ᴬ injᴬ i a
    injᴬ-✓ ✓a =  updᴬ-✓ ✓a ✓ᴬ-ε

    injᴬ-∙ :  injᴬ i a ∙ᴬ injᴬ i b  ≈ᴬ  injᴬ i (a ∙ⁱ b)
    injᴬ-∙ =  updᴬ-∙ »ᴬ updᴬ-cong reflⁱ ∙-unitˡᴬ

    injᴬ-ε :  injᴬ i εⁱ ≈ᴬ εᴬ
    injᴬ-ε j with i ≟ j
    ... | yes refl⁼ =  reflⁱ
    ... | no _ =  Ra˙ j .refl˜

    injᴬ-⌞⌟ :  ⌞ injᴬ i a ⌟ᴬ  ≈ᴬ  injᴬ i ⌞ a ⌟ⁱ
    injᴬ-⌞⌟ =  updᴬ-⌞⌟ »ᴬ updᴬ-cong reflⁱ ⌞⌟ᴬ-ε

    injᴬ-↝ :  a ↝ⁱ b →  injᴬ i a ↝ᴬ injᴬ i b
    injᴬ-↝ =  updᴬ-↝
