--------------------------------------------------------------------------------
-- Index-specific operations on AllRA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Syho.Model.RA using (RA)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using (Dec²)
module Syho.Model.RA.All.Index {ℓ' ℓ ℓ≈ ℓ✓} {I : Set ℓ'}
  (Ra˙ : I → RA ℓ ℓ≈ ℓ✓) (_≟_ : Dec² _≡_) where

open import Base.Eq using (refl)
open import Base.Dec using (yes; no)
open import Base.Few using (absurd)
open import Syho.Model.RA.All Ra˙ using (AllRA)

open RA using (Car; refl˜; ✓-ε; ∙-unitˡ; ⌞⌟-ε)
open RA AllRA using () renaming (Car to Aᴬ; _≈_ to _≈ᴬ_; ✓_ to ✓ᴬ_;
  _∙_ to _∙ᴬ_; ε to εᴬ; ⌞_⌟ to ⌞_⌟ᴬ; _↝_ to _↝ᴬ_; refl˜ to reflᴬ; _◇˜_ to _◇ᴬ_)

--------------------------------------------------------------------------------
-- updᴬ/upda$1 :  Updating an element at an index

updᴬ :  ∀ i →  Ra˙ i .Car →  Aᴬ →  Aᴬ
updᴬ i a b˙ j  with i ≟ j
... | yes refl =  a
... | no _ =  b˙ j

abstract

  -- Abstract version of updᴬ

  updaᴬ :  ∀ i →  Ra˙ i .Car →  Aᴬ →  Aᴬ
  updaᴬ =  updᴬ

  updaᴬ-eq :  updaᴬ ≡ updᴬ
  updaᴬ-eq =  refl

--------------------------------------------------------------------------------
-- injᴬ/inja$1 :  Injecting an element at an index

injᴬ injaᴬ :  ∀ i →  Ra˙ i .Car →  Aᴬ
injᴬ i a =  updᴬ i a εᴬ
injaᴬ i a =  updaᴬ i a εᴬ

module _ {i : I} where

  open RA (Ra˙ i) using () renaming (Car to Aⁱ; _≈_ to _≈ⁱ_; ✓_ to ✓ⁱ_;
    _∙_ to _∙ⁱ_; ε to εⁱ; ⌞_⌟ to ⌞_⌟ⁱ; refl˜ to reflⁱ; _↝_ to _↝ⁱ_)

  private variable
    a b :  Aⁱ
    b˙ c˙ d˙ :  Aᴬ

  abstract

    ----------------------------------------------------------------------------
    -- On updaᴬ

    -- updaᴬ preserves ≈/✓/∙/⌞⌟/↝

    updaᴬ-cong :  a ≈ⁱ b →  c˙ ≈ᴬ d˙ →  updaᴬ i a c˙ ≈ᴬ updaᴬ i b d˙
    updaᴬ-cong a≈b c˙≈d˙ j  with i ≟ j
    ... | yes refl =  a≈b
    ... | no _ =  c˙≈d˙ j

    updaᴬ-✓ :  ✓ⁱ a →  ✓ᴬ b˙ →  ✓ᴬ updaᴬ i a b˙
    updaᴬ-✓ ✓a ✓b˙ j  with i ≟ j
    ... | yes refl =  ✓a
    ... | no _ =  ✓b˙ j

    updaᴬ-∙ :  updaᴬ i a c˙ ∙ᴬ updaᴬ i b d˙  ≈ᴬ  updaᴬ i (a ∙ⁱ b) (c˙ ∙ᴬ d˙)
    updaᴬ-∙ j  with i ≟ j
    ... | yes refl =  reflⁱ
    ... | no _ =  Ra˙ j .refl˜

    updaᴬ-⌞⌟ :  ⌞ updaᴬ i a b˙ ⌟ᴬ  ≈ᴬ  updaᴬ i ⌞ a ⌟ⁱ ⌞ b˙ ⌟ᴬ
    updaᴬ-⌞⌟ j  with i ≟ j
    ... | yes refl =  reflⁱ
    ... | no _ =  Ra˙ j .refl˜

    updaᴬ-↝ :  a ↝ⁱ b →  updaᴬ i a c˙ ↝ᴬ updaᴬ i b c˙
    updaᴬ-↝ a↝b d˙ ✓d˙∙iac˙ j  with i ≟ j | ✓d˙∙iac˙ j
    ... | yes refl | ✓d˙i∙a =  a↝b (d˙ i) ✓d˙i∙a
    ... | no _ | ✓d˙j∙c˙j =  ✓d˙j∙c˙j

    -- Double update

    updaᴬ-2 :  updaᴬ i a (updaᴬ i b c˙) ≈ᴬ updaᴬ i a c˙
    updaᴬ-2 j  with i ≟ j
    ... | yes refl =  reflⁱ
    ... | no i≢j  with i ≟ j  -- We need this to simplify updaᴬ i b c˙ j
    ...   | yes i≡j =  absurd (i≢j i≡j)
    ...   | no _ =  Ra˙ j .refl˜

    ----------------------------------------------------------------------------
    -- On injaᴬ

    -- injaᴬ preserves ≈/✓/∙/ε/⌞⌟/↝

    injaᴬ-cong :  a ≈ⁱ b →  injaᴬ i a  ≈ᴬ  injaᴬ i b
    injaᴬ-cong a≈b =  updaᴬ-cong a≈b reflᴬ

    injaᴬ-✓ :  ✓ⁱ a →  ✓ᴬ injaᴬ i a
    injaᴬ-✓ ✓a =  updaᴬ-✓ ✓a (✓-ε AllRA)

    injaᴬ-∙ :  injaᴬ i a ∙ᴬ injaᴬ i b  ≈ᴬ  injaᴬ i (a ∙ⁱ b)
    injaᴬ-∙ =  updaᴬ-∙ ◇ᴬ updaᴬ-cong reflⁱ (∙-unitˡ AllRA)

    injaᴬ-ε :  injaᴬ i εⁱ ≈ᴬ εᴬ
    injaᴬ-ε j  with i ≟ j
    ... | yes refl =  reflⁱ
    ... | no _ =  Ra˙ j .refl˜

    injaᴬ-⌞⌟ :  ⌞ injaᴬ i a ⌟ᴬ  ≈ᴬ  injaᴬ i ⌞ a ⌟ⁱ
    injaᴬ-⌞⌟ =  updaᴬ-⌞⌟ ◇ᴬ updaᴬ-cong reflⁱ (⌞⌟-ε AllRA)

    injaᴬ-↝ :  a ↝ⁱ b →  injaᴬ i a ↝ᴬ injaᴬ i b
    injaᴬ-↝ =  updaᴬ-↝
