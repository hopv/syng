--------------------------------------------------------------------------------
-- Global ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Glob where

open import Base.Level using (2ᴸ)
open import Base.Func using (_$_)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using (yes; no)
open import Base.Prod using (_,_; proj₀; proj₁)
open import Base.Nat using (ℕ; _≡?_)
open import Base.Nmap using (updᵈⁿᵐ; updaᵈⁿᵐ; updaᵈⁿᵐ-eq)
open import Syho.Model.ERA using (ERA)
open import Syho.Model.ERA.Top using (⊤ᴱᴿᴬ)
open import Syho.Model.ERA.Ind using (Indˣᴱᴿᴬ; Ind□ᴱᴿᴬ)

open ERA using (Env; Res; _≈ᴱ_; _≈_; _✓_; _∙_; ε; ⌞_⌟; refl˜ᴱ; ◠˜ᴱ_; _◇˜ᴱ_;
  refl˜; ◠˜_; _◇˜_; ∙-congˡ; ∙-unitˡ; ∙-comm; ∙-assocˡ; ✓-resp; ✓-rem; ✓-ε;
  ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem; ⌞⌟-ε)

--------------------------------------------------------------------------------
-- Globᴱᴿᴬ :  Global ERA

pattern indˣ =  0
pattern ind□ =  1

Globᴱᴿᴬ˙ :  ℕ →  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ 2ᴸ
Globᴱᴿᴬ˙ indˣ =  Indˣᴱᴿᴬ
Globᴱᴿᴬ˙ ind□ =  Ind□ᴱᴿᴬ
Globᴱᴿᴬ˙ _ =  ⊤ᴱᴿᴬ

Globᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ 2ᴸ
Globᴱᴿᴬ .Env =  ∀ i →  Globᴱᴿᴬ˙ i .Env
Globᴱᴿᴬ .Res =  ∀ i →  Globᴱᴿᴬ˙ i .Res
Globᴱᴿᴬ ._≈ᴱ_ E F =  ∀ i →  Globᴱᴿᴬ˙ i ._≈ᴱ_ (E i) (F i)
Globᴱᴿᴬ ._≈_ a b =  ∀ i →  Globᴱᴿᴬ˙ i ._≈_ (a i) (b i)
Globᴱᴿᴬ ._✓_ E a =  ∀ i →  Globᴱᴿᴬ˙ i ._✓_ (E i) (a i)
Globᴱᴿᴬ ._∙_ a b i =  Globᴱᴿᴬ˙ i ._∙_ (a i) (b i)
Globᴱᴿᴬ .ε i =  Globᴱᴿᴬ˙ i .ε
Globᴱᴿᴬ .⌞_⌟ a i =  Globᴱᴿᴬ˙ i .⌞_⌟ (a i)
Globᴱᴿᴬ .refl˜ᴱ i =  Globᴱᴿᴬ˙ i .refl˜ᴱ
Globᴱᴿᴬ .◠˜ᴱ_ E≈F i =  Globᴱᴿᴬ˙ i .◠˜ᴱ_ (E≈F i)
Globᴱᴿᴬ ._◇˜ᴱ_ E≈F F≈G i =  Globᴱᴿᴬ˙ i ._◇˜ᴱ_ (E≈F i) (F≈G i)
Globᴱᴿᴬ .refl˜ i =  Globᴱᴿᴬ˙ i .refl˜
Globᴱᴿᴬ .◠˜_ a≈b i =  Globᴱᴿᴬ˙ i .◠˜_ (a≈b i)
Globᴱᴿᴬ ._◇˜_ a≈b b≈c i =  Globᴱᴿᴬ˙ i ._◇˜_ (a≈b i) (b≈c i)
Globᴱᴿᴬ .∙-congˡ a≈b i =  Globᴱᴿᴬ˙ i .∙-congˡ (a≈b i)
Globᴱᴿᴬ .∙-unitˡ i =  Globᴱᴿᴬ˙ i .∙-unitˡ
Globᴱᴿᴬ .∙-comm i =  Globᴱᴿᴬ˙ i .∙-comm
Globᴱᴿᴬ .∙-assocˡ i =  Globᴱᴿᴬ˙ i .∙-assocˡ
Globᴱᴿᴬ .✓-resp E≈F a≈b E✓a i =  Globᴱᴿᴬ˙ i .✓-resp (E≈F i) (a≈b i) (E✓a i)
Globᴱᴿᴬ .✓-rem ✓a∙b i =  Globᴱᴿᴬ˙ i .✓-rem (✓a∙b i)
Globᴱᴿᴬ .✓-ε i =  Globᴱᴿᴬ˙ i .✓-ε
Globᴱᴿᴬ .⌞⌟-cong a≈b i =  Globᴱᴿᴬ˙ i .⌞⌟-cong (a≈b i)
Globᴱᴿᴬ .⌞⌟-add =
  (λ i → Globᴱᴿᴬ˙ i .⌞⌟-add .proj₀) , λ i → Globᴱᴿᴬ˙ i .⌞⌟-add .proj₁
Globᴱᴿᴬ .⌞⌟-unitˡ i =  Globᴱᴿᴬ˙ i .⌞⌟-unitˡ
Globᴱᴿᴬ .⌞⌟-idem i =  Globᴱᴿᴬ˙ i .⌞⌟-idem

open ERA Globᴱᴿᴬ using () renaming (Env to Envᴳ; Res to Resᴳ; _≈_ to _≈ᴳ_;
  _✓_ to _✓ᴳ_; _∙_ to _∙ᴳ_; ε to εᴳ; ⌞_⌟ to ⌞_⌟ᴳ; _↝_ to _↝ᴳ_; refl˜ to refl˜ᴳ;
  _◇˜_ to _◇˜ᴳ_)

--------------------------------------------------------------------------------
-- Update & inject at an index

-- updᴱᴳ, updᴳ :  Update an element at an index

updᴱᴳ :  ∀ i →  Globᴱᴿᴬ˙ i .Env →  Envᴳ →  Envᴳ
updᴱᴳ =  updᵈⁿᵐ

updᴳ :  ∀ i →  Globᴱᴿᴬ˙ i .Res →  Resᴳ →  Resᴳ
updᴳ =  updᵈⁿᵐ

-- injᴳ :  Inject an element at an index

injᴳ :  ∀ i →  Globᴱᴿᴬ˙ i .Res →  Resᴳ
injᴳ i a =  updᴳ i a εᴳ

module _ {i : ℕ} where

  open ERA (Globᴱᴿᴬ˙ i) using () renaming (Env to Envⁱ; Res to Resⁱ;
    _≈_ to _≈ⁱ_; _✓_ to _✓ⁱ_; _∙_ to _∙ⁱ_; ε to εⁱ; ⌞_⌟ to ⌞_⌟ⁱ;
    refl˜ to refl˜ⁱ; _↝_ to _↝ⁱ_)

  private variable
    E˙ F˙ G˙ :  Envᴳ
    b˙ c˙ d˙ :  Resᴳ
    E F :  Envⁱ
    a b :  Resⁱ

  abstract

    ----------------------------------------------------------------------------
    -- On updᴳ

    -- updᴳ preserves ≈/✓/∙/⌞⌟/↝

    updᴳ-cong :  a ≈ⁱ b →  c˙ ≈ᴳ d˙ →  updᴳ i a c˙ ≈ᴳ updᴳ i b d˙
    updᴳ-cong a≈b c˙≈d˙ j  with i ≡? j
    ... | no _ =  c˙≈d˙ j
    ... | yes refl =  a≈b

    updᴳ-✓ :  E˙ i ✓ⁱ a →  E˙ ✓ᴳ b˙ →  E˙ ✓ᴳ updᴳ i a b˙
    updᴳ-✓ Ei✓a E✓b˙ j  with i ≡? j
    ... | no _ =  E✓b˙ j
    ... | yes refl =  Ei✓a

    updᴳ-∙ :  updᴳ i a c˙ ∙ᴳ updᴳ i b d˙  ≈ᴳ  updᴳ i (a ∙ⁱ b) (c˙ ∙ᴳ d˙)
    updᴳ-∙ j  with i ≡? j
    ... | no _ =  Globᴱᴿᴬ˙ j .refl˜
    ... | yes refl =  refl˜ⁱ

    updᴳ-⌞⌟ :  ⌞ updᴳ i a b˙ ⌟ᴳ  ≈ᴳ  updᴳ i ⌞ a ⌟ⁱ ⌞ b˙ ⌟ᴳ
    updᴳ-⌞⌟ j  with i ≡? j
    ... | no _ =  Globᴱᴿᴬ˙ j .refl˜
    ... | yes refl =  refl˜ⁱ

    updᴳ-↝ :  (E˙ i , a) ↝ⁱ (E˙ i , b) →
      (E˙ , updᴳ i a c˙) ↝ᴳ (E˙ , updᴳ i b c˙)
    updᴳ-↝ Eia↝Eib d˙ E✓d∙iac j  with i ≡? j | E✓d∙iac j
    ... | no _ | E✓dj∙cj =  E✓dj∙cj
    ... | yes refl | Ei✓d˙i∙a =  Eia↝Eib (d˙ i) Ei✓d˙i∙a

    updᴱᴳ-updᴳ-↝ :  (E , a) ↝ⁱ (F , b) →
      (updᴱᴳ i E G˙ , updᴳ i a c˙) ↝ᴳ (updᴱᴳ i F G˙ , updᴳ i b c˙)
    updᴱᴳ-updᴳ-↝ Ea↝Fb d˙ iEG✓d∙iac j  with i ≡? j | iEG✓d∙iac j
    ... | no _ | Gj✓dj∙cj =  Gj✓dj∙cj
    ... | yes refl | E✓d˙i∙a =  Ea↝Fb (d˙ i) E✓d˙i∙a

    ----------------------------------------------------------------------------
    -- On injᴳ

    -- injᴳ preserves ≈/✓/∙/ε/⌞⌟/↝

    injᴳ-cong :  a ≈ⁱ b →  injᴳ i a  ≈ᴳ  injᴳ i b
    injᴳ-cong a≈b =  updᴳ-cong a≈b refl˜ᴳ

    injᴳ-✓ :  E˙ i ✓ⁱ a →  E˙ ✓ᴳ injᴳ i a
    injᴳ-✓ Ei✓a =  updᴳ-✓ Ei✓a $ Globᴱᴿᴬ .✓-ε

    injᴳ-∙ :  injᴳ i a ∙ᴳ injᴳ i b  ≈ᴳ  injᴳ i (a ∙ⁱ b)
    injᴳ-∙ =  updᴳ-∙ ◇˜ᴳ updᴳ-cong refl˜ⁱ $ Globᴱᴿᴬ .∙-unitˡ

    injᴳ-ε :  injᴳ i εⁱ ≈ᴳ εᴳ
    injᴳ-ε j  with i ≡? j
    ... | no _ =  Globᴱᴿᴬ˙ j .refl˜
    ... | yes refl =  refl˜ⁱ

    injᴳ-⌞⌟ :  ⌞ injᴳ i a ⌟ᴳ  ≈ᴳ  injᴳ i ⌞ a ⌟ⁱ
    injᴳ-⌞⌟ =  updᴳ-⌞⌟ ◇˜ᴳ updᴳ-cong refl˜ⁱ $ ⌞⌟-ε Globᴱᴿᴬ

    injᴳ-↝ :  (E˙ i , a) ↝ⁱ (E˙ i , b) →  (E˙ , injᴳ i a) ↝ᴳ (E˙ , injᴳ i b)
    injᴳ-↝ =  updᴳ-↝

    updᴱᴳ-injᴳ-↝ :  (E , a) ↝ⁱ (F , b) →
      (updᴱᴳ i E G˙ , injᴳ i a) ↝ᴳ (updᴱᴳ i F G˙ , injᴳ i b)
    updᴱᴳ-injᴳ-↝ =  updᴱᴳ-updᴳ-↝
