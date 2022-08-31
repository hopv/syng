--------------------------------------------------------------------------------
-- Global ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Glob where

open import Base.Level using (Level; 2ᴸ)
open import Base.Func using (_$_)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using (yes; no)
open import Base.Prod using (∑-syntax; _,_; proj₀; proj₁; -,_)
open import Base.Nat using (ℕ; ṡ_; _≡?_; ≡?-refl)
open import Base.Nmap using (updᴰᴺᴹ)
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Top using (⊤ᴱᴿᴬ)
open import Syho.Model.ERA.Ind using (Indˣᴱᴿᴬ; Ind□ᴱᴿᴬ)

open ERA using (Env; Res; _≈_; _✓_; _∙_; ε; ⌞_⌟; refl˜; ◠˜_; _◇˜_; ⊑-refl;
  ∙-congˡ; ∙-unitˡ; ∙-comm; ∙-assocˡ; ✓-resp; ✓-rem; ✓-ε; ⌞⌟-cong; ⌞⌟-add;
  ⌞⌟-unitˡ; ⌞⌟-idem; ⌞⌟-ε)

--------------------------------------------------------------------------------
-- Global ERA

-- Ids of ERAs

pattern indˣ =  0
pattern ind□ =  1
pattern elseᴳ =  ṡ ṡ _

-- Map of ERAs

Globᴱᴿᴬ˙ :  ℕ →  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ
Globᴱᴿᴬ˙ indˣ =  Indˣᴱᴿᴬ
Globᴱᴿᴬ˙ ind□ =  Ind□ᴱᴿᴬ
Globᴱᴿᴬ˙ elseᴳ =  ⊤ᴱᴿᴬ

-- Globᴱᴿᴬ :  Global ERA

Globᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ
Globᴱᴿᴬ .Env =  ∀ i →  Globᴱᴿᴬ˙ i .Env
Globᴱᴿᴬ .Res =  ∀ i →  Globᴱᴿᴬ˙ i .Res
Globᴱᴿᴬ ._≈_ a b =  ∀ i →  Globᴱᴿᴬ˙ i ._≈_ (a i) (b i)
Globᴱᴿᴬ ._✓_ E a =  ∀ i →  Globᴱᴿᴬ˙ i ._✓_ (E i) (a i)
Globᴱᴿᴬ ._∙_ a b i =  Globᴱᴿᴬ˙ i ._∙_ (a i) (b i)
Globᴱᴿᴬ .ε i =  Globᴱᴿᴬ˙ i .ε
Globᴱᴿᴬ .⌞_⌟ a i =  Globᴱᴿᴬ˙ i .⌞_⌟ (a i)
Globᴱᴿᴬ .refl˜ i =  Globᴱᴿᴬ˙ i .refl˜
Globᴱᴿᴬ .◠˜_ a≈b i =  Globᴱᴿᴬ˙ i .◠˜_ (a≈b i)
Globᴱᴿᴬ ._◇˜_ a≈b b≈c i =  Globᴱᴿᴬ˙ i ._◇˜_ (a≈b i) (b≈c i)
Globᴱᴿᴬ .∙-congˡ a≈b i =  Globᴱᴿᴬ˙ i .∙-congˡ (a≈b i)
Globᴱᴿᴬ .∙-unitˡ i =  Globᴱᴿᴬ˙ i .∙-unitˡ
Globᴱᴿᴬ .∙-comm i =  Globᴱᴿᴬ˙ i .∙-comm
Globᴱᴿᴬ .∙-assocˡ i =  Globᴱᴿᴬ˙ i .∙-assocˡ
Globᴱᴿᴬ .✓-resp a≈b E✓a i =  Globᴱᴿᴬ˙ i .✓-resp (a≈b i) (E✓a i)
Globᴱᴿᴬ .✓-rem ✓a∙b i =  Globᴱᴿᴬ˙ i .✓-rem (✓a∙b i)
Globᴱᴿᴬ .✓-ε i =  Globᴱᴿᴬ˙ i .✓-ε
Globᴱᴿᴬ .⌞⌟-cong a≈b i =  Globᴱᴿᴬ˙ i .⌞⌟-cong (a≈b i)
Globᴱᴿᴬ .⌞⌟-add =
  (λ i → Globᴱᴿᴬ˙ i .⌞⌟-add .proj₀) , λ i → Globᴱᴿᴬ˙ i .⌞⌟-add .proj₁
Globᴱᴿᴬ .⌞⌟-unitˡ i =  Globᴱᴿᴬ˙ i .⌞⌟-unitˡ
Globᴱᴿᴬ .⌞⌟-idem i =  Globᴱᴿᴬ˙ i .⌞⌟-idem

open ERA Globᴱᴿᴬ public using () renaming (Env to Envᴳ)

open ERA Globᴱᴿᴬ using () renaming (Res to Resᴳ; _≈_ to _≈ᴳ_; _⊑_ to _⊑ᴳ_;
  _✓_ to _✓ᴳ_; _∙_ to _∙ᴳ_; ε to εᴳ; ⌞_⌟ to ⌞_⌟ᴳ; _↝_ to _↝ᴳ_; refl˜ to refl˜ᴳ;
  _◇˜_ to _◇˜ᴳ_)

--------------------------------------------------------------------------------
-- Update & inject at an index

-- updᴱᴳ, updᴳ :  Update an element at an index

updᴱᴳ :  ∀ i →  Globᴱᴿᴬ˙ i .Env →  Envᴳ →  Envᴳ
updᴱᴳ =  updᴰᴺᴹ

updᴳ :  ∀ i →  Globᴱᴿᴬ˙ i .Res →  Resᴳ →  Resᴳ
updᴳ =  updᴰᴺᴹ

-- injᴳ :  Inject an element at an index

injᴳ :  ∀ i →  Globᴱᴿᴬ˙ i .Res →  Resᴳ
injᴳ i a =  updᴳ i a εᴳ

module _ {i : ℕ} where

  open ERA (Globᴱᴿᴬ˙ i) using () renaming (Env to Envⁱ; Res to Resⁱ;
    _≈_ to _≈ⁱ_; _⊑_ to _⊑ⁱ_; _✓_ to _✓ⁱ_; _∙_ to _∙ⁱ_; ε to εⁱ; ⌞_⌟ to ⌞_⌟ⁱ;
    _↝_ to _↝ⁱ_; refl˜ to refl˜ⁱ)

  private variable
    E˙ F˙ G˙ :  Envᴳ
    a˙ b˙ c˙ d˙ :  Resᴳ
    E F :  Envⁱ
    a b :  Resⁱ
    ł :  Level
    X :  Set ł
    bˣ :  X → Resⁱ
    Fˣ :  X → Envⁱ

  abstract

    -- ⊑ᴳ distributes

    ⊑ᴳ⇒⊑ :  a˙ ⊑ᴳ b˙ →  a˙ i ⊑ⁱ b˙ i
    ⊑ᴳ⇒⊑ (-, c∙a≈b) =  -, c∙a≈b i

    ----------------------------------------------------------------------------
    -- On updᴱᴳ

    -- Self updᴱᴳ preserves ✓

    updᴱᴳ-self-✓ :  E˙ ✓ᴳ a˙ →  updᴱᴳ i (E˙ i) E˙ ✓ᴳ a˙
    updᴱᴳ-self-✓ E✓a j  with j ≡? i
    … | yes refl =  E✓a i
    … | no _ =  E✓a j

    ----------------------------------------------------------------------------
    -- On updᴳ

    -- updᴳ preserves ≈/⊑/✓/∙/⌞⌟/↝

    updᴳ-cong :  a ≈ⁱ b →  c˙ ≈ᴳ d˙ →  updᴳ i a c˙ ≈ᴳ updᴳ i b d˙
    updᴳ-cong a≈b c˙≈d˙ j  with j ≡? i
    … | no _ =  c˙≈d˙ j
    … | yes refl =  a≈b

    updᴳ-mono :  a ⊑ⁱ b →  c˙ ⊑ᴳ d˙ →  updᴳ i a c˙ ⊑ᴳ updᴳ i b d˙
    updᴳ-mono _ _ .proj₀ =  updᴳ i _ _
    updᴳ-mono (-, e∙a≈b) (-, f˙∙c˙≈d˙) .proj₁ j  with j ≡? i
    … | no _ =  f˙∙c˙≈d˙ j
    … | yes refl =  e∙a≈b

    updᴳ-✓ :  E˙ i ✓ⁱ a →  E˙ ✓ᴳ b˙ →  E˙ ✓ᴳ updᴳ i a b˙
    updᴳ-✓ Ei✓a E✓b˙ j  with j ≡? i
    … | no _ =  E✓b˙ j
    … | yes refl =  Ei✓a

    updᴳ-∙ :  updᴳ i a c˙ ∙ᴳ updᴳ i b d˙  ≈ᴳ  updᴳ i (a ∙ⁱ b) (c˙ ∙ᴳ d˙)
    updᴳ-∙ j  with j ≡? i
    … | no _ =  Globᴱᴿᴬ˙ j .refl˜
    … | yes refl =  refl˜ⁱ

    updᴳ-⌞⌟ :  ⌞ updᴳ i a b˙ ⌟ᴳ  ≈ᴳ  updᴳ i ⌞ a ⌟ⁱ ⌞ b˙ ⌟ᴳ
    updᴳ-⌞⌟ j  with j ≡? i
    … | no _ =  Globᴱᴿᴬ˙ j .refl˜
    … | yes refl =  refl˜ⁱ

    updᴳ-↝ :  (E˙ i , a)  ↝ⁱ  (λ x → E˙ i , bˣ x)  →
              (E˙ , updᴳ i a c˙)  ↝ᴳ  λ x → (E˙ , updᴳ i (bˣ x) c˙)
    updᴳ-↝ {E˙} {bˣ = bˣ} {c˙} Eia↝Eib d˙ E✓d∙iac  with E✓d∙iac i
    … | Ei✓di∙a  rewrite ≡?-refl {i}  =  body
     where
      body :  ∑ x , E˙ ✓ᴳ d˙ ∙ᴳ updᴳ i (bˣ x) c˙
      body .proj₀ =  Eia↝Eib _ Ei✓di∙a .proj₀
      body .proj₁ j  with j ≡? i | E✓d∙iac j
      … | no _ | E✓dj∙cj =  E✓dj∙cj
      … | yes refl | _ =  Eia↝Eib _ Ei✓di∙a .proj₁

    updᴱᴳ-updᴳ-↝ :  (E˙ i , a)  ↝ⁱ  (λ x → Fˣ x , bˣ x)  →
      (E˙ , updᴳ i a c˙)  ↝ᴳ  λ x → updᴱᴳ i (Fˣ x) E˙ , updᴳ i (bˣ x) c˙
    updᴱᴳ-updᴳ-↝ {E˙} {Fˣ = Fˣ} {bˣ} {c˙} Eia↝Fb d˙ E✓d∙iac  with E✓d∙iac i
    … | Ei✓di∙a  rewrite ≡?-refl {i}  =  body
     where
      body :  ∑ x , updᴱᴳ i (Fˣ x) E˙ ✓ᴳ d˙ ∙ᴳ updᴳ i (bˣ x) c˙
      body .proj₀ =  Eia↝Fb _ Ei✓di∙a .proj₀
      body .proj₁ j  with j ≡? i | E✓d∙iac j
      … | no _ | E✓dj∙cj =  E✓dj∙cj
      … | yes refl | _ =  Eia↝Fb _ Ei✓di∙a .proj₁

    ----------------------------------------------------------------------------
    -- On injᴳ

    -- injᴳ preserves ≈/✓/∙/ε/⌞⌟/↝

    injᴳ-cong :  a ≈ⁱ b →  injᴳ i a  ≈ᴳ  injᴳ i b
    injᴳ-cong a≈b =  updᴳ-cong a≈b refl˜ᴳ

    injᴳ-mono :  a ⊑ⁱ b →  injᴳ i a  ⊑ᴳ  injᴳ i b
    injᴳ-mono a⊑b =  updᴳ-mono a⊑b $ ⊑-refl Globᴱᴿᴬ

    injᴳ-✓ :  E˙ i ✓ⁱ a →  E˙ ✓ᴳ injᴳ i a
    injᴳ-✓ Ei✓a =  updᴳ-✓ Ei✓a $ Globᴱᴿᴬ .✓-ε

    injᴳ-∙ :  injᴳ i a ∙ᴳ injᴳ i b  ≈ᴳ  injᴳ i (a ∙ⁱ b)
    injᴳ-∙ =  updᴳ-∙ ◇˜ᴳ updᴳ-cong refl˜ⁱ $ Globᴱᴿᴬ .∙-unitˡ

    injᴳ-ε :  injᴳ i εⁱ ≈ᴳ εᴳ
    injᴳ-ε j  with j ≡? i
    … | no _ =  Globᴱᴿᴬ˙ j .refl˜
    … | yes refl =  refl˜ⁱ

    injᴳ-⌞⌟ :  ⌞ injᴳ i a ⌟ᴳ  ≈ᴳ  injᴳ i ⌞ a ⌟ⁱ
    injᴳ-⌞⌟ =  updᴳ-⌞⌟ ◇˜ᴳ updᴳ-cong refl˜ⁱ $ ⌞⌟-ε Globᴱᴿᴬ

    injᴳ-↝ :  (E˙ i , a)  ↝ⁱ  (λ x → E˙ i , bˣ x) →
              (E˙ , injᴳ i a)  ↝ᴳ  λ x → E˙ , injᴳ i $ bˣ x
    injᴳ-↝ =  updᴳ-↝

    updᴱᴳ-injᴳ-↝ :  (E˙ i , a)  ↝ⁱ  (λ x → Fˣ x , bˣ x)  →
                    (E˙ , injᴳ i a)  ↝ᴳ  λ x → updᴱᴳ i (Fˣ x) E˙ , injᴳ i $ bˣ x
    updᴱᴳ-injᴳ-↝ =  updᴱᴳ-updᴳ-↝
