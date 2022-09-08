--------------------------------------------------------------------------------
-- Global ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Glob where

open import Base.Level using (Level; 2ᴸ)
open import Base.Func using (_$_)
open import Base.Eq using (_≡_; _≢_; refl; ◠_; _≡˙_)
open import Base.Prod using (∑-syntax; _,_; π₀; π₁; -,_)
open import Base.Dec using (yes; no; _≡?_; ≡?-refl; upd˙; upd˙-cong;
  upd˙-self; upd˙-2; upd˙-swap)
open import Base.Nat using (ℕ; ṡ_)
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
  (λ i → Globᴱᴿᴬ˙ i .⌞⌟-add .π₀) , λ i → Globᴱᴿᴬ˙ i .⌞⌟-add .π₁
Globᴱᴿᴬ .⌞⌟-unitˡ i =  Globᴱᴿᴬ˙ i .⌞⌟-unitˡ
Globᴱᴿᴬ .⌞⌟-idem i =  Globᴱᴿᴬ˙ i .⌞⌟-idem

open ERA Globᴱᴿᴬ public using () renaming (Env to Envᴳ)

open ERA Globᴱᴿᴬ using () renaming (Res to Resᴳ; _≈_ to _≈ᴳ_; _⊑_ to _⊑ᴳ_;
  _✓_ to _✓ᴳ_; _∙_ to _∙ᴳ_; ε to εᴳ; ⌞_⌟ to ⌞_⌟ᴳ; _↝_ to _↝ᴳ_; refl˜ to refl˜ᴳ;
  _◇˜_ to _◇˜ᴳ_)

private variable
  E˙ F˙ G˙ :  Envᴳ
  a˙ b˙ c˙ d˙ :  Resᴳ

abstract

  ✓ᴳ-respᴱ :  E˙ ≡˙ F˙ →  E˙ ✓ᴳ a˙ →  F˙ ✓ᴳ a˙
  ✓ᴳ-respᴱ E≡F E✓a i  rewrite ◠ E≡F i =  E✓a i

--------------------------------------------------------------------------------
-- Update & inject at an index

-- injᴳ :  Inject an element at an index

injᴳ :  ∀ i →  Globᴱᴿᴬ˙ i .Res →  Resᴳ
injᴳ i a =  upd˙ i a εᴳ

module _ {i : ℕ} where

  open ERA (Globᴱᴿᴬ˙ i) using () renaming (Env to Envⁱ; Res to Resⁱ;
    _≈_ to _≈ⁱ_; _⊑_ to _⊑ⁱ_; _✓_ to _✓ⁱ_; _∙_ to _∙ⁱ_; ε to εⁱ; ⌞_⌟ to ⌞_⌟ⁱ;
    _↝_ to _↝ⁱ_; refl˜ to refl˜ⁱ)

  private variable
    E F G :  Envⁱ
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
    -- On upd˙

    -- upd˙ preserves ≈/⊑/✓/∙/⌞⌟/↝

    upd˙-congᴳ :  a ≈ⁱ b →  c˙ ≈ᴳ d˙ →  upd˙ i a c˙ ≈ᴳ upd˙ i b d˙
    upd˙-congᴳ a≈b c˙≈d˙ j  with j ≡? i
    … | no _ =  c˙≈d˙ j
    … | yes refl =  a≈b

    upd˙-mono :  a ⊑ⁱ b →  c˙ ⊑ᴳ d˙ →  upd˙ i a c˙ ⊑ᴳ upd˙ i b d˙
    upd˙-mono _ _ .π₀ =  upd˙ i _ _
    upd˙-mono (-, e∙a≈b) (-, f˙∙c˙≈d˙) .π₁ j  with j ≡? i
    … | no _ =  f˙∙c˙≈d˙ j
    … | yes refl =  e∙a≈b

    upd˙-✓ :  E˙ i ✓ⁱ a →  E˙ ✓ᴳ b˙ →  E˙ ✓ᴳ upd˙ i a b˙
    upd˙-✓ Ei✓a E✓b˙ j  with j ≡? i
    … | no _ =  E✓b˙ j
    … | yes refl =  Ei✓a

    upd˙-∙ :  upd˙ i a c˙ ∙ᴳ upd˙ i b d˙  ≈ᴳ  upd˙ i (a ∙ⁱ b) (c˙ ∙ᴳ d˙)
    upd˙-∙ j  with j ≡? i
    … | no _ =  Globᴱᴿᴬ˙ j .refl˜
    … | yes refl =  refl˜ⁱ

    upd˙-⌞⌟ :  ⌞ upd˙ i a b˙ ⌟ᴳ  ≈ᴳ  upd˙ i ⌞ a ⌟ⁱ ⌞ b˙ ⌟ᴳ
    upd˙-⌞⌟ j  with j ≡? i
    … | no _ =  Globᴱᴿᴬ˙ j .refl˜
    … | yes refl =  refl˜ⁱ

    upd˙-↝ :  (E˙ i , a)  ↝ⁱ  (λ x → E˙ i , bˣ x)  →
              (E˙ , upd˙ i a c˙)  ↝ᴳ  λ x → (E˙ , upd˙ i (bˣ x) c˙)
    upd˙-↝ {E˙} {bˣ = bˣ} {c˙} Eia↝Eib d˙ E✓d∙iac  with E✓d∙iac i
    … | Ei✓di∙a  rewrite ≡?-refl {a = i}  =  body
     where
      body :  ∑ x , E˙ ✓ᴳ d˙ ∙ᴳ upd˙ i (bˣ x) c˙
      body .π₀ =  Eia↝Eib _ Ei✓di∙a .π₀
      body .π₁ j  with j ≡? i | E✓d∙iac j
      … | no _ | E✓dj∙cj =  E✓dj∙cj
      … | yes refl | _ =  Eia↝Eib _ Ei✓di∙a .π₁

    upd˙-upd˙-↝ :  (E˙ i , a)  ↝ⁱ  (λ x → Fˣ x , bˣ x)  →
      (E˙ , upd˙ i a c˙)  ↝ᴳ  λ x → upd˙ i (Fˣ x) E˙ , upd˙ i (bˣ x) c˙
    upd˙-upd˙-↝ {E˙} {Fˣ = Fˣ} {bˣ} {c˙} Eia↝Fb d˙ E✓d∙iac  with E✓d∙iac i
    … | Ei✓di∙a  rewrite ≡?-refl {a = i}  =  body
     where
      body :  ∑ x , upd˙ i (Fˣ x) E˙ ✓ᴳ d˙ ∙ᴳ upd˙ i (bˣ x) c˙
      body .π₀ =  Eia↝Fb _ Ei✓di∙a .π₀
      body .π₁ j  with j ≡? i | E✓d∙iac j
      … | no _ | E✓dj∙cj =  E✓dj∙cj
      … | yes refl | _ =  Eia↝Fb _ Ei✓di∙a .π₁

    ----------------------------------------------------------------------------
    -- On injᴳ

    -- injᴳ preserves ≈/✓/∙/ε/⌞⌟/↝

    injᴳ-cong :  a ≈ⁱ b →  injᴳ i a  ≈ᴳ  injᴳ i b
    injᴳ-cong a≈b =  upd˙-congᴳ a≈b refl˜ᴳ

    injᴳ-mono :  a ⊑ⁱ b →  injᴳ i a  ⊑ᴳ  injᴳ i b
    injᴳ-mono a⊑b =  upd˙-mono a⊑b $ ⊑-refl Globᴱᴿᴬ

    injᴳ-✓ :  E˙ i ✓ⁱ a →  E˙ ✓ᴳ injᴳ i a
    injᴳ-✓ Ei✓a =  upd˙-✓ Ei✓a $ Globᴱᴿᴬ .✓-ε

    injᴳ-∙ :  injᴳ i a ∙ᴳ injᴳ i b  ≈ᴳ  injᴳ i (a ∙ⁱ b)
    injᴳ-∙ =  upd˙-∙ ◇˜ᴳ upd˙-congᴳ refl˜ⁱ $ Globᴱᴿᴬ .∙-unitˡ

    injᴳ-ε :  injᴳ i εⁱ ≈ᴳ εᴳ
    injᴳ-ε j  with j ≡? i
    … | no _ =  Globᴱᴿᴬ˙ j .refl˜
    … | yes refl =  refl˜ⁱ

    injᴳ-⌞⌟ :  ⌞ injᴳ i a ⌟ᴳ  ≈ᴳ  injᴳ i ⌞ a ⌟ⁱ
    injᴳ-⌞⌟ =  upd˙-⌞⌟ ◇˜ᴳ upd˙-congᴳ refl˜ⁱ $ ⌞⌟-ε Globᴱᴿᴬ

    injᴳ-↝ :  (E˙ i , a)  ↝ⁱ  (λ x → E˙ i , bˣ x) →
              (E˙ , injᴳ i a)  ↝ᴳ  λ x → E˙ , injᴳ i $ bˣ x
    injᴳ-↝ =  upd˙-↝

    upd˙-injᴳ-↝ :  (E˙ i , a)  ↝ⁱ  (λ x → Fˣ x , bˣ x)  →
                    (E˙ , injᴳ i a)  ↝ᴳ  λ x → upd˙ i (Fˣ x) E˙ , injᴳ i $ bˣ x
    upd˙-injᴳ-↝ =  upd˙-upd˙-↝
