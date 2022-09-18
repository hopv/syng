--------------------------------------------------------------------------------
-- Dependent-map ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Level using (Level)
open import Base.Dec using (≡Dec)
open import Syho.Model.ERA.Base using (ERA)
module Syho.Model.ERA.All {łᴵ łᴱ łᴿ ł≈ ł✓ : Level} (I : Set łᴵ) {{_ : ≡Dec I}}
  (Era˙ : I → ERA łᴱ łᴿ ł≈ ł✓) where

open import Base.Level using (_⊔ᴸ_)
open import Base.Func using (_$_)
open import Base.Eq using (_≡_; _≢_; refl; ◠_; _≡˙_)
open import Base.Prod using (∑-syntax; _,_; π₀; π₁; -,_)
open import Base.Dec using (yes; no; _≡?_; ≡?-refl; upd˙; upd˙-cong; upd˙-self;
  upd˙-2; upd˙-swap)

open ERA using (Env; Res; _≈_; _✓_; _∙_; ε; ⌞_⌟; refl˜; ◠˜_; _◇˜_; ⊑-refl;
  ∙-congˡ; ∙-unitˡ; ∙-comm; ∙-assocˡ; ✓-resp; ✓-rem; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ;
  ⌞⌟-idem; ⌞⌟-ε)

--------------------------------------------------------------------------------
-- ∀ᴱᴿᴬ :  Dependent-map ERA

∀ᴱᴿᴬ :  ERA (łᴵ ⊔ᴸ łᴱ) (łᴵ ⊔ᴸ łᴿ) (łᴵ ⊔ᴸ ł≈) (łᴵ ⊔ᴸ ł✓)
∀ᴱᴿᴬ .Env =  ∀ i →  Era˙ i .Env
∀ᴱᴿᴬ .Res =  ∀ i →  Era˙ i .Res
∀ᴱᴿᴬ ._≈_ a b =  ∀ i →  Era˙ i ._≈_ (a i) (b i)
∀ᴱᴿᴬ ._✓_ E a =  ∀ i →  Era˙ i ._✓_ (E i) (a i)
∀ᴱᴿᴬ ._∙_ a b i =  Era˙ i ._∙_ (a i) (b i)
∀ᴱᴿᴬ .ε i =  Era˙ i .ε
∀ᴱᴿᴬ .⌞_⌟ a i =  Era˙ i .⌞_⌟ (a i)
∀ᴱᴿᴬ .refl˜ i =  Era˙ i .refl˜
∀ᴱᴿᴬ .◠˜_ a≈b i =  Era˙ i .◠˜_ (a≈b i)
∀ᴱᴿᴬ ._◇˜_ a≈b b≈c i =  Era˙ i ._◇˜_ (a≈b i) (b≈c i)
∀ᴱᴿᴬ .∙-congˡ a≈b i =  Era˙ i .∙-congˡ (a≈b i)
∀ᴱᴿᴬ .∙-unitˡ i =  Era˙ i .∙-unitˡ
∀ᴱᴿᴬ .∙-comm i =  Era˙ i .∙-comm
∀ᴱᴿᴬ .∙-assocˡ i =  Era˙ i .∙-assocˡ
∀ᴱᴿᴬ .✓-resp a≈b E✓a i =  Era˙ i .✓-resp (a≈b i) (E✓a i)
∀ᴱᴿᴬ .✓-rem E✓a∙b i =  Era˙ i .✓-rem (E✓a∙b i)
∀ᴱᴿᴬ .⌞⌟-cong a≈b i =  Era˙ i .⌞⌟-cong (a≈b i)
∀ᴱᴿᴬ .⌞⌟-add =  (λ i → Era˙ i .⌞⌟-add .π₀) , λ i → Era˙ i .⌞⌟-add .π₁
∀ᴱᴿᴬ .⌞⌟-unitˡ i =  Era˙ i .⌞⌟-unitˡ
∀ᴱᴿᴬ .⌞⌟-idem i =  Era˙ i .⌞⌟-idem

open ERA ∀ᴱᴿᴬ public using () renaming (Env to Env˙; Res to Res˙)

open ERA ∀ᴱᴿᴬ using () renaming (_≈_ to _≈˙_; _⊑_ to _⊑˙_; _✓_ to _✓˙_;
  _∙_ to _∙˙_; ε to ε˙; ⌞_⌟ to ⌞_⌟˙; _↝_ to _↝˙_; refl˜ to refl˜˙;
  _◇˜_ to _◇˜˙_; ⊑≡ to ⊑˙≡)

private variable
  E˙ F˙ G˙ :  Env˙
  a˙ b˙ c˙ d˙ :  Res˙

abstract

  ✓˙-respᴱ :  E˙ ≡˙ F˙ →  E˙ ✓˙ a˙ →  F˙ ✓˙ a˙
  ✓˙-respᴱ E≡F E✓a i  rewrite ◠ E≡F i =  E✓a i

--------------------------------------------------------------------------------
-- Update & inject at an index

-- inj˙ :  Inject an element at an index

inj˙ :  ∀ i →  Era˙ i .Res →  Res˙
inj˙ i a =  upd˙ i a ε˙

module _ {i : I} where

  open ERA (Era˙ i) using () renaming (Env to Envⁱ; Res to Resⁱ;
    _≈_ to _≈ⁱ_; _⊑_ to _⊑ⁱ_; _✓_ to _✓ⁱ_; _∙_ to _∙ⁱ_; ε to εⁱ; ⌞_⌟ to ⌞_⌟ⁱ;
    _↝_ to _↝ⁱ_; refl˜ to refl˜ⁱ; ⊑≡ to ⊑ⁱ≡)

  private variable
    E F G :  Envⁱ
    a b :  Resⁱ
    ł :  Level
    X :  Set ł
    bˣ :  X → Resⁱ
    Fˣ :  X → Envⁱ

  abstract

    -- ⊑˙ distributes

    ⊑˙⇒⊑ :  a˙ ⊑˙ b˙ →  a˙ i ⊑ⁱ b˙ i
    ⊑˙⇒⊑ a⊑b rewrite ⊑˙≡ | ⊑ⁱ≡ =  let (-, c∙a≈b) = a⊑b in  -, c∙a≈b i

    ----------------------------------------------------------------------------
    -- On upd˙

    -- upd˙ preserves ≈/⊑/✓/∙/⌞⌟/↝

    upd˙-≈ :  a ≈ⁱ b →  c˙ ≈˙ d˙ →  upd˙ i a c˙ ≈˙ upd˙ i b d˙
    upd˙-≈ a≈b c˙≈d˙ j  with j ≡? i
    … | no _ =  c˙≈d˙ j
    … | yes refl =  a≈b

    upd˙-⊑' :  ∑ e , e ∙ⁱ a ≈ⁱ b →  ∑ f˙ , f˙ ∙˙ c˙ ≈˙ d˙ →
               ∑ g˙ , g˙ ∙˙ upd˙ i a c˙ ≈˙ upd˙ i b d˙
    upd˙-⊑' _ _ .π₀ =  upd˙ i _ _
    upd˙-⊑' (-, e∙a≈b) (-, f˙∙c˙≈d˙) .π₁ j  with j ≡? i
    … | no _ =  f˙∙c˙≈d˙ j
    … | yes refl =  e∙a≈b

    upd˙-⊑ :  a ⊑ⁱ b →  c˙ ⊑˙ d˙ →  upd˙ i a c˙ ⊑˙ upd˙ i b d˙
    upd˙-⊑  rewrite ⊑ⁱ≡ | ⊑˙≡ =  upd˙-⊑'

    upd˙-✓ :  E˙ i ✓ⁱ a →  E˙ ✓˙ b˙ →  E˙ ✓˙ upd˙ i a b˙
    upd˙-✓ Ei✓a E✓b˙ j  with j ≡? i
    … | no _ =  E✓b˙ j
    … | yes refl =  Ei✓a

    upd˙-∙ :  upd˙ i a c˙ ∙˙ upd˙ i b d˙  ≈˙  upd˙ i (a ∙ⁱ b) (c˙ ∙˙ d˙)
    upd˙-∙ j  with j ≡? i
    … | no _ =  Era˙ j .refl˜
    … | yes refl =  refl˜ⁱ

    upd˙-⌞⌟ :  ⌞ upd˙ i a b˙ ⌟˙  ≈˙  upd˙ i ⌞ a ⌟ⁱ ⌞ b˙ ⌟˙
    upd˙-⌞⌟ j  with j ≡? i
    … | no _ =  Era˙ j .refl˜
    … | yes refl =  refl˜ⁱ

    upd˙-↝ :  (E˙ i , a)  ↝ⁱ  (λ x → E˙ i , bˣ x)  →
              (E˙ , upd˙ i a c˙)  ↝˙  λ x → (E˙ , upd˙ i (bˣ x) c˙)
    upd˙-↝ {E˙} {bˣ = bˣ} {c˙} Eia↝Eib d˙ E✓iac∙d  with E✓iac∙d i
    … | Ei✓a∙di  rewrite ≡?-refl {a = i}  =  body
     where
      body :  ∑ x , E˙ ✓˙ upd˙ i (bˣ x) c˙ ∙˙ d˙
      body .π₀ =  Eia↝Eib _ Ei✓a∙di .π₀
      body .π₁ j  with j ≡? i | E✓iac∙d j
      … | no _ | E✓cj∙dj =  E✓cj∙dj
      … | yes refl | _ =  Eia↝Eib _ Ei✓a∙di .π₁

    upd˙-upd˙-↝ :  (E˙ i , a)  ↝ⁱ  (λ x → Fˣ x , bˣ x)  →
      (E˙ , upd˙ i a c˙)  ↝˙  λ x → upd˙ i (Fˣ x) E˙ , upd˙ i (bˣ x) c˙
    upd˙-upd˙-↝ {E˙} {Fˣ = Fˣ} {bˣ} {c˙} Eia↝Fb d˙ E✓iac∙d  with E✓iac∙d i
    … | Ei✓a∙di  rewrite ≡?-refl {a = i}  =  body
     where
      body :  ∑ x , upd˙ i (Fˣ x) E˙ ✓˙ upd˙ i (bˣ x) c˙ ∙˙ d˙
      body .π₀ =  Eia↝Fb _ Ei✓a∙di .π₀
      body .π₁ j  with j ≡? i | E✓iac∙d j
      … | no _ | E✓cj∙dj =  E✓cj∙dj
      … | yes refl | _ =  Eia↝Fb _ Ei✓a∙di .π₁

    ----------------------------------------------------------------------------
    -- On inj˙

    -- inj˙ preserves ≈/⊑/∙/ε/⌞⌟/↝

    inj˙-≈ :  a ≈ⁱ b →  inj˙ i a  ≈˙  inj˙ i b
    inj˙-≈ a≈b =  upd˙-≈ a≈b refl˜˙

    inj˙-⊑ :  a ⊑ⁱ b →  inj˙ i a  ⊑˙  inj˙ i b
    inj˙-⊑ a⊑b =  upd˙-⊑ a⊑b $ ⊑-refl ∀ᴱᴿᴬ

    inj˙-∙ :  inj˙ i a ∙˙ inj˙ i b  ≈˙  inj˙ i (a ∙ⁱ b)
    inj˙-∙ =  upd˙-∙ ◇˜˙ upd˙-≈ refl˜ⁱ $ ∀ᴱᴿᴬ .∙-unitˡ

    inj˙-ε :  inj˙ i εⁱ ≈˙ ε˙
    inj˙-ε j  with j ≡? i
    … | no _ =  Era˙ j .refl˜
    … | yes refl =  refl˜ⁱ

    inj˙-⌞⌟ :  ⌞ inj˙ i a ⌟˙  ≈˙  inj˙ i ⌞ a ⌟ⁱ
    inj˙-⌞⌟ =  upd˙-⌞⌟ ◇˜˙ upd˙-≈ refl˜ⁱ $ ⌞⌟-ε ∀ᴱᴿᴬ

    inj˙-↝ :  (E˙ i , a)  ↝ⁱ  (λ x → E˙ i , bˣ x) →
              (E˙ , inj˙ i a)  ↝˙  λ x → E˙ , inj˙ i $ bˣ x
    inj˙-↝ =  upd˙-↝

    upd˙-inj˙-↝ :  (E˙ i , a)  ↝ⁱ  (λ x → Fˣ x , bˣ x)  →
                    (E˙ , inj˙ i a)  ↝˙  λ x → upd˙ i (Fˣ x) E˙ , inj˙ i $ bˣ x
    upd˙-inj˙-↝ =  upd˙-upd˙-↝

    -- Get ✓ⁱ from ✓˙ inj˙

    ✓-inj˙ :  E˙ ✓˙ inj˙ i a →  E˙ i ✓ⁱ a
    ✓-inj˙ E✓ia  with E✓ia i
    … | E✓a  rewrite ≡?-refl {a = i} =  E✓a
