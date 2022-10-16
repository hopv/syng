--------------------------------------------------------------------------------
-- Finite-map ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Level using (Level)
open import Base.Nat using (ℕ)
open import Syho.Model.ERA.Base using (ERA)
module Syho.Model.ERA.Fin {łᴿ ł≈ łᴱ ł✓ : Level} (Era : ERA łᴿ ł≈ łᴱ ł✓)
  (≈ε-rem :  ∀{a b} →  Era .ERA._≈_ (Era .ERA._∙_ a b) (Era .ERA.ε) →
                       Era .ERA._≈_ b (Era .ERA.ε)) where

open import Base.Level using (_⊔ᴸ_)
open import Base.Func using (_$_; flip)
open import Base.Few using (⊤₀; absurd; ¬_)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using (yes; no; _≟_; ≟-refl; upd˙)
open import Base.Prod using (∑-syntax; π₀; π₁; _,_; -,_; _,-)
open import Base.Nat using (ṡ_; Cofin; ≤-refl; <-irrefl; <⇒≤)
open import Syho.Model.ERA.Base using (Valmᴱᴿᴬ)
import Syho.Model.ERA.All

open ERA Era using (Res; _≈_; ε; Env; _✓_; _↝_; refl˜; ◠˜_; _◇˜_; ∙-congʳ;
  ∙-unitˡ; ∙-unitʳ; ∙-comm; ✓-resp)

--------------------------------------------------------------------------------
-- Finᴱᴿᴬ :  Finite-map ERA

module AllFin =  Syho.Model.ERA.All ℕ (λ _ → Era)
-- Re-export all
open AllFin public

private variable
  i :  ℕ
  a b :  Res
  ł :  Level
  X :  Set ł
  bˣ :  X → Res
  E :  Env
  a˙ b˙ :  Res˙
  E˙ F˙ : Env˙

-- Cofinε a˙ :  a˙ i ≈ ε holds for all but finitely many i's

Cofinε :  Res˙ →  Set ł≈
Cofinε =  Cofin (λ _ → _≈ ε)

abstract

  -- Cofinε respects ≈˙

  Cofinε-resp :  a˙ ≈˙ b˙ →  Cofinε a˙ →  Cofinε b˙
  Cofinε-resp _ (n ,-) .π₀ =  n
  Cofinε-resp a≈b (-, i≥n⇒ai≈ε) .π₁ i i≥n =  ◠˜ a≈b i ◇˜ i≥n⇒ai≈ε i i≥n

  -- Cofinε is preserved by removal w.r.t. ∙˙

  Cofinε-rem :  Cofinε (a˙ ∙˙ b˙) →  Cofinε b˙
  Cofinε-rem (i ,-) .π₀ =  i
  Cofinε-rem (-, i≥n⇒ai∙bi≈ε) .π₁ i i≥n =  ≈ε-rem $ i≥n⇒ai∙bi≈ε i i≥n

-- Finᴱᴿᴬ :  Finite-map ERA

Finᴱᴿᴬ :  ERA łᴿ ł≈ łᴱ (ł≈ ⊔ᴸ ł✓)
Finᴱᴿᴬ =  Valmᴱᴿᴬ ∀ᴱᴿᴬ (λ _ → Cofinε) Cofinε-resp Cofinε-rem

open ERA Finᴱᴿᴬ using () renaming (_✓_ to _✓ᶠⁱⁿ_; _↝_ to _↝ᶠⁱⁿ_)

abstract

  -- Allocate a valid resource and environment to a fresh index

  ↝ᶠⁱⁿ-new :  E ✓ a  →   (F˙ , ε˙)  ↝ᶠⁱⁿ λ i →  upd˙ i E F˙ , inj˙ i a
  ↝ᶠⁱⁿ-new _ _ ((n ,-) ,-) .π₀ =  n
  ↝ᶠⁱⁿ-new _ _ ((n ,-) ,-) .π₁ .π₀ .π₀ =  ṡ n
  ↝ᶠⁱⁿ-new _ b˙ ((n , i≥n⇒bi≈ε) ,-) .π₁ .π₀ .π₁ i i>n  with i ≟ n
  … | no _ =  i≥n⇒bi≈ε i (<⇒≤ i>n)
  … | yes refl =  absurd $ <-irrefl i>n
  ↝ᶠⁱⁿ-new E✓a b˙ ((n , i≥n⇒bi≈ε) , F✓b) .π₁ .π₁ i  with i ≟ n
  … | no _ =  F✓b i
  … | yes refl =  flip ✓-resp E✓a $ ◠˜_ $
    ∙-congʳ (◠˜ ∙-unitˡ ◇˜ i≥n⇒bi≈ε n ≤-refl) ◇˜ ∙-unitʳ

  -- Lift a resource update

  inj˙-↝ᶠⁱⁿ :  ¬ a ≈ ε  →   ((E˙ i , a)  ↝ λ x →  E˙ i , bˣ x)  →
               (E˙ , inj˙ i a)  ↝ᶠⁱⁿ λ x →  E˙ , inj˙ i (bˣ x)
  inj˙-↝ᶠⁱⁿ {E˙ = E˙} {i} {bˣ = bˣ}
    ¬a≈ε Eia↝Eibx c˙ ((n , j≥n⇒ia∙cj≈ε) , ✓ia∙c)  with ✓ia∙c i
  … | ✓a∙ci  rewrite ≟-refl {a = i}  =  body
   where
    body :  ∑ x , E˙ ✓ᶠⁱⁿ inj˙ i (bˣ x) ∙˙ c˙
    body .π₀ =  Eia↝Eibx (c˙ i) ✓a∙ci .π₀
    body .π₁ .π₀ .π₀ =  n
    body .π₁ .π₀ .π₁ j j≥n  with j≥n⇒ia∙cj≈ε j j≥n
    … | ia∙cj≈ε  with j ≟ i
    …   | no _ =  ia∙cj≈ε
    …   | yes refl =  absurd $ ¬a≈ε $ ≈ε-rem $ ∙-comm ◇˜ ia∙cj≈ε
    body .π₁ .π₁ j  with ✓ia∙c j
    … | ✓ia∙cj  with j ≟ i
    …   | no _ =  ✓ia∙cj
    …   | yes refl =  Eia↝Eibx (c˙ i) ✓a∙ci .π₁
