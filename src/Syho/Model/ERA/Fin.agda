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
open import Base.Few using (absurd)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using (yes; no; _≟_; upd˙)
open import Base.Prod using (π₀; π₁; _,_; -,_; _,-)
open import Base.Nat using (ṡ_; Cofin; ≤-refl; <-irrefl; <⇒≤)
open import Syho.Model.ERA.Base using (Valmᴱᴿᴬ)
import Syho.Model.ERA.All

open ERA Era using (Res; _≈_; ε; Env; _✓_; refl˜; ◠˜_; _◇˜_; ∙-congʳ; ∙-unitˡ;
  ∙-unitʳ; ✓-resp)

--------------------------------------------------------------------------------
-- Finᴱᴿᴬ :  Finite-map ERA

module AllFin =  Syho.Model.ERA.All ℕ (λ _ → Era)
-- Re-export all
open AllFin public

private variable
  a :  Res
  E :  Env
  a˙ b˙ :  Res˙
  F˙ : Env˙

-- Cofinε a˙ :  a˙ i ≡ εᴸᵇ holds for all but finitely many i's

Cofinε :  Res˙ →  Set ł≈
Cofinε =  Cofin (λ _ → _≈ ε)

abstract

  -- Cofinε respects ≈˙

  Cofinε-resp :  a˙ ≈˙ b˙ →  Cofinε a˙ →  Cofinε b˙
  Cofinε-resp _ (n ,-) .π₀ =  n
  Cofinε-resp a≈b (-, i≥n⇒ai≈ε) .π₁ i i≥n =  ◠˜ a≈b i ◇˜ i≥n⇒ai≈ε i i≥n

  -- Cofinε is preserved by removal w.r.t. ∙˙

  Cofinε-rem :  Cofinε (a˙ ∙˙ b˙) →  Cofinε b˙
  Cofinε-rem {a˙} {b˙} (i ,-) .π₀ =  i
  Cofinε-rem {a˙} {b˙} (-, i≥n⇒ai∙bi≈ε) .π₁ i i≥n =  ≈ε-rem $ i≥n⇒ai∙bi≈ε i i≥n

-- Finᴱᴿᴬ :  Finite-map ERA

Finᴱᴿᴬ :  ERA łᴿ ł≈ łᴱ (ł≈ ⊔ᴸ ł✓)
Finᴱᴿᴬ =  Valmᴱᴿᴬ ∀ᴱᴿᴬ (λ _ → Cofinε) Cofinε-resp Cofinε-rem

open ERA Finᴱᴿᴬ using () renaming (_↝_ to _↝ᶠⁱⁿ_)

abstract

  -- Allocate a valid resource and environment to a fresh index

  ✓-new :  E ✓ a  →   (F˙ , ε˙)  ↝ᶠⁱⁿ λ i →  upd˙ i E F˙ , inj˙ i a
  ✓-new _ _ ((n ,-) ,-) .π₀ =  n
  ✓-new _ _ ((n ,-) ,-) .π₁ .π₀ .π₀ =  ṡ n
  ✓-new _ b˙ ((n , i≥n⇒bi≈ε) ,-) .π₁ .π₀ .π₁ i i>n  with i ≟ n
  … | no _ =  i≥n⇒bi≈ε i (<⇒≤ i>n)
  … | yes refl =  absurd $ <-irrefl i>n
  ✓-new E✓a b˙ ((n , i≥n⇒bi≈ε) , F✓b) .π₁ .π₁ i  with i ≟ n
  … | no _ =  F✓b i
  … | yes refl =  flip ✓-resp E✓a $ ◠˜_ $
    ∙-congʳ (◠˜ ∙-unitˡ ◇˜ i≥n⇒bi≈ε n ≤-refl) ◇˜ ∙-unitʳ
