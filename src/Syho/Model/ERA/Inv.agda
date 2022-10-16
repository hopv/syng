--------------------------------------------------------------------------------
-- Invariant ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Inv where

open import Base.Func using (_$_; _›_)
open import Base.Few using (⊤₀; ¬_; absurd)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using (≟-refl; upd˙)
open import Base.Option using (¿_; š_; ň)
open import Base.Prod using (_×_; π₀; π₁; _,_; -,_; _,-)
open import Base.Nat using (ℕ; ṡ_; _<_)
open import Base.List using ([]; [_]; ≡⇒≈ᴸ; ≈ᴸ-[])
open import Syho.Logic.Prop using (Name; Prop∞)
open import Syho.Model.ERA.Base using (ERA; _×ᴱᴿᴬ_; Envmᴱᴿᴬ)
open import Syho.Model.ERA.Exc using (εˣ; #ˣ_; Excᴱᴿᴬ; ň-✓ˣ)
open import Syho.Model.ERA.Ag using (Agᴱᴿᴬ; ň-✓ᴸ; ✓ᴸ-[]; ✓ᴸ-š-[?]; ✓ᴸ-agree)
import Syho.Model.ERA.All
import Syho.Model.ERA.Bnd

--------------------------------------------------------------------------------
-- Invᴱᴿᴬ :  Invariant ERA

NameProp :  Set₁
NameProp =  Name × Prop∞

private variable
  P :  Prop∞
  nm :  Name
  i n :  ℕ
  ⁿPˇ˙ ⁿQˇ˙ :  ℕ →  ¿ NameProp

module BndInv =  Syho.Model.ERA.Bnd
  (Envmᴱᴿᴬ (Agᴱᴿᴬ NameProp ×ᴱᴿᴬ Excᴱᴿᴬ NameProp) _ λ ⁿPˇ → ⁿPˇ , ⁿPˇ)
  ň (λ (ň✓as , ň✓x) → ≡⇒≈ᴸ (ň-✓ᴸ ň✓as) , ň-✓ˣ ň✓x)
open BndInv public using () renaming (
  --  Invᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  Bndᴱᴿᴬ to Invᴱᴿᴬ;
  inj˙ to inj˙ᴵⁿᵛ; inj˙-∙ to inj˙ᴵⁿᵛ-∙; inj˙-⌞⌟ to inj˙ᴵⁿᵛ-⌞⌟;
  ↝ᴮⁿᵈ-new to ↝ᴵⁿᵛ-new; ↝ᴮⁿᵈ-agree to ↝ᴵⁿᵛ-agree)

open ERA Invᴱᴿᴬ public using () renaming (Env to Envᴵⁿᵛ; Res to Resᴵⁿᵛ;
  _≈_ to _≈ᴵⁿᵛ_; _∙_ to _∙ᴵⁿᵛ_; ε to εᴵⁿᵛ; ⌞_⌟ to ⌞_⌟ᴵⁿᵛ; _✓_ to _✓ᴵⁿᵛ_;
  _↝_ to _↝ᴵⁿᵛ_; ◠˜_ to ◠˜ᴵⁿᵛ_; ↝-respʳ to ↝ᴵⁿᵛ-respʳ)

-- Empty environment of Invᴱᴿᴬ

empᴵⁿᵛ :  Envᴵⁿᵛ
empᴵⁿᵛ =  (λ _ → ň) , 0

-- Persistently observe a proposition at an index

inv :  ℕ →  Name →  Prop∞ →  Resᴵⁿᵛ
inv i nm P =  inj˙ᴵⁿᵛ i ([ nm , P ] , εˣ)

-- Exclusively own a key of an index

invk :  ℕ →  Name →  Prop∞ →  Resᴵⁿᵛ
invk i nm P =  inj˙ᴵⁿᵛ i ([] , #ˣ (nm , P))

abstract

  -- empᴵⁿᵛ with εᴵⁿᵛ is valid

  empᴵⁿᵛ-✓ε :  empᴵⁿᵛ ✓ᴵⁿᵛ εᴵⁿᵛ
  empᴵⁿᵛ-✓ε =  (λ _ _ → refl) , (λ _ → ✓ᴸ-[] , _)

  -- inv i nm P absorbs ⌞ ⌟

  inv-⌞⌟ :  ⌞ inv i nm P ⌟ᴵⁿᵛ ≈ᴵⁿᵛ inv i nm P
  inv-⌞⌟ =  inj˙ᴵⁿᵛ-⌞⌟

  -- invk i nm P cannot overlap

  invk-no2 :  ¬ (ⁿQˇ˙ , n) ✓ᴵⁿᵛ invk i nm P ∙ᴵⁿᵛ invk i nm P
  invk-no2 {i = i} (-, ✓inmP2)  with ✓inmP2 i
  … | -, ✓↯  rewrite ≟-refl {a = i} =  absurd ✓↯

  -- Get inv and invk

  inv-invk-new :  ((ⁿQˇ˙ , n) , εᴵⁿᵛ)  ↝ᴵⁿᵛ λ (_ : ⊤₀) →
    (upd˙ n (š (nm , P)) ⁿQˇ˙ , ṡ n) , inv n nm P ∙ᴵⁿᵛ invk n nm P
  inv-invk-new =
    ↝ᴵⁿᵛ-respʳ {a = εᴵⁿᵛ} (◠˜ᴵⁿᵛ inj˙ᴵⁿᵛ-∙) $ ↝ᴵⁿᵛ-new (✓ᴸ-š-[?] , refl)

  -- Get agreement from inv

  inv-agree :  ((ⁿQˇ˙ , n) , inv i nm P)  ↝ᴵⁿᵛ
    λ (_ :  ⁿQˇ˙ i ≡ š (nm , P)  ×  i < n) →  (ⁿQˇ˙ , n) , inv i nm P
  inv-agree =  ↝ᴵⁿᵛ-agree (π₀ › ≈ᴸ-[] › λ ()) (π₀ › ✓ᴸ-agree)

  -- Get agreement from invk

  invk-agree :  ((ⁿQˇ˙ , n) , invk i nm P)  ↝ᴵⁿᵛ
    λ (_ :  ⁿQˇ˙ i ≡ š (nm , P)  ×  i < n) →  (ⁿQˇ˙ , n) , invk i nm P
  invk-agree =  ↝ᴵⁿᵛ-agree (λ ()) π₁
