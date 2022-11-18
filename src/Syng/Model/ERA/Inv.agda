--------------------------------------------------------------------------------
-- Invariant ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syng.Model.ERA.Inv where

open import Base.Func using (_$_; _›_)
open import Base.Few using (⊤₀; ¬_; absurd)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using (≟-refl; upd˙)
open import Base.Option using (¿_; š_; ň)
open import Base.Prod using (_×_; π₀; π₁; _,_; -,_; _,-)
open import Base.Nat using (ℕ; ṡ_; _<_)
open import Base.List using ([]; [_]; ≡⇒≈ᴸ; ≈ᴸ-[])
open import Syng.Logic.Prop using (Name; SProp∞)
open import Syng.Model.ERA.Base using (ERA; _×ᴱᴿᴬ_; Envmᴱᴿᴬ)
open import Syng.Model.ERA.Exc using (εˣ; #ˣ_; Excᴱᴿᴬ; ň-✓ˣ)
open import Syng.Model.ERA.Ag using (Agᴱᴿᴬ; ň-✓ᴸ; ✓ᴸ-[]; ✓ᴸ-š-[?]; ✓ᴸ-agree)
import Syng.Model.ERA.All
import Syng.Model.ERA.Bnd

--------------------------------------------------------------------------------
-- Invᴱᴿᴬ :  Invariant ERA

-- NameSProp :  Pair of a name and a proposition

NameSProp :  Set₁
NameSProp =  Name × SProp∞

private variable
  P :  SProp∞
  nm :  Name
  i n :  ℕ
  ⁿPˇ˙ ⁿQˇ˙ :  ℕ →  ¿ NameSProp

-- Invᴱᴿᴬ :  Invariant ERA

module BndInv =  Syng.Model.ERA.Bnd
  (Envmᴱᴿᴬ (Agᴱᴿᴬ NameSProp ×ᴱᴿᴬ Excᴱᴿᴬ NameSProp) _ λ ⁿPˇ → ⁿPˇ , ⁿPˇ)
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

∅ᴵⁿᵛ :  Envᴵⁿᵛ
∅ᴵⁿᵛ =  (λ _ → ň) , 0

-- Persistently observe a proposition at an index

inv :  ℕ →  Name →  SProp∞ →  Resᴵⁿᵛ
inv i nm P =  inj˙ᴵⁿᵛ i ([ nm , P ] , εˣ)

-- Exclusively own a key of an index

kinv :  ℕ →  Name →  SProp∞ →  Resᴵⁿᵛ
kinv i nm P =  inj˙ᴵⁿᵛ i ([] , #ˣ (nm , P))

abstract

  -- ∅ᴵⁿᵛ with εᴵⁿᵛ is valid

  ∅ᴵⁿᵛ-✓ε :  ∅ᴵⁿᵛ ✓ᴵⁿᵛ εᴵⁿᵛ
  ∅ᴵⁿᵛ-✓ε =  (λ _ _ → refl) , (λ _ → ✓ᴸ-[] , _)

  -- inv i nm P absorbs ⌞ ⌟

  inv-⌞⌟ :  ⌞ inv i nm P ⌟ᴵⁿᵛ ≈ᴵⁿᵛ inv i nm P
  inv-⌞⌟ =  inj˙ᴵⁿᵛ-⌞⌟

  -- kinv i nm P cannot overlap

  kinv-no2 :  ¬ (ⁿQˇ˙ , n) ✓ᴵⁿᵛ kinv i nm P ∙ᴵⁿᵛ kinv i nm P
  kinv-no2 {i = i} (-, ✓inmP2)  with ✓inmP2 i
  … | -, ✓↯  rewrite ≟-refl {a = i} =  absurd ✓↯

  -- Get inv and kinv

  inv-kinv-new :  ((ⁿQˇ˙ , n) , εᴵⁿᵛ)  ↝ᴵⁿᵛ λ (_ : ⊤₀) →
    (upd˙ n (š (nm , P)) ⁿQˇ˙ , ṡ n) , inv n nm P ∙ᴵⁿᵛ kinv n nm P
  inv-kinv-new =
    ↝ᴵⁿᵛ-respʳ {a = εᴵⁿᵛ} (◠˜ᴵⁿᵛ inj˙ᴵⁿᵛ-∙) $ ↝ᴵⁿᵛ-new (✓ᴸ-š-[?] , refl)

  -- Get agreement from inv

  inv-agree :  ((ⁿQˇ˙ , n) , inv i nm P)  ↝ᴵⁿᵛ
    λ (_ :  i < n  ×  ⁿQˇ˙ i ≡ š (nm , P)) →  (ⁿQˇ˙ , n) , inv i nm P
  inv-agree =  ↝ᴵⁿᵛ-agree (π₀ › ≈ᴸ-[] › λ ()) (π₀ › ✓ᴸ-agree)

  -- Get agreement from kinv

  kinv-agree :  ((ⁿQˇ˙ , n) , kinv i nm P)  ↝ᴵⁿᵛ
    λ (_ :  i < n  ×  ⁿQˇ˙ i ≡ š (nm , P)) →  (ⁿQˇ˙ , n) , kinv i nm P
  kinv-agree =  ↝ᴵⁿᵛ-agree (λ ()) π₁
