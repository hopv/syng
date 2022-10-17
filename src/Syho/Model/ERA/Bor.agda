--------------------------------------------------------------------------------
-- Borrow ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Bor where

open import Base.Level using (1ᴸ)
open import Base.Func using (_$_)
open import Base.Few using (⊤₀)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using (upd˙)
open import Base.Bool using (𝔹; tt; ff)
open import Base.Option using (¿_; š_; ň; ¿-case)
open import Base.Prod using (_×_; _,_; _,-)
open import Base.Nat using (ℕ; ṡ_; _<_)
open import Base.Ratp using (ℚ⁺)
open import Syho.Logic.Prop using (Lft; Prop∞)
open import Syho.Model.ERA.Base using (ERA; _×ᴱᴿᴬ_; Envmᴱᴿᴬ)
open import Syho.Model.ERA.Exc using (Excᴱᴿᴬ; εˣ; #ˣ_; ň-✓ˣ; ✓ˣ-free)
import Syho.Model.ERA.Bnd

--------------------------------------------------------------------------------
-- Borᴱᴿᴬ :  Borrow ERA

-- Borbᴱᴿᴬ :  Borrow box ERA

Borbᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
Borbᴱᴿᴬ =  Envmᴱᴿᴬ (Excᴱᴿᴬ (¿ ℚ⁺ × Lft × Prop∞) ×ᴱᴿᴬ Excᴱᴿᴬ (𝔹 × Lft × Prop∞))
  (¿ (¿ ℚ⁺ × 𝔹 × Lft × Prop∞))
  (¿-case (λ (pˇ , b , α , P) → š (pˇ , α , P) , š (b , α , P)) (ň , ň))

-- Borᴱᴿᴬ :  Borrow ERA

module BndBor =  Syho.Model.ERA.Bnd Borbᴱᴿᴬ ň
  (λ (ň✓x , ň✓y) → ň-✓ˣ ň✓x , ň-✓ˣ ň✓y)
open BndBor public using () renaming (
  --  Borᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  Bndᴱᴿᴬ to Borᴱᴿᴬ;
  inj˙ to inj˙ᴮᵒʳ; inj˙-∙ to inj˙ᴮᵒʳ-∙;
  ↝ᴮⁿᵈ-new to ↝ᴮᵒʳ-new)

open ERA Borbᴱᴿᴬ public using () renaming (Env to Envᴮᵒʳᵇ)
open ERA Borᴱᴿᴬ public using () renaming (Res to Resᴮᵒʳ; _∙_ to _∙ᴮᵒʳ_;
  ε to εᴮᵒʳ; Env to Envᴮᵒʳ; _✓_ to _✓ᴮᵒʳ_; _↝_ to _↝ᴮⁿᵈ_; ◠˜_ to ◠˜ᴮᵒʳ_;
  ↝-respʳ to ↝ᴮᵒʳ-respʳ)

-- Resource for the borrow token

bor :  ℕ →  Lft →  Prop∞ →  Resᴮᵒʳ
bor i α P =  inj˙ᴮᵒʳ i (#ˣ (ň , α , P) , εˣ)

-- Resource for the open borrow token

obor :  ℕ →  Lft →  ℚ⁺ →  Prop∞ →  Resᴮᵒʳ
obor i α p P =  inj˙ᴮᵒʳ i (#ˣ (š p , α , P) , εˣ)

-- Resource for the lender token

lend :  ℕ →  Lft →  Prop∞ →  Resᴮᵒʳ
lend i α P =  inj˙ᴮᵒʳ i (εˣ , #ˣ (tt , α , P))

-- Resource for a finished lender

flend :  ℕ →  Lft →  Prop∞ →  Resᴮᵒʳ
flend i α P =  inj˙ᴮᵒʳ i (εˣ , #ˣ (ff , α , P))

private variable
  E˙ :  ℕ → Envᴮᵒʳᵇ
  n :  ℕ
  α :  Lft
  P :  Prop∞

abstract

  -- Empty environment for Borᴱᴿᴬ

  empᴮᵒʳ :  Envᴮᵒʳ
  empᴮᵒʳ =  (λ _ → ň) , 0

  -- empᴮᵒʳ with εᴮᵒʳ is valid

  empᴮᵒʳ-✓ε :  empᴮᵒʳ ✓ᴮᵒʳ εᴮᵒʳ
  empᴮᵒʳ-✓ε =  (λ _ _ → refl) ,-

  -- Create bor and lend at a fresh new index

  bor-lend-new :  ((E˙ , n) , εᴮᵒʳ)  ↝ᴮⁿᵈ λ (_ : ⊤₀) →
    (upd˙ n (š (ň , tt , α , P)) E˙ , ṡ n) , bor n α P ∙ᴮᵒʳ lend n α P
  bor-lend-new =
    ↝ᴮᵒʳ-respʳ {a = εᴮᵒʳ} (◠˜ᴮᵒʳ inj˙ᴮᵒʳ-∙) $ ↝ᴮᵒʳ-new (refl , refl)
