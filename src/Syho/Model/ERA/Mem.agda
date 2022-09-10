--------------------------------------------------------------------------------
-- Memory ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Mem where

open import Base.Level using (2ᴸ; ↑_; ↓)
open import Base.Func using (_$_; _▷_; _∘_)
open import Base.Eq using (_≡_)
open import Base.Nat using (ℕ)
open import Base.Prod using (π₀; π₁; _,_; -,_)
open import Base.Option using (š_; ň; _$¿_)
open import Base.Dec using (upd˙)
open import Base.List using ([_]; len)
open import Base.RatPos using (ℚ⁺; _+ᴿ⁺_; _≤1ᴿ⁺)
open import Syho.Lang.Expr using (Addr; TyVal)
open import Syho.Lang.Reduce using (Mem; _‼ᴹ_; ✓ᴹ_)
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Exc using (Excᴱᴿᴬ; #ˣ_)
open import Syho.Model.ERA.Frac using (Fracᴱᴿᴬ; š[?]-∙ᶠʳ; ✓ᶠʳ-≤1; ✓ᶠʳ-agree2)
import Syho.Model.ERA.All
import Syho.Model.ERA.Prod
import Syho.Model.ERA.Wrap
import Syho.Model.ERA.Up

--------------------------------------------------------------------------------
-- Memᴱᴿᴬ :  Memory ERA

-- For the points-to token

module AllPnts =  Syho.Model.ERA.All Addr (λ _ → Fracᴱᴿᴬ TyVal)
open AllPnts public using () renaming (
  --  Pntsᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  ∀ᴱᴿᴬ to Pntsᴱᴿᴬ;
  --  inj˙ᴾⁿᵗˢ :  ∀ θ →  Fracᴱᴿᴬ TyVal →  Pntsᴱᴿᴬ .Res
  inj˙ to inj˙ᴾⁿᵗˢ;
  inj˙-∙ to inj˙ᴾⁿᵗˢ-∙; inj˙-≈ to inj˙ᴾⁿᵗˢ-≈; ✓-inj˙ to ✓-inj˙ᴾⁿᵗˢ)

-- For the freeing token

module AllFree =  Syho.Model.ERA.All ℕ (λ _ → Excᴱᴿᴬ ℕ)
open AllFree public using () renaming (
  --  Freeᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
  ∀ᴱᴿᴬ to Freeᴱᴿᴬ;
  inj˙ to inj˙ᶠʳᵉᵉ)

-- For both tokens

module ProdMem =  Syho.Model.ERA.Prod Pntsᴱᴿᴬ Freeᴱᴿᴬ
open ProdMem public using () renaming (
  --  ×Memᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  ×ᴱᴿᴬ to ×Memᴱᴿᴬ)
module WrapMem =  Syho.Model.ERA.Wrap ×Memᴱᴿᴬ
  Mem (λ M → M ‼ᴹ_ , (len $¿_) ∘ M) ✓ᴹ_
open WrapMem public using () renaming (
  --  WrapMemᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  Wrapᴱᴿᴬ to WrapMemᴱᴿᴬ)
module UpMem =  Syho.Model.ERA.Up WrapMemᴱᴿᴬ {2ᴸ} {2ᴸ} {2ᴸ} {2ᴸ}
open UpMem public using () renaming (
  --  Memᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ
  Upᴱᴿᴬ to Memᴱᴿᴬ)

open ERA Pntsᴱᴿᴬ public using () renaming (ε to εᴾⁿᵗˢ; _◇˜_ to _◇˜ᴾⁿᵗˢ_;
  ✓-resp to ✓ᴾⁿᵗˢ-resp)
open ERA Freeᴱᴿᴬ public using () renaming (ε to εᶠʳᵉᵉ; refl˜ to refl˜ᶠʳᵉᵉ)
open ERA Memᴱᴿᴬ public using () renaming (Res to Resᴹᵉᵐ; _≈_ to _≈ᴹᵉᵐ_;
  _✓_ to _✓ᴹᵉᵐ_; _∙_ to _∙ᴹᵉᵐ_; ◠˜_ to ◠˜ᴹᵉᵐ_)

private variable
  θ :  Addr
  p q :  ℚ⁺
  ᵗv ᵗw :  TyVal
  M :  Mem

--------------------------------------------------------------------------------
-- ↦⟨ ⟩ʳ :  Resource for the points-to token

infix 9 _↦⟨_⟩ʳ_
_↦⟨_⟩ʳ_ :  Addr →  ℚ⁺ →  TyVal →  Resᴹᵉᵐ
(θ ↦⟨ p ⟩ʳ ᵗv) .↓ =  inj˙ᴾⁿᵗˢ θ (š (p , [ ᵗv ])) , εᶠʳᵉᵉ

abstract

  ↦⟨⟩ʳ-agree :  ↑ M ✓ᴹᵉᵐ θ ↦⟨ p ⟩ʳ ᵗv ∙ᴹᵉᵐ θ ↦⟨ q ⟩ʳ ᵗw  →  ᵗv ≡ ᵗw
  ↦⟨⟩ʳ-agree (↑ (-, M✓θpvw , _)) =
    M✓θpvw ▷ ✓ᴾⁿᵗˢ-resp inj˙ᴾⁿᵗˢ-∙ ▷ ✓-inj˙ᴾⁿᵗˢ ▷ ✓ᶠʳ-agree2

  ↦⟨⟩ʳ-≤1 :  ↑ M ✓ᴹᵉᵐ θ ↦⟨ p ⟩ʳ ᵗv →  p ≤1ᴿ⁺
  ↦⟨⟩ʳ-≤1 (↑ (-, M✓θpv , _)) =  M✓θpv ▷ ✓-inj˙ᴾⁿᵗˢ ▷ ✓ᶠʳ-≤1

  ↦⟨⟩ʳ-∙ :  θ ↦⟨ p ⟩ʳ ᵗv ∙ᴹᵉᵐ θ ↦⟨ q ⟩ʳ ᵗv  ≈ᴹᵉᵐ  θ ↦⟨ p +ᴿ⁺ q ⟩ʳ ᵗv
  ↦⟨⟩ʳ-∙ .↓ .π₁ =  refl˜ᶠʳᵉᵉ
  ↦⟨⟩ʳ-∙ {p = p} {q = q} .↓ .π₀ =
    inj˙ᴾⁿᵗˢ-∙ ◇˜ᴾⁿᵗˢ inj˙ᴾⁿᵗˢ-≈ $ š[?]-∙ᶠʳ {p} {q = q}

--------------------------------------------------------------------------------
-- freeʳ :  Resource for the freeing token

freeʳ :  ℕ →  ℕ →  Resᴹᵉᵐ
freeʳ n o .↓ =  εᴾⁿᵗˢ , inj˙ᶠʳᵉᵉ o (#ˣ n)
