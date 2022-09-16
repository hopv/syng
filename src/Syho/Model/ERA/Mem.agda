--------------------------------------------------------------------------------
-- Memory ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Mem where

open import Base.Level using (0ᴸ; 2ᴸ; ↑_; ↓)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Eq using (_≡_; refl)
open import Base.Nat using (ℕ)
open import Base.Prod using (π₀; π₁; _,_; -,_; _,-)
open import Base.Option using (š_; ň; _»-¿_; _$¿_)
open import Base.Dec using (upd˙)
open import Base.List using ([_]; len; _‼_)
open import Base.RatPos using (ℚ⁺; _+ᴿ⁺_; _≤1ᴿ⁺)
open import Syho.Lang.Expr using (Addr; addr; TyVal)
open import Syho.Lang.Reduce using (Mblo; Mem; _‼ᴹ_; ✓ᴹ_)
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Exc using (Excᴱᴿᴬ; #ˣ_; ?ˣ)
open import Syho.Model.ERA.Frac using (Fracᴱᴿᴬ; š[?]-∙ᶠʳ; ✓ᶠʳ-≤1; ✓ᶠʳ-agree2)
import Syho.Model.ERA.All
import Syho.Model.ERA.Prod
import Syho.Model.ERA.Envm
import Syho.Model.ERA.Envv
import Syho.Model.ERA.Up

--------------------------------------------------------------------------------
-- Memᴱᴿᴬ :  Memory ERA

-- For the points-to token

module AllPnts =  Syho.Model.ERA.All ℕ (λ _ → Fracᴱᴿᴬ TyVal)
open AllPnts public using () renaming (
  --  Pntsᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  ∀ᴱᴿᴬ to Pntsᴱᴿᴬ;
  --  inj˙ᴾⁿᵗˢ :  ℕ →  Fracᴱᴿᴬ TyVal →  Pntsᴱᴿᴬ .Res
  inj˙ to inj˙ᴾⁿᵗˢ;
  inj˙-∙ to inj˙ᴾⁿᵗˢ-∙; inj˙-≈ to inj˙ᴾⁿᵗˢ-≈; ✓-inj˙ to ✓-inj˙ᴾⁿᵗˢ)

-- For the freeing token

Freeᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
Freeᴱᴿᴬ =  Excᴱᴿᴬ ℕ

-- For the memory block

module ProdMblo =  Syho.Model.ERA.Prod Pntsᴱᴿᴬ Freeᴱᴿᴬ
open ProdMblo public using () renaming (
  --  ×Mbloᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  ×ᴱᴿᴬ to ×Mbloᴱᴿᴬ)
module EnvmMblo =  Syho.Model.ERA.Envm ×Mbloᴱᴿᴬ
  Mblo (λ Mb → (λ i → Mb »-¿ (_‼ i)) , len $¿ Mb)
open EnvmMblo public using () renaming (
  --  Mbloᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  Envmᴱᴿᴬ to Mbloᴱᴿᴬ)

-- For the memory

module AllMem =  Syho.Model.ERA.All ℕ (λ _ → Mbloᴱᴿᴬ)
open AllMem public using () renaming (
  --  ∀Memᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  ∀ᴱᴿᴬ to ∀Memᴱᴿᴬ;
  --  inj˙ᴬᴹᵉᵐ :  ℕ →  Mbloᴱᴿᴬ .Res →  ∀Memᴱᴿᴬ .Res
  inj˙ to inj˙ᴬᴹᵉᵐ;
  inj˙-∙ to inj˙ᴬᴹᵉᵐ-∙; inj˙-≈ to inj˙ᴬᴹᵉᵐ-≈; ✓-inj˙ to ✓-inj˙ᴬᴹᵉᵐ)
module EnvvMem =  Syho.Model.ERA.Envv ∀Memᴱᴿᴬ ✓ᴹ_
open EnvvMem public using () renaming (
  --  EnvvMemᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  Envvᴱᴿᴬ to EnvvMemᴱᴿᴬ)
module UpMem =  Syho.Model.ERA.Up EnvvMemᴱᴿᴬ {2ᴸ} {2ᴸ} {2ᴸ} {2ᴸ}
open UpMem public using () renaming (
  --  Memᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ
  Upᴱᴿᴬ to Memᴱᴿᴬ)

open ERA Pntsᴱᴿᴬ public using () renaming (_◇˜_ to _◇˜ᴾⁿᵗˢ_;
  ✓-resp to ✓ᴾⁿᵗˢ-resp)
open ERA Mbloᴱᴿᴬ public using () renaming (Res to Resᴹᵇˡᵒ; _≈_ to _≈ᴹᵇˡᵒ_;
  _✓_ to _✓ᴹᵇˡᵒ_; _∙_ to _∙ᴹᵇˡᵒ_)
open ERA ∀Memᴱᴿᴬ public using () renaming (✓-resp to ✓ᴬᴹᵉᵐ-resp)
open ERA Memᴱᴿᴬ public using () renaming (Res to Resᴹᵉᵐ; _≈_ to _≈ᴹᵉᵐ_;
  _✓_ to _✓ᴹᵉᵐ_; _∙_ to _∙ᴹᵉᵐ_; ◠˜_ to ◠˜ᴹᵉᵐ_; _◇˜_ to _◇˜ᴹᵉᵐ_)

private variable
  θ :  Addr
  i :  ℕ
  p q :  ℚ⁺
  ᵗv ᵗw :  TyVal
  Mb :  Mblo
  M :  Mem

--------------------------------------------------------------------------------
-- ↦⟨ ⟩ᵇˡᵒ, freeᵇˡᵒ :  Block-level resource for the points-to / freeing token

infix 9 _↦⟨_⟩ᵇˡᵒ_
_↦⟨_⟩ᵇˡᵒ_ :  ℕ →  ℚ⁺ →  TyVal →  Resᴹᵇˡᵒ
i ↦⟨ p ⟩ᵇˡᵒ ᵗv =  inj˙ᴾⁿᵗˢ i (š (p , [ ᵗv ])) , ?ˣ

freeᵇˡᵒ :  ℕ →  Resᴹᵇˡᵒ
freeᵇˡᵒ n =  (λ _ → ň) , #ˣ n

abstract

  -- Agreement of ↦⟨ ⟩ᵇˡᵒ

  ↦⟨⟩ᵇˡᵒ-agree :  Mb ✓ᴹᵇˡᵒ i ↦⟨ p ⟩ᵇˡᵒ ᵗv ∙ᴹᵇˡᵒ i ↦⟨ q ⟩ᵇˡᵒ ᵗw  →  ᵗv ≡ ᵗw
  ↦⟨⟩ᵇˡᵒ-agree =  π₀ › ✓ᴾⁿᵗˢ-resp inj˙ᴾⁿᵗˢ-∙ › ✓-inj˙ᴾⁿᵗˢ › ✓ᶠʳ-agree2

  -- The fraction of ↦⟨ ⟩ᵇˡᵒ is no more than 1

  ↦⟨⟩ᵇˡᵒ-≤1 :  Mb ✓ᴹᵇˡᵒ i ↦⟨ p ⟩ᵇˡᵒ ᵗv →  p ≤1ᴿ⁺
  ↦⟨⟩ᵇˡᵒ-≤1 =  π₀ › ✓-inj˙ᴾⁿᵗˢ › ✓ᶠʳ-≤1

  -- Merge ↦⟨ ⟩ᵇˡᵒ with ∙ᴹᵇˡᵒ

  ↦⟨⟩ᵇˡᵒ-∙ :  i ↦⟨ p ⟩ᵇˡᵒ ᵗv ∙ᴹᵇˡᵒ i ↦⟨ q ⟩ᵇˡᵒ ᵗv  ≈ᴹᵇˡᵒ i ↦⟨ p +ᴿ⁺ q ⟩ᵇˡᵒ ᵗv
  ↦⟨⟩ᵇˡᵒ-∙ .π₁ =  refl
  ↦⟨⟩ᵇˡᵒ-∙ {p = p} {q = q} .π₀ =
    inj˙ᴾⁿᵗˢ-∙ ◇˜ᴾⁿᵗˢ inj˙ᴾⁿᵗˢ-≈ $ š[?]-∙ᶠʳ {p} {q = q}

--------------------------------------------------------------------------------
-- ↦⟨ ⟩ʳ, freeʳ :  Resource for the points-to / freeing token

infix 9 _↦⟨_⟩ʳ_
_↦⟨_⟩ʳ_ :  Addr →  ℚ⁺ →  TyVal →  Resᴹᵉᵐ
(addr o i ↦⟨ p ⟩ʳ ᵗv) .↓ =  inj˙ᴬᴹᵉᵐ o $ i ↦⟨ p ⟩ᵇˡᵒ ᵗv

freeʳ :  ℕ →  ℕ →  Resᴹᵉᵐ
freeʳ n o .↓ =  inj˙ᴬᴹᵉᵐ o $ freeᵇˡᵒ n

abstract

  -- Agreement of ↦⟨ ⟩ʳ

  ↦⟨⟩ʳ-agree :  ↑ M ✓ᴹᵉᵐ θ ↦⟨ p ⟩ʳ ᵗv ∙ᴹᵉᵐ θ ↦⟨ q ⟩ʳ ᵗw  →  ᵗv ≡ ᵗw
  ↦⟨⟩ʳ-agree {M} =  ↓ › π₁ ›
    ✓ᴬᴹᵉᵐ-resp inj˙ᴬᴹᵉᵐ-∙ › ✓-inj˙ᴬᴹᵉᵐ › ↦⟨⟩ᵇˡᵒ-agree {M _}

  -- The fraction of ↦⟨ ⟩ʳ is no more than 1

  ↦⟨⟩ʳ-≤1 :  ↑ M ✓ᴹᵉᵐ θ ↦⟨ p ⟩ʳ ᵗv →  p ≤1ᴿ⁺
  ↦⟨⟩ʳ-≤1 {M} =  ↓ › π₁ › ✓-inj˙ᴬᴹᵉᵐ › ↦⟨⟩ᵇˡᵒ-≤1 {M _}

  -- Merge ↦⟨ ⟩ʳ with ∙ʳ

  ↦⟨⟩ʳ-∙ :  θ ↦⟨ p ⟩ʳ ᵗv ∙ᴹᵉᵐ θ ↦⟨ q ⟩ʳ ᵗv  ≈ᴹᵉᵐ  θ ↦⟨ p +ᴿ⁺ q ⟩ʳ ᵗv
  ↦⟨⟩ʳ-∙ =  ↑ inj˙ᴬᴹᵉᵐ-∙ ◇˜ᴹᵉᵐ ↑ inj˙ᴬᴹᵉᵐ-≈ ↦⟨⟩ᵇˡᵒ-∙
