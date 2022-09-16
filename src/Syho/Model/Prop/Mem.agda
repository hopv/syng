--------------------------------------------------------------------------------
-- Interpret the points-to and freeing tokens
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Mem where

open import Base.Level using (2ᴸ)
open import Base.Func using (_$_; _›_)
open import Base.Eq using (_≡_)
open import Base.Prod using (-,_)
open import Base.Nat using (ℕ)
open import Base.List using (List)
open import Base.RatPos using (ℚ⁺; 1ᴿ⁺; _+ᴿ⁺_; _≤1ᴿ⁺)
open import Syho.Lang.Expr using (Addr; addr; TyVal)
open import Syho.Model.ERA.Exc using (?ˣ)
open import Syho.Model.ERA.Mem using (Memᴱᴿᴬ; ◠˜ᴹᵉᵐ_; _↦⟨_⟩ʳ_; freeʳ; _↦ᴸʳ_;
  ↦⟨⟩ʳ-agree; ↦⟨⟩ʳ-≤1; ↦⟨⟩ʳ-∙)
open import Syho.Model.ERA.Glob using (iᴹᵉᵐ)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; ∃ᵒ-syntax;
  ∃ᵒ∈-syntax; ⌜_⌝ᵒ; _∗ᵒ_; ◎⟨_⟩_; ∃ᵒ-Mono; ◎-Mono; ◎⟨⟩-cong; ◎⟨⟩-∗ᵒ⇒∙; ◎⟨⟩-∙⇒∗ᵒ;
  ◎⟨⟩-✓)

private variable
  n :  ℕ
  θ :  Addr
  p q :  ℚ⁺
  ᵗu ᵗv :  TyVal

--------------------------------------------------------------------------------
-- Interpret the points-to and freeing tokens

infix 9 _↦⟨_⟩ᵒ_ _↦ᵒ_

-- ↦⟨ ⟩ᵒ : Interpret the points-to token

_↦⟨_⟩ᵒ_ :  Addr →  ℚ⁺ →  TyVal →  Propᵒ 2ᴸ
θ ↦⟨ p ⟩ᵒ ᵗv =  ◎⟨ iᴹᵉᵐ ⟩ θ ↦⟨ p ⟩ʳ ᵗv

-- ↦ᵒ : ↦⟨ ⟩ᵒ with the fraction 1

_↦ᵒ_ :  Addr →  TyVal →  Propᵒ 2ᴸ
θ ↦ᵒ ᵗv =  θ ↦⟨ 1ᴿ⁺ ⟩ᵒ ᵗv

-- Freeᵒ : Interpret the freeing token

Freeᵒ :  ℕ →  Addr →  Propᵒ 2ᴸ
Freeᵒ n θ =  ∃ᵒ o , ∃ᵒ _ ∈ θ ≡ addr o 0 , ◎⟨ iᴹᵉᵐ ⟩ freeʳ n o

-- ↦ᴸᵒ :  Interpret the points-to token over a list of values

infix 9 _↦ᴸᵒ_
_↦ᴸᵒ_ :  ℕ →  List TyVal →  Propᵒ 2ᴸ
o ↦ᴸᵒ ᵗvs =  ◎⟨ iᴹᵉᵐ ⟩ o ↦ᴸʳ ᵗvs

abstract

  -- Mono for Freeᵒ

  Freeᵒ-Mono :  Monoᵒ $ Freeᵒ n θ
  Freeᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ◎-Mono

  -- Agreement of ↦⟨ ⟩ᵒ

  ↦⟨⟩ᵒ-agree :  θ ↦⟨ p ⟩ᵒ ᵗu  ∗ᵒ  θ ↦⟨ q ⟩ᵒ ᵗv  ⊨✓  ⌜ ᵗu ≡ ᵗv ⌝ᵒ
  ↦⟨⟩ᵒ-agree ✓∙ =  ◎⟨⟩-∗ᵒ⇒∙ › ◎⟨⟩-✓ ✓∙ › λ (-, ✓↦⟨⟩ʳ) → ↦⟨⟩ʳ-agree ✓↦⟨⟩ʳ

  -- The fraction of ↦⟨ ⟩ᵒ is no more than 1

  ↦⟨⟩ᵒ-≤1 :  θ ↦⟨ p ⟩ᵒ ᵗv  ⊨✓  ⌜ p ≤1ᴿ⁺ ⌝ᵒ
  ↦⟨⟩ᵒ-≤1 ✓∙ =  ◎⟨⟩-✓ ✓∙ › λ (-, ✓↦⟨⟩ʳ) → ↦⟨⟩ʳ-≤1 ✓↦⟨⟩ʳ

  -- Merge and split ↦⟨ ⟩ᵒ with ∗ᵒ

  ↦⟨⟩ᵒ-merge :  θ ↦⟨ p ⟩ᵒ ᵗv  ∗ᵒ  θ ↦⟨ q ⟩ᵒ ᵗv  ⊨  θ ↦⟨ p +ᴿ⁺ q ⟩ᵒ ᵗv
  ↦⟨⟩ᵒ-merge =  ◎⟨⟩-∗ᵒ⇒∙ › ◎⟨⟩-cong ↦⟨⟩ʳ-∙

  ↦⟨⟩ᵒ-split :  θ ↦⟨ p +ᴿ⁺ q ⟩ᵒ ᵗv  ⊨  θ ↦⟨ p ⟩ᵒ ᵗv  ∗ᵒ  θ ↦⟨ q ⟩ᵒ ᵗv
  ↦⟨⟩ᵒ-split =  ◎⟨⟩-cong (◠˜ᴹᵉᵐ ↦⟨⟩ʳ-∙) › ◎⟨⟩-∙⇒∗ᵒ
