--------------------------------------------------------------------------------
-- Interpret the points-to and freeing tokens
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Mem where

open import Base.Level using (2ᴸ)
open import Base.Func using (_$_; _›_)
open import Base.Eq using (_≡_)
open import Base.Prod using (_,_; -,_)
open import Base.Nat using (ℕ; +-0)
open import Base.List using (List; []; _∷_)
open import Base.RatPos using (ℚ⁺; 1ᴿ⁺; _+ᴿ⁺_; _≤1ᴿ⁺)
open import Syho.Lang.Expr using (Addr; addr; _ₒ_; TyVal)
open import Syho.Model.ERA.Exc using (?ˣ)
open import Syho.Model.ERA.Mem using (Memᴱᴿᴬ; ◠˜ᴹᵉᵐ_; [∙ᴹᵉᵐ∈ⁱ]-syntax;
  [∙ᴹᵉᵐ∈ⁱ⟨⟩]-syntax; _↦⟨_⟩ʳ_; _↦ʳ_; freeʳ; _↦ᴸʳ_; ↦⟨⟩ʳ-agree; ↦⟨⟩ʳ-≤1; ↦⟨⟩ʳ-∙;
  [∙∈ⁱ]↦≈↦ᴸʳ)
open import Syho.Model.ERA.Glob using (iᴹᵉᵐ)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; ∃ᵒ-syntax;
  ∃ᵒ∈-syntax; ⌜_⌝ᵒ; _∗ᵒ_; [∗ᵒ∈ⁱ]-syntax; [∗ᵒ∈ⁱ⟨⟩]-syntax; ◎⟨_⟩_; ∃ᵒ-Mono;
  ∗ᵒ-monoʳ; ◎-Mono; ◎⟨⟩-cong; ◎⟨⟩-ε; ◎⟨⟩-∗ᵒ⇒∙; ◎⟨⟩-∙⇒∗ᵒ; ◎⟨⟩-✓)

private variable
  i k n o :  ℕ
  θ :  Addr
  p q :  ℚ⁺
  ᵗu ᵗv :  TyVal
  ᵗvs :  List TyVal

--------------------------------------------------------------------------------
-- Interpret the points-to and freeing tokens

infix 9 _↦⟨_⟩ᵒ_ _↦ᵒ_

-- ↦⟨ ⟩ᵒ : Interpret the points-to token

_↦⟨_⟩ᵒ_ :  Addr →  ℚ⁺ →  TyVal →  Propᵒ 2ᴸ
θ ↦⟨ p ⟩ᵒ ᵗv =  ◎⟨ iᴹᵉᵐ ⟩ θ ↦⟨ p ⟩ʳ ᵗv

-- ↦ᵒ : ↦⟨ ⟩ᵒ with the fraction 1

_↦ᵒ_ :  Addr →  TyVal →  Propᵒ 2ᴸ
θ ↦ᵒ ᵗv =  θ ↦⟨ 1ᴿ⁺ ⟩ᵒ ᵗv

-- Freeᵒ' : The freeing token over a block id

Freeᵒ' :  ℕ →  ℕ →  Propᵒ 2ᴸ
Freeᵒ' n o =  ◎⟨ iᴹᵉᵐ ⟩ freeʳ n o

-- Freeᵒ : Interpret the freeing token

Freeᵒ :  ℕ →  Addr →  Propᵒ 2ᴸ
Freeᵒ n θ =  ∃ᵒ o , ∃ᵒ _ ∈ θ ≡ addr o 0 , Freeᵒ' n o

-- ↦ᴸᵒ, ↦ᴸᵒ' :  Interpret the points-to token over a list of values

infix 9 _↦ᴸᵒ_ _↦ᴸᵒ'_

_↦ᴸᵒ_ :  Addr →  List TyVal →  Propᵒ 2ᴸ
θ ↦ᴸᵒ ᵗvs =  [∗ᵒ (i , ᵗv) ∈ⁱ ᵗvs ] θ ₒ i ↦ᵒ ᵗv

_↦ᴸᵒ'_ :  ℕ →  List TyVal →  Propᵒ 2ᴸ
o ↦ᴸᵒ' ᵗvs =  ◎⟨ iᴹᵉᵐ ⟩ o ↦ᴸʳ ᵗvs

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

  -- [∗ᵒ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] addr o 0 ₒ i ↦ᵒ ᵗv  agrees with
  -- ◎⟨ iᴹᵉᵐ ⟩ [∙ᴹᵉᵐ (i , ᵗv) ∈ⁱ ᵗvs ] addr o i ↦ʳ ᵗv

  [∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ⇒◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ :
    [∗ᵒ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] addr o 0 ₒ i ↦ᵒ ᵗv  ⊨
      ◎⟨ iᴹᵉᵐ ⟩ [∙ᴹᵉᵐ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] addr o i ↦ʳ ᵗv
  [∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ⇒◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ {ᵗvs = []} _ =  ◎⟨⟩-ε
  [∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ⇒◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ {k} {_ ∷ ᵗvs'}  rewrite +-0 {k} =
    ∗ᵒ-monoʳ ([∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ⇒◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ {ᵗvs = ᵗvs'}) › ◎⟨⟩-∗ᵒ⇒∙

  ◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ⇒[∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ :
    ◎⟨ iᴹᵉᵐ ⟩ [∙ᴹᵉᵐ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] addr o i ↦ʳ ᵗv  ⊨
      [∗ᵒ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] addr o 0 ₒ i ↦ᵒ ᵗv
  ◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ⇒[∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ {ᵗvs = []} _ =  _
  ◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ⇒[∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ {k} {_ ∷ ᵗvs'}  rewrite +-0 {k} =
    ◎⟨⟩-∙⇒∗ᵒ › ∗ᵒ-monoʳ $ ◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ⇒[∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ {ᵗvs = ᵗvs'}

  -- addr o 0 ↦ᴸᵒ ᵗvs  agrees with  o ↦ᴸᵒ' ᵗvs

  ↦ᴸᵒ⇒↦ᴸᵒ' :  addr o 0 ↦ᴸᵒ ᵗvs  ⊨  o ↦ᴸᵒ' ᵗvs
  ↦ᴸᵒ⇒↦ᴸᵒ' {ᵗvs = ᵗvs} =  [∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ⇒◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ {ᵗvs = ᵗvs} ›
    ◎⟨⟩-cong $ [∙∈ⁱ]↦≈↦ᴸʳ {ᵗvs = ᵗvs}

  ↦ᴸᵒ'⇒↦ᴸᵒ :  o ↦ᴸᵒ' ᵗvs  ⊨  addr o 0 ↦ᴸᵒ ᵗvs
  ↦ᴸᵒ'⇒↦ᴸᵒ {ᵗvs = ᵗvs} =  ◎⟨⟩-cong (◠˜ᴹᵉᵐ [∙∈ⁱ]↦≈↦ᴸʳ {ᵗvs = ᵗvs}) ›
    ◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ⇒[∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ {ᵗvs = ᵗvs}
