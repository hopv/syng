--------------------------------------------------------------------------------
-- Interpret the lifetime and dead lifetime tokens
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Lft where

open import Base.Level using (1ᴸ)
open import Base.Func using (_›_)
open import Base.Prod using (-,_)
open import Base.Ratp using (ℚ⁺; 1ᴿ⁺; _+ᴿ⁺_; _≤1ᴿ⁺)
open import Syho.Logic.Prop using (Lft)
open import Syho.Model.ERA.Lft using ([_]ᴸ⟨_⟩ʳ; †ᴸʳ_; ◠˜ᴸᶠᵗ_; []ᴸ⟨⟩ʳ-∙;
  []ᴸ⟨⟩ʳ-≤1; †ᴸʳ-⌞⌟; []ᴸ⟨⟩ʳ-†ᴸʳ-no; []ᴸʳ-new)
open import Syho.Model.ERA.Glob using (iᴸᶠᵗ)
open import Syho.Model.Prop.Base using (Propᵒ; _⊨✓_; _⊨_; ⊨_; ∃ᵒ-syntax; ⌜_⌝ᵒ;
  ⊥ᵒ₀; _∗ᵒ_; □ᵒ_; ⤇ᵒ_; ◎⟨_⟩_; ◎⟨⟩-resp; ◎⟨⟩-∗ᵒ⇒∙; ◎⟨⟩-∙⇒∗ᵒ; ◎⟨⟩-⌞⌟≈-□ᵒ; ◎⟨⟩-✓;
  ε↝-◎⟨⟩-⤇ᵒ-∃ᵒ)

private variable
  α :  Lft
  p q :  ℚ⁺

--------------------------------------------------------------------------------
-- Interpret the lifetime and dead lifetime tokens

-- [ ]ᴸ⟨ ⟩ᵒ :  Interpret the lifetime token

[_]ᴸ⟨_⟩ᵒ :  Lft →  ℚ⁺ →  Propᵒ 1ᴸ
[ α ]ᴸ⟨ p ⟩ᵒ =  ◎⟨ iᴸᶠᵗ ⟩ [ α ]ᴸ⟨ p ⟩ʳ

[_]ᴸᵒ :  Lft →  Propᵒ 1ᴸ
[ α ]ᴸᵒ =  [ α ]ᴸ⟨ 1ᴿ⁺ ⟩ᵒ

-- †ᴸᵒ :  Interpret the dead lifetime token

infix 8 †ᴸᵒ_
†ᴸᵒ_ :  Lft →  Propᵒ 1ᴸ
†ᴸᵒ α =  ◎⟨ iᴸᶠᵗ ⟩ †ᴸʳ α

abstract

  -- Merge and split [ ]ᴸ⟨ ⟩ᵒ w.r.t. +ᴿ⁺

  []ᴸ⟨⟩ᵒ-merge :  [ α ]ᴸ⟨ p ⟩ᵒ  ∗ᵒ  [ α ]ᴸ⟨ q ⟩ᵒ  ⊨  [ α ]ᴸ⟨ p +ᴿ⁺ q ⟩ᵒ
  []ᴸ⟨⟩ᵒ-merge =  ◎⟨⟩-∗ᵒ⇒∙ › ◎⟨⟩-resp []ᴸ⟨⟩ʳ-∙

  []ᴸ⟨⟩ᵒ-split :  [ α ]ᴸ⟨ p +ᴿ⁺ q ⟩ᵒ  ⊨  [ α ]ᴸ⟨ p ⟩ᵒ  ∗ᵒ  [ α ]ᴸ⟨ q ⟩ᵒ
  []ᴸ⟨⟩ᵒ-split =  ◎⟨⟩-resp (◠˜ᴸᶠᵗ []ᴸ⟨⟩ʳ-∙) › ◎⟨⟩-∙⇒∗ᵒ

  -- The fraction of [ ]ᴸ⟨ ⟩ᵒ is no more than 1

  []ᴸ⟨⟩ᵒ-≤1 :  [ α ]ᴸ⟨ p ⟩ᵒ  ⊨✓  ⌜ p ≤1ᴿ⁺ ⌝ᵒ
  []ᴸ⟨⟩ᵒ-≤1 ✓∙ =  ◎⟨⟩-✓ ✓∙ › λ (-, ✓αp) → []ᴸ⟨⟩ʳ-≤1 ✓αp

  -- The dead lifetime token is persistent

  †ᴸᵒ-⇒□ᵒ :  †ᴸᵒ α  ⊨  □ᵒ †ᴸᵒ α
  †ᴸᵒ-⇒□ᵒ =  ◎⟨⟩-⌞⌟≈-□ᵒ †ᴸʳ-⌞⌟

  -- The lifetime and dead lifetime tokens for a lifetime cannot coexist

  []ᴸ⟨⟩ᵒ-†ᴸᵒ-no :  [ α ]ᴸ⟨ p ⟩ᵒ  ∗ᵒ  †ᴸᵒ α  ⊨✓  ⊥ᵒ₀
  []ᴸ⟨⟩ᵒ-†ᴸᵒ-no ✓∙ =  ◎⟨⟩-∗ᵒ⇒∙ ›
    ◎⟨⟩-✓ ✓∙ › λ (-, ✓αp∙†α) → []ᴸ⟨⟩ʳ-†ᴸʳ-no ✓αp∙†α

  -- Allocate a new lifetime

  []ᴸᵒ-new :  ⊨ ⤇ᵒ  ∃ᵒ α , [ α ]ᴸᵒ
  []ᴸᵒ-new =  ε↝-◎⟨⟩-⤇ᵒ-∃ᵒ []ᴸʳ-new
