--------------------------------------------------------------------------------
-- Interpret the lifetime and dead lifetime tokens
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Symp.Model.Prop.Lft where

open import Base.Level using (1ᴸ)
open import Base.Func using (_$_; _›_)
open import Base.Prod using (-,_)
open import Base.Ratp using (ℚ⁺; 1ᴿ⁺; _≈ᴿ⁺_; _+ᴿ⁺_; _≤1ᴿ⁺; _/2⁺; /2⁺-merge;
  /2⁺-split)
open import Symp.Logic.Prop using (Lft)
open import Symp.Model.ERA.Lft using ([_]ᴸ⟨_⟩ʳ; †ᴸʳ_; ◠˜ᴸᶠᵗ_; []ᴸ⟨⟩ʳ-cong;
  []ᴸ⟨⟩ʳ-∙; []ᴸ⟨⟩ʳ-≤1; †ᴸʳ-⌞⌟; []ᴸ⟨⟩ʳ-†ᴸʳ-no; []ᴸʳ-new; []ᴸʳ-kill)
open import Symp.Model.ERA.Glob using (iᴸᶠᵗ)
open import Symp.Model.Prop.Base using (SPropᵒ; _⊨✓_; _⊨_; ⊨_; ∃ᵒ-syntax; ⌜_⌝ᵒ;
  ⊥ᵒ₀; _∗ᵒ_; □ᵒ_; ⤇ᵒ_; ◎⟨_⟩_; dup-⇒□ᵒ; ◎-Mono; ◎⟨⟩-resp; ◎⟨⟩-∗ᵒ⇒∙; ◎⟨⟩-∙⇒∗ᵒ;
  ◎⟨⟩-⌞⌟≈-□ᵒ; ◎⟨⟩-✓; ε↝-◎⟨⟩-⤇ᵒ-∃ᵒ; ↝-◎⟨⟩-⤇ᵒ)

private variable
  α :  Lft
  p q :  ℚ⁺

--------------------------------------------------------------------------------
-- Interpret the lifetime and dead lifetime tokens

-- [ ]ᴸ⟨ ⟩ᵒ :  Interpret the lifetime token

[_]ᴸ⟨_⟩ᵒ :  Lft →  ℚ⁺ →  SPropᵒ 1ᴸ
[ α ]ᴸ⟨ p ⟩ᵒ =  ◎⟨ iᴸᶠᵗ ⟩ [ α ]ᴸ⟨ p ⟩ʳ

[_]ᴸᵒ :  Lft →  SPropᵒ 1ᴸ
[ α ]ᴸᵒ =  [ α ]ᴸ⟨ 1ᴿ⁺ ⟩ᵒ

-- †ᴸᵒ :  Interpret the dead lifetime token

infix 8 †ᴸᵒ_
†ᴸᵒ_ :  Lft →  SPropᵒ 1ᴸ
†ᴸᵒ α =  ◎⟨ iᴸᶠᵗ ⟩ †ᴸʳ α

abstract

  -- Modify the fraction of [ ]ᴸ⟨ ⟩ᵒ

  []ᴸ⟨⟩ᵒ-resp :  p ≈ᴿ⁺ q  →   [ α ]ᴸ⟨ p ⟩ᵒ  ⊨  [ α ]ᴸ⟨ q ⟩ᵒ
  []ᴸ⟨⟩ᵒ-resp p≈q =  ◎⟨⟩-resp $ []ᴸ⟨⟩ʳ-cong p≈q

  -- Merge and split [ ]ᴸ⟨ ⟩ᵒ w.r.t. +ᴿ⁺

  []ᴸ⟨⟩ᵒ-merge :  [ α ]ᴸ⟨ p ⟩ᵒ  ∗ᵒ  [ α ]ᴸ⟨ q ⟩ᵒ  ⊨  [ α ]ᴸ⟨ p +ᴿ⁺ q ⟩ᵒ
  []ᴸ⟨⟩ᵒ-merge =  ◎⟨⟩-∗ᵒ⇒∙ › ◎⟨⟩-resp []ᴸ⟨⟩ʳ-∙

  []ᴸ⟨⟩ᵒ-split :  [ α ]ᴸ⟨ p +ᴿ⁺ q ⟩ᵒ  ⊨  [ α ]ᴸ⟨ p ⟩ᵒ  ∗ᵒ  [ α ]ᴸ⟨ q ⟩ᵒ
  []ᴸ⟨⟩ᵒ-split =  ◎⟨⟩-resp (◠˜ᴸᶠᵗ []ᴸ⟨⟩ʳ-∙) › ◎⟨⟩-∙⇒∗ᵒ

  []ᴸ⟨⟩ᵒ-merge-/2 :  [ α ]ᴸ⟨ p /2⁺ ⟩ᵒ  ∗ᵒ  [ α ]ᴸ⟨ p /2⁺ ⟩ᵒ  ⊨  [ α ]ᴸ⟨ p ⟩ᵒ
  []ᴸ⟨⟩ᵒ-merge-/2 {p = p} =  []ᴸ⟨⟩ᵒ-merge › []ᴸ⟨⟩ᵒ-resp $ /2⁺-merge {p}

  []ᴸ⟨⟩ᵒ-split-/2 :  [ α ]ᴸ⟨ p ⟩ᵒ  ⊨  [ α ]ᴸ⟨ p /2⁺ ⟩ᵒ  ∗ᵒ  [ α ]ᴸ⟨ p /2⁺ ⟩ᵒ
  []ᴸ⟨⟩ᵒ-split-/2 {p = p} =  []ᴸ⟨⟩ᵒ-resp (/2⁺-split {p}) › []ᴸ⟨⟩ᵒ-split

  -- The fraction of [ ]ᴸ⟨ ⟩ᵒ is no more than 1

  []ᴸ⟨⟩ᵒ-≤1 :  [ α ]ᴸ⟨ p ⟩ᵒ  ⊨✓  ⌜ p ≤1ᴿ⁺ ⌝ᵒ
  []ᴸ⟨⟩ᵒ-≤1 ✓∙ =  ◎⟨⟩-✓ ✓∙ › λ (-, ✓αp) → []ᴸ⟨⟩ʳ-≤1 ✓αp

  -- The dead lifetime token is persistent

  †ᴸᵒ-⇒□ᵒ :  †ᴸᵒ α  ⊨  □ᵒ †ᴸᵒ α
  †ᴸᵒ-⇒□ᵒ =  ◎⟨⟩-⌞⌟≈-□ᵒ †ᴸʳ-⌞⌟

  -- Duplicate †ᴸᵒ

  dup-†ᴸᵒ :  †ᴸᵒ α  ⊨  †ᴸᵒ α  ∗ᵒ  †ᴸᵒ α
  dup-†ᴸᵒ =  dup-⇒□ᵒ ◎-Mono †ᴸᵒ-⇒□ᵒ

  -- The lifetime and dead lifetime tokens for a lifetime cannot coexist

  []ᴸ⟨⟩ᵒ-†ᴸᵒ-no :  [ α ]ᴸ⟨ p ⟩ᵒ  ∗ᵒ  †ᴸᵒ α  ⊨✓  ⊥ᵒ₀
  []ᴸ⟨⟩ᵒ-†ᴸᵒ-no ✓∙ =  ◎⟨⟩-∗ᵒ⇒∙ ›
    ◎⟨⟩-✓ ✓∙ › λ (-, ✓αp∙†α) → []ᴸ⟨⟩ʳ-†ᴸʳ-no ✓αp∙†α

  -- Allocate a new lifetime

  []ᴸᵒ-new :  ⊨ ⤇ᵒ  ∃ᵒ α , [ α ]ᴸᵒ
  []ᴸᵒ-new =  ε↝-◎⟨⟩-⤇ᵒ-∃ᵒ []ᴸʳ-new

  -- Kill a lifetime consuming a full lifetime token

  []ᴸᵒ-kill :  [ α ]ᴸᵒ  ⊨ ⤇ᵒ  †ᴸᵒ α
  []ᴸᵒ-kill =  ↝-◎⟨⟩-⤇ᵒ []ᴸʳ-kill
