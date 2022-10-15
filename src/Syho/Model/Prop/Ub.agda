--------------------------------------------------------------------------------
-- Interpret the upper-boundee and upper-bound tokens
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Ub where

open import Base.Level using (1ᴸ)
open import Base.Func using (_▷_; _›_)
open import Base.Prod using (_,_; -,_)
open import Base.Nat using (ℕ; _≤_; _⊓_)
open import Syho.Model.ERA.Ub using (#ᵁᵇ⟨_⟩ʳ_; ≤ᵁᵇ⟨_⟩ʳ_; ◠˜ᵁᵇ_; ≤ᵁᵇʳ-∙; ≤ᵁᵇʳ-⌞⌟;
  ≤ᵁᵇʳ-#ᵁᵇʳ; #ᵁᵇʳ-new; #ᵁᵇʳ-upd)
open import Syho.Model.ERA.Glob using (iᵁᵇ)
open import Syho.Model.Prop.Base using (Propᵒ; _⊨✓_; _⊨_; ⊨_; ∃ᵒ-syntax; ⌜_⌝ᵒ;
  _∗ᵒ_; □ᵒ_; ⤇ᵒ_; ◎⟨_⟩_; ⤇ᵒ-mono; ◎⟨⟩-resp; ◎⟨⟩-∗ᵒ⇒∙; ◎⟨⟩-∙⇒∗ᵒ; ◎⟨⟩-✓;
  ◎⟨⟩-⌞⌟≈-□ᵒ; ε↝-◎⟨⟩-⤇ᵒ-∃ᵒ; ↝-◎⟨⟩-⤇ᵒ)

private variable
  i m n :  ℕ

--------------------------------------------------------------------------------
-- Interpret the upper-boundee and upper-bound tokens

-- #ᵁᵇ⟨ ⟩ᵒ :  Interpret the upper-boundee token

infix 8 #ᵁᵇ⟨_⟩ᵒ_
#ᵁᵇ⟨_⟩ᵒ_ :  ℕ →  ℕ →  Propᵒ 1ᴸ
#ᵁᵇ⟨ i ⟩ᵒ n =  ◎⟨ iᵁᵇ ⟩ #ᵁᵇ⟨ i ⟩ʳ n

-- ≤ᵁᵇ⟨ ⟩ᵒ :  Interpret the upper-bound token

infix 8 ≤ᵁᵇ⟨_⟩ᵒ_
≤ᵁᵇ⟨_⟩ᵒ_ :  ℕ →  ℕ →  Propᵒ 1ᴸ
≤ᵁᵇ⟨ i ⟩ᵒ n =  ◎⟨ iᵁᵇ ⟩ ≤ᵁᵇ⟨ i ⟩ʳ n

abstract

  -- Merge and split ≤ᵁᵇᵒ w.r.t. ⊓

  ≤ᵁᵇᵒ-merge :  ≤ᵁᵇ⟨ i ⟩ᵒ m  ∗ᵒ  ≤ᵁᵇ⟨ i ⟩ᵒ n  ⊨  ≤ᵁᵇ⟨ i ⟩ᵒ (m ⊓ n)
  ≤ᵁᵇᵒ-merge =  ◎⟨⟩-∗ᵒ⇒∙ › ◎⟨⟩-resp ≤ᵁᵇʳ-∙

  ≤ᵁᵇᵒ-split :  ≤ᵁᵇ⟨ i ⟩ᵒ (m ⊓ n)  ⊨  ≤ᵁᵇ⟨ i ⟩ᵒ m  ∗ᵒ  ≤ᵁᵇ⟨ i ⟩ᵒ n
  ≤ᵁᵇᵒ-split =  ◎⟨⟩-resp (◠˜ᵁᵇ ≤ᵁᵇʳ-∙) › ◎⟨⟩-∙⇒∗ᵒ

  -- The upper-bound token is persistent

  ≤ᵁᵇᵒ-⇒□ᵒ :  ≤ᵁᵇ⟨ i ⟩ᵒ n  ⊨  □ᵒ ≤ᵁᵇ⟨ i ⟩ᵒ n
  ≤ᵁᵇᵒ-⇒□ᵒ =  ◎⟨⟩-⌞⌟≈-□ᵒ ≤ᵁᵇʳ-⌞⌟

  -- Upper bound #ᵁᵇᵒ with ≤ᵁᵇᵒ

  ≤ᵁᵇᵒ-#ᵁᵇᵒ :  ≤ᵁᵇ⟨ i ⟩ᵒ m  ∗ᵒ  #ᵁᵇ⟨ i ⟩ᵒ n  ⊨✓  ⌜ n ≤ m ⌝ᵒ
  ≤ᵁᵇᵒ-#ᵁᵇᵒ ✓∙ =  ◎⟨⟩-∗ᵒ⇒∙ › ◎⟨⟩-✓ ✓∙ › λ (-, ✓≤m∙#n) → ≤ᵁᵇʳ-#ᵁᵇʳ ✓≤m∙#n

  -- Create #ᵁᵇᵒ and ≤ᵁᵇᵒ at a fresh index

  #ᵁᵇᵒ-new :  ⊨ ⤇ᵒ  ∃ᵒ i , ≤ᵁᵇ⟨ i ⟩ᵒ n  ∗ᵒ  #ᵁᵇ⟨ i ⟩ᵒ n
  #ᵁᵇᵒ-new =  ε↝-◎⟨⟩-⤇ᵒ-∃ᵒ #ᵁᵇʳ-new ▷ ⤇ᵒ-mono λ (i , big) → i , ◎⟨⟩-∙⇒∗ᵒ big

  -- Kill a lifetime consuming a full lifetime token

  #ᵁᵇᵒ-upd :  m ≤ n  →   #ᵁᵇ⟨ i ⟩ᵒ n  ⊨ ⤇ᵒ  ≤ᵁᵇ⟨ i ⟩ᵒ m  ∗ᵒ  #ᵁᵇ⟨ i ⟩ᵒ m
  #ᵁᵇᵒ-upd m≤n =  ↝-◎⟨⟩-⤇ᵒ (#ᵁᵇʳ-upd m≤n) › ⤇ᵒ-mono ◎⟨⟩-∙⇒∗ᵒ
