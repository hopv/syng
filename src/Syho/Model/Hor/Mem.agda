--------------------------------------------------------------------------------
-- Semantic super update and weakest precondition lemmas for the memory
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Hor.Mem where

open import Base.Level using (Level)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Eq using (_≡_)
open import Base.Prod using (_,_)
open import Base.Option using (š_; ň)
open import Base.Dec using (upd˙)
open import Base.Nat using (ℕ)
open import Base.List using (List; len; rep)
open import Base.RatPos using (ℚ⁺)
open import Syho.Lang.Expr using (Addr; addr; TyVal; ⊤ṽ)
open import Syho.Lang.Reduce using (Mem; _‼ᴹ_; updᴹ)
open import Syho.Model.ERA.Glob using (upd˙-mem-envᴳ)
open import Syho.Model.ERA.Mem using (εᴹᵉᵐ; ↦⟨⟩ʳ-read; ↦ʳ-write; ↦ᴸʳ-alloc;
  ↦ᴸʳ-free)
open import Syho.Model.Prop.Base using (Propᵒ; _⊨_; ⊨_; ⌜_⌝ᵒ×_; ⊤ᵒ₀; _∗ᵒ_;
  _⤇ᴱ_; ⤇ᴱ-mono; ⤇ᴱ-respᴱʳ; ⤇ᴱ-param; ◎⟨⟩-∗ᵒ⇒∙; ◎⟨⟩-∙⇒∗ᵒ; ↝-◎⟨⟩-⤇ᴱ; ε↝-◎⟨⟩-⤇ᴱ)
open import Syho.Model.Prop.Mem using (_↦⟨_⟩ᵒ_; _↦ᵒ_; Freeᵒ'; _↦ᴸᵒ'_)
open import Syho.Model.Supd.Interp using (⟨_⟩⇛ᵒ⟨_⟩_; ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᵒ; ⊨⤇ᴱᴹᵉᵐ⇒⊨⇛ᵒ)

private variable
  ł :  Level
  Pᵒ Qᵒ :  Propᵒ ł
  M M' :  Mem
  θ :  Addr
  p :  ℚ⁺
  o n :  ℕ
  ᵗu ᵗv :  TyVal
  ᵗvs :  List TyVal

--------------------------------------------------------------------------------
-- Semantic super update for the memory

abstract

  -- Read using ↦⟨⟩ᵒ

  ↦⟨⟩ᵒ-read :  θ ↦⟨ p ⟩ᵒ ᵗv  ⊨  ⟨ M ⟩⇛ᵒ⟨ M ⟩
                ⌜ M ‼ᴹ θ ≡ š ᵗv ⌝ᵒ×  θ ↦⟨ p ⟩ᵒ ᵗv
  ↦⟨⟩ᵒ-read =  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᵒ $ ↝-◎⟨⟩-⤇ᴱ ↦⟨⟩ʳ-read › ⤇ᴱ-respᴱʳ upd˙-mem-envᴳ ›
    ⤇ᴱ-mono (λ M‼θ≡v →  M‼θ≡v ,_) › ⤇ᴱ-param

  -- Write using ↦ᵒ

  ↦ᵒ-write :  θ ↦ᵒ ᵗu  ⊨  ⟨ M ⟩⇛ᵒ⟨ updᴹ θ ᵗv M ⟩  θ ↦ᵒ ᵗv
  ↦ᵒ-write =  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᵒ $ ↝-◎⟨⟩-⤇ᴱ ↦ʳ-write › ⤇ᴱ-respᴱʳ upd˙-mem-envᴳ

  -- Allocate getting ↦ᴸᵒ' and Freeᵒ'

  ↦ᴸᵒ'-alloc :  M o ≡ ň  →
    ⊨  ⟨ M ⟩⇛ᵒ⟨ upd˙ o (š rep n ⊤ṽ) M ⟩  o ↦ᴸᵒ' rep n ⊤ṽ  ∗ᵒ  Freeᵒ' n o
  ↦ᴸᵒ'-alloc Mo≡ň =  ⊨⤇ᴱᴹᵉᵐ⇒⊨⇛ᵒ (ε↝-◎⟨⟩-⤇ᴱ (↦ᴸʳ-alloc Mo≡ň) ▷
    ⤇ᴱ-respᴱʳ upd˙-mem-envᴳ ▷ ⤇ᴱ-mono λ _ → ◎⟨⟩-∙⇒∗ᵒ)

  -- Free using ↦ᴸᵒ' and Freeᵒ'

  ↦ᴸᵒ'-free :  len ᵗvs ≡ n  →
    o ↦ᴸᵒ' ᵗvs  ∗ᵒ  Freeᵒ' n o  ⊨  ⟨ M ⟩⇛ᵒ⟨ upd˙ o ň M ⟩  ⊤ᵒ₀
  ↦ᴸᵒ'-free lenvs≡n =  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᵒ $ ◎⟨⟩-∗ᵒ⇒∙ ›
    ↝-◎⟨⟩-⤇ᴱ {bⁱ˙ = λ _ → εᴹᵉᵐ} (↦ᴸʳ-free lenvs≡n) › ⤇ᴱ-respᴱʳ upd˙-mem-envᴳ ›
    ⤇ᴱ-mono _

--------------------------------------------------------------------------------
-- Weakest precondition lemmas for the memory
