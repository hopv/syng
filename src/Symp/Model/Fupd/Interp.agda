--------------------------------------------------------------------------------
-- Interpret the fancy update
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Fupd.Interp where

open import Base.Level using (Level; _⊔ᴸ_; 1ᴸ; ↑_)
open import Base.Func using (_$_; _▷_; _∘_; _›_; id; const)
open import Base.Few using (⊤₀)
open import Base.Eq using (_≡_; refl; ◠_; refl˙)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_)
open import Base.Nat using ()
open import Syho.Lang.Expr using (Mem; ✓ᴹ_; ✓ᴹ-∅)
open import Syho.Model.ERA.Glob using (Resᴳ; _✓ᴳ_; iᴹᵉᵐ; Envᴵⁿᴳ; envᴳ; ∅ᴵⁿᴳ;
  jᴵⁿᵛ; jᴮᵒʳ; ∅ᴵⁿᴳ-✓[⊤]; envᴳ-cong; upd˙-mem-envᴳ)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; ⊨_; ⊨⇒⊨✓;
  ∀ᵒ-syntax; ⊤ᵒ₀; ⌜_⌝ᵒ; ⌜_⌝ᵒ×_; _∗ᵒ_; _-∗ᵒ_; ⤇ᵒ_; _⤇ᴱ_; ⤇ᴱ⟨⟩; substᵒ; ∗ᵒ-mono✓ˡ;
  ∗ᵒ-monoˡ; ∗ᵒ-mono✓ʳ; ∗ᵒ-monoʳ; ∗ᵒ-comm; ∗ᵒ-assocˡ; ∗ᵒ-assocʳ; ?∗ᵒ-intro;
  -∗ᵒ-Mono; -∗ᵒ-monoʳ; -∗ᵒ-introˡ; -∗ᵒ-applyˡ; ⤇ᵒ-intro; ⤇ᴱ-respᴱˡ; ⤇ᴱ-respᴱʳ;
  ⤇ᴱ-param; ⤇ᴱ-eatʳ; ⤇ᴱ-step)
open import Syho.Model.Prop.Names using ([⊤]ᴺᵒ)
open import Syho.Model.Fupd.Base using (⟨_⟩[_]⇛ᴳ'⟨_⟩_; ⟨_⟩[_]⇛ᴳ⟨_⟩_; ⇛ᴳ≡⇛ᴳ';
  ⇛ᴳ-Mono; ⇛ᵍ-Mono; ⇛ᴳ-mono✓; ⇛ᴳ-mono; ⇛ᵍ-mono✓; ⇛ᵍ-mono; ⇛ᴳ-make; ⇛ᴳ-apply;
  ⊨✓⇒⊨-⇛ᴳ; ⊨✓⇒⊨-⇛ᵍ; ⇛ᴳ-all; ⇛ᵍ-all; ⤇ᵒ⇒⇛ᴳ; ⇛ᴳ-intro; ⤇ᵒ⇒⇛ᵍ; ⇛ᵍ-intro;
  ⇛ᴳ-intro-✓ᴹ; ⇛ᴳ-join; ⇛ᵍ-join; ⇛ᵍ-join2; ⇛ᴳ-eatˡ; ⇛ᴳ-eatʳ; ⇛ᵍ-eatˡ; ⇛ᵍ-eatʳ;
  ⇛ᴳ-adeq)
open import Syho.Model.Fupd.Ind using (envᴵⁿᵈ; Invᴵⁿᵈ; ⇛ᴵⁿᵈ_; Invᴵⁿᵈ-∅;
  ⇛ᴵⁿᵈ-intro)
open import Syho.Model.Fupd.Inv using (Invᴵⁿᵛ; ⇛ᴵⁿᵛ_; Invᴵⁿᵛ-∅; ⇛ᴵⁿᵛ-intro)
open import Syho.Model.Fupd.Bor using (Invᴮᵒʳ; ⇛ᴮᵒʳ_; Invᴮᵒʳ-∅; ⇛ᴮᵒʳ-intro)

private variable
  ł :  Level
  M M' M'' :  Mem
  Pᵒ Qᵒ :  Propᵒ ł
  X :  Set ł
  Eᴵⁿ :  Envᴵⁿᴳ
  a :  Resᴳ

--------------------------------------------------------------------------------
-- Interpret the fancy update

infix 3 ⟨_⟩⇛ᴹ'⟨_⟩_ ⟨_⟩⇛ᴹ⟨_⟩_ ⇛ᵒ_ ⇛ᴺᵒ_

-- Invᴳ :  Global invariant

Invᴳ :  Envᴵⁿᴳ →  Propᵒ 1ᴸ
Invᴳ Eᴵⁿ =  Invᴵⁿᵈ (envᴵⁿᵈ Eᴵⁿ)  ∗ᵒ  Invᴵⁿᵛ (Eᴵⁿ jᴵⁿᵛ)  ∗ᵒ  Invᴮᵒʳ (Eᴵⁿ jᴮᵒʳ)

-- ⇛ᴹ' :  Non-abstract version of ⇛ᴹ

⟨_⟩⇛ᴹ'⟨_⟩_ :  Mem →  Mem →  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⟨ M ⟩⇛ᴹ'⟨ M' ⟩ Pᵒ =  ⟨ M ⟩[ id , const , Invᴳ ]⇛ᴳ'⟨ M' ⟩ Pᵒ

abstract

  -- ⇛ᴹ :  Semantic fancy update with a memory

  ⟨_⟩⇛ᴹ⟨_⟩_ :  Mem →  Mem →  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ =  ⟨ M ⟩[ id , const , Invᴳ ]⇛ᴳ⟨ M' ⟩ Pᵒ

-- ⇛ᵒ :  Semantic fancy update, i.e., ⇛ᴹ with any fixed memory

⇛ᵒ_ :  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⇛ᵒ Pᵒ =  ∀ᵒ M , ⟨ M ⟩⇛ᴹ⟨ M ⟩ Pᵒ

-- ⇛ᴺᵒ :  ⇛ᵒ with [⊤]ᴺᵒ

⇛ᴺᵒ_ :  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⇛ᴺᵒ Pᵒ =  [⊤]ᴺᵒ -∗ᵒ ⇛ᵒ [⊤]ᴺᵒ ∗ᵒ Pᵒ

abstract

  -- Get Invᴳ ∅ᴵⁿᴳ for free

  Invᴳ-∅ :  ⊨ Invᴳ ∅ᴵⁿᴳ
  Invᴳ-∅ =  Invᴮᵒʳ-∅ ▷ ?∗ᵒ-intro Invᴵⁿᵛ-∅ ▷ ?∗ᵒ-intro Invᴵⁿᵈ-∅

  -- ⇛ᴹ equals ⇛ᴹ'

  ⇛ᴹ≡⇛ᴹ' :  (⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ)  ≡  (⟨ M ⟩⇛ᴹ'⟨ M' ⟩ Pᵒ)
  ⇛ᴹ≡⇛ᴹ' =  ⇛ᴳ≡⇛ᴳ'

  ⇛ᴹ⇒⇛ᴹ' :  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᴹ'⟨ M' ⟩ Pᵒ
  ⇛ᴹ⇒⇛ᴹ' =  substᵒ id ⇛ᴹ≡⇛ᴹ'

  ⇛ᴹ'⇒⇛ᴹ :  ⟨ M ⟩⇛ᴹ'⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ
  ⇛ᴹ'⇒⇛ᴹ =  substᵒ id $ ◠ ⇛ᴹ≡⇛ᴹ'

  -- ⇛ᴵⁿᵈ into ⇛ᵒ

  ⇛ᴵⁿᵈ⇒⇛ᵒ :  ⇛ᴵⁿᵈ Pᵒ  ⊨  ⇛ᵒ Pᵒ
  ⇛ᴵⁿᵈ⇒⇛ᵒ =  ⇛ᵍ-mono (⇛ᴮᵒʳ-intro › ⇛ᴵⁿᵛ-intro › ⇛ᵍ-join2 refl) ›
    ⇛ᵍ-join2 refl › ⇛ᵍ-all refl

  -- ⇛ᴵⁿᵛ into ⇛ᵒ

  ⇛ᴵⁿᵛ⇒⇛ᵒ :  ⇛ᴵⁿᵛ Pᵒ  ⊨  ⇛ᵒ Pᵒ
  ⇛ᴵⁿᵛ⇒⇛ᵒ =  ⇛ᵍ-mono ⇛ᴮᵒʳ-intro ›
    ⇛ᵍ-join2 refl › ⇛ᴵⁿᵈ-intro › ⇛ᵍ-join2 refl › ⇛ᵍ-all refl

  -- ⇛ᴮᵒʳ into ⇛ᵒ

  ⇛ᴮᵒʳ⇒⇛ᵒ :  ⇛ᴮᵒʳ Pᵒ  ⊨  ⇛ᵒ Pᵒ
  ⇛ᴮᵒʳ⇒⇛ᵒ =  ⇛ᴵⁿᵛ-intro ›
    ⇛ᵍ-join2 refl › ⇛ᴵⁿᵈ-intro › ⇛ᵍ-join2 refl › ⇛ᵍ-all refl

  -- ⤇ᴱ⟨⟩ on iᴹᵉᵐ into ⇛ᴹ

  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᴹ :  Pᵒ  ⊨ ↑ M ⤇ᴱ⟨ iᴹᵉᵐ ⟩ (λ (_ : ⊤₀) → ↑ M' ,  Qᵒ)  →
                  Pᵒ  ⊨ ⟨ M ⟩⇛ᴹ⟨ M' ⟩  Qᵒ
  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᴹ {M = M} P⊨M⤇M'Q =  ⇛ᴳ-make $ ∗ᵒ-monoˡ (P⊨M⤇M'Q › _$ _) ›
    ⤇ᴱ-eatʳ › ⤇ᴱ-respᴱˡ (upd˙-mem-envᴳ {M = M}) › ⤇ᴱ-respᴱʳ upd˙-mem-envᴳ ›
    ⤇ᴱ-param

  ⊨⤇ᴱᴹᵉᵐ⇒⊨⇛ᴹ :  ⊨ ↑ M ⤇ᴱ⟨ iᴹᵉᵐ ⟩ (λ (_ : ⊤₀) → ↑ M' ,  Pᵒ)  →
                ⊨  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ
  ⊨⤇ᴱᴹᵉᵐ⇒⊨⇛ᴹ ⊨M⤇M'P =  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᴹ {Pᵒ = ⊤ᵒ₀} (λ _ → ⊨M⤇M'P) _

  -- Monoᵒ for ⇛ᴹ/⇛ᵒ

  ⇛ᴹ-Mono :  Monoᵒ $ ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ
  ⇛ᴹ-Mono =  ⇛ᴳ-Mono

  ⇛ᵒ-Mono :  Monoᵒ $ ⇛ᵒ Pᵒ
  ⇛ᵒ-Mono =  ⇛ᵍ-Mono

  -- Monotonicity of ⇛ᴹ/⇛ᵒ

  ⇛ᴹ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Qᵒ
  ⇛ᴹ-mono✓ =  ⇛ᴳ-mono✓

  ⇛ᴹ-mono :  Pᵒ ⊨ Qᵒ →  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Qᵒ
  ⇛ᴹ-mono =  ⇛ᴳ-mono

  ⇛ᵒ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  ⇛ᵒ Pᵒ ⊨ ⇛ᵒ Qᵒ
  ⇛ᵒ-mono✓ =  ⇛ᵍ-mono✓

  ⇛ᵒ-mono :  Pᵒ ⊨ Qᵒ →  ⇛ᵒ Pᵒ ⊨ ⇛ᵒ Qᵒ
  ⇛ᵒ-mono =  ⇛ᵍ-mono

  -- ⊨✓ ⇛ᴹ/⇛ᵒ into ⊨ ⇛ᴹ/⇛ᵒ

  ⊨✓⇒⊨-⇛ᴹ :  Pᵒ ⊨✓ ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Qᵒ →  Pᵒ ⊨ ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Qᵒ
  ⊨✓⇒⊨-⇛ᴹ =  ⊨✓⇒⊨-⇛ᴳ

  ⊨✓⇒⊨-⇛ᵒ :  Pᵒ ⊨✓ ⇛ᵒ Qᵒ →  Pᵒ ⊨ ⇛ᵒ Qᵒ
  ⊨✓⇒⊨-⇛ᵒ =  ⊨✓⇒⊨-⇛ᵍ

  -- Introduce ⇛ᴹ/⇛ᵒ

  ⤇ᵒ⇒⇛ᴹ :  ⤇ᵒ Pᵒ  ⊨ ⟨ M ⟩⇛ᴹ⟨ M ⟩  Pᵒ
  ⤇ᵒ⇒⇛ᴹ =  ⤇ᵒ⇒⇛ᴳ refl˙

  ⇛ᴹ-intro :  Pᵒ  ⊨ ⟨ M ⟩⇛ᴹ⟨ M ⟩  Pᵒ
  ⇛ᴹ-intro =  ⇛ᴳ-intro refl˙

  ⤇ᵒ⇒⇛ᵒ :  ⤇ᵒ Pᵒ  ⊨ ⇛ᵒ  Pᵒ
  ⤇ᵒ⇒⇛ᵒ =  ⤇ᵒ⇒⇛ᵍ refl˙

  ⇛ᵒ-intro :  Pᵒ  ⊨ ⇛ᵒ  Pᵒ
  ⇛ᵒ-intro =  ⇛ᵍ-intro refl˙

  -- Introduce ⇛ᴹ with ✓ᴹ

  ⇛ᴹ-intro-✓ᴹ :  Pᵒ  ⊨ ⟨ M ⟩⇛ᴹ⟨ M ⟩  ⌜ ✓ᴹ M ⌝ᵒ×  Pᵒ
  ⇛ᴹ-intro-✓ᴹ =  ⇛ᴳ-intro-✓ᴹ refl˙

  -- Join ⇛ᴹ/⇛ᵒ

  ⇛ᴹ-join :  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ ⟨ M' ⟩⇛ᴹ⟨ M'' ⟩ Pᵒ  ⊨ ⟨ M ⟩⇛ᴹ⟨ M'' ⟩  Pᵒ
  ⇛ᴹ-join =  ⇛ᴳ-join refl refl˙

  ⇛ᵒ-join :  ⇛ᵒ ⇛ᵒ Pᵒ  ⊨  ⇛ᵒ Pᵒ
  ⇛ᵒ-join =  ⇛ᵍ-join refl refl˙

  -- Let ⇛ᴹ/⇛ᵒ eat a proposition under ∗ᵒ

  ⇛ᴹ-eatˡ :  Qᵒ ∗ᵒ (⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ)  ⊨ ⟨ M ⟩⇛ᴹ⟨ M' ⟩  Qᵒ ∗ᵒ Pᵒ
  ⇛ᴹ-eatˡ =  ⇛ᴳ-eatˡ

  ⇛ᴹ-eatʳ :  (⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ) ∗ᵒ Qᵒ  ⊨ ⟨ M ⟩⇛ᴹ⟨ M' ⟩  Pᵒ ∗ᵒ Qᵒ
  ⇛ᴹ-eatʳ =  ⇛ᴳ-eatʳ

  ⇛ᵒ-eatˡ :  Qᵒ ∗ᵒ (⇛ᵒ Pᵒ)  ⊨ ⇛ᵒ  Qᵒ ∗ᵒ Pᵒ
  ⇛ᵒ-eatˡ =  ⇛ᵍ-eatˡ

  ⇛ᵒ-eatʳ :  (⇛ᵒ Pᵒ) ∗ᵒ Qᵒ  ⊨ ⇛ᵒ  Pᵒ ∗ᵒ Qᵒ
  ⇛ᵒ-eatʳ =  ⇛ᵍ-eatʳ

  -- Adequacy of ⇛ᴹ
  -- If we have X under [⊤]ᴺᵒ and ⟨ M ⟩⇛ᴹ⟨ _ ⟩ for valid M, then X holds purely

  ⇛ᴹ-adeq :  ✓ᴹ M →  [⊤]ᴺᵒ ⊨ ⟨ M ⟩⇛ᴹ⟨ M' ⟩ ⌜ X ⌝ᵒ →  X
  ⇛ᴹ-adeq =  ⇛ᴳ-adeq Invᴳ-∅

  -- Adequacy of ⇛ᵒ

  ⇛ᵒ-adeq :  [⊤]ᴺᵒ ⊨ ⇛ᵒ ⌜ X ⌝ᵒ →  X
  ⇛ᵒ-adeq [⊤]⊨X =  ⇛ᴹ-adeq ✓ᴹ-∅ $ [⊤]⊨X › _$ _

  -- Perform a step by ⇛ᴹ

  ⇛ᴹ-step :  envᴳ M Eᴵⁿ ✓ᴳ a  →  ((⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ) ∗ᵒ Invᴳ Eᴵⁿ) a  →
             ∑ Fᴵⁿ , ∑ b ,  envᴳ M' Fᴵⁿ ✓ᴳ b  ×  (Pᵒ ∗ᵒ Invᴳ Fᴵⁿ) b
  ⇛ᴹ-step ME✓a ⇛P∗InvEa  with ⤇ᴱ-step ME✓a (⇛ᴳ-apply ⇛P∗InvEa)
  … | -, -, M'F✓b , P∗InvFb =  -, -, M'F✓b , P∗InvFb

  -- ⇛ᵒ into ⇛ᴺᵒ

  ⇛ᵒ⇒⇛ᴺᵒ :  ⇛ᵒ Pᵒ ⊨ ⇛ᴺᵒ Pᵒ
  ⇛ᵒ⇒⇛ᴺᵒ =  -∗ᵒ-introˡ λ _ → ⇛ᵒ-eatˡ

  -- Monoᵒ for ⇛ᴺᵒ

  ⇛ᴺᵒ-Mono :  Monoᵒ $ ⇛ᴺᵒ Pᵒ
  ⇛ᴺᵒ-Mono =  -∗ᵒ-Mono

  -- Monotonicity of ⇛ᴺᵒ

  ⇛ᴺᵒ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  ⇛ᴺᵒ Pᵒ ⊨ ⇛ᴺᵒ Qᵒ
  ⇛ᴺᵒ-mono✓ P⊨✓Q =  -∗ᵒ-introˡ λ ✓∙ →
    -∗ᵒ-applyˡ ⇛ᵒ-Mono ✓∙ › ⇛ᵒ-mono✓ $ ∗ᵒ-mono✓ʳ P⊨✓Q

  ⇛ᴺᵒ-mono :  Pᵒ ⊨ Qᵒ →  ⇛ᴺᵒ Pᵒ ⊨ ⇛ᴺᵒ Qᵒ
  ⇛ᴺᵒ-mono =  ⇛ᴺᵒ-mono✓ ∘ ⊨⇒⊨✓

  -- Introduce ⇛ᴺᵒ

  ⤇ᵒ⇒⇛ᴺᵒ :  ⤇ᵒ Pᵒ  ⊨ ⇛ᴺᵒ  Pᵒ
  ⤇ᵒ⇒⇛ᴺᵒ =  -∗ᵒ-introˡ λ _ → ∗ᵒ-monoʳ ⤇ᵒ⇒⇛ᵒ › ⇛ᵒ-eatˡ

  ⇛ᴺᵒ-intro :  Pᵒ  ⊨ ⇛ᴺᵒ  Pᵒ
  ⇛ᴺᵒ-intro =  ⤇ᵒ-intro › ⤇ᵒ⇒⇛ᴺᵒ

  -- Join ⇛ᴺᵒ

  ⇛ᴺᵒ-join :  ⇛ᴺᵒ ⇛ᴺᵒ Pᵒ  ⊨ ⇛ᴺᵒ Pᵒ
  ⇛ᴺᵒ-join =  -∗ᵒ-monoʳ $ ⇛ᵒ-mono✓ (λ ✓∙ → -∗ᵒ-applyˡ ⇛ᵒ-Mono ✓∙) › ⇛ᵒ-join

  -- Let ⇛ᴺᵒ eat a proposition under ∗ᵒ

  ⇛ᴺᵒ-eatʳ :  (⇛ᴺᵒ Pᵒ) ∗ᵒ Qᵒ  ⊨ ⇛ᴺᵒ  Pᵒ ∗ᵒ Qᵒ
  ⇛ᴺᵒ-eatʳ =  -∗ᵒ-introˡ λ ✓∙ → ∗ᵒ-assocˡ › ∗ᵒ-mono✓ˡ (-∗ᵒ-applyˡ ⇛ᵒ-Mono) ✓∙ ›
    ⇛ᵒ-eatʳ › ⇛ᵒ-mono ∗ᵒ-assocʳ

  ⇛ᴺᵒ-eatˡ :  Pᵒ ∗ᵒ (⇛ᴺᵒ Qᵒ)  ⊨ ⇛ᴺᵒ  Pᵒ ∗ᵒ Qᵒ
  ⇛ᴺᵒ-eatˡ =  ∗ᵒ-comm › ⇛ᴺᵒ-eatʳ › ⇛ᴺᵒ-mono ∗ᵒ-comm
