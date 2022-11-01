--------------------------------------------------------------------------------
-- Interpret the fancy update
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Symp.Model.Fupd.Interp where

open import Base.Level using (Level; _⊔ᴸ_; 1ᴸ; ↑_)
open import Base.Func using (_$_; _▷_; _∘_; _›_; id; const)
open import Base.Few using (⊤₀)
open import Base.Eq using (_≡_; refl; ◠_; refl˙)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_)
open import Base.Nat using ()
open import Symp.Lang.Expr using (Heap; ✓ᴴ_; ✓ᴴ-∅)
open import Symp.Model.ERA.Glob using (Resᴳ; _✓ᴳ_; iᴴᵉᵃᵖ; Envᴵⁿᴳ; envᴳ; ∅ᴵⁿᴳ;
  jᴵⁿᵛ; jᴮᵒʳ; ∅ᴵⁿᴳ-✓[⊤]; envᴳ-cong; upd˙-mem-envᴳ)
open import Symp.Model.Prop.Base using (SPropᵒ; Monoᵒ; _⊨✓_; _⊨_; ⊨_; ⊨⇒⊨✓;
  ∀ᵒ-syntax; ⊤ᵒ₀; ⌜_⌝ᵒ; ⌜_⌝ᵒ×_; _∗ᵒ_; _-∗ᵒ_; ⤇ᵒ_; _⤇ᴱ_; ⤇ᴱ⟨⟩; substᵒ; ∗ᵒ-mono✓ˡ;
  ∗ᵒ-monoˡ; ∗ᵒ-mono✓ʳ; ∗ᵒ-monoʳ; ∗ᵒ-comm; ∗ᵒ-assocˡ; ∗ᵒ-assocʳ; ?∗ᵒ-intro;
  -∗ᵒ-Mono; -∗ᵒ-monoʳ; -∗ᵒ-introˡ; -∗ᵒ-applyˡ; ⤇ᵒ-intro; ⤇ᴱ-respᴱˡ; ⤇ᴱ-respᴱʳ;
  ⤇ᴱ-param; ⤇ᴱ-eatʳ; ⤇ᴱ-step)
open import Symp.Model.Prop.Names using ([⊤]ᴺᵒ)
open import Symp.Model.Fupd.Base using (⟨_⟩[_]⇛ᴳ'⟨_⟩_; ⟨_⟩[_]⇛ᴳ⟨_⟩_; ⇛ᴳ≡⇛ᴳ';
  ⇛ᴳ-Mono; ⇛ᵍ-Mono; ⇛ᴳ-mono✓; ⇛ᴳ-mono; ⇛ᵍ-mono✓; ⇛ᵍ-mono; ⇛ᴳ-make; ⇛ᴳ-apply;
  ⊨✓⇒⊨-⇛ᴳ; ⊨✓⇒⊨-⇛ᵍ; ⇛ᴳ-all; ⇛ᵍ-all; ⤇ᵒ⇒⇛ᴳ; ⇛ᴳ-intro; ⤇ᵒ⇒⇛ᵍ; ⇛ᵍ-intro;
  ⇛ᴳ-intro-✓ᴴ; ⇛ᴳ-join; ⇛ᵍ-join; ⇛ᵍ-join2; ⇛ᴳ-eatˡ; ⇛ᴳ-eatʳ; ⇛ᵍ-eatˡ; ⇛ᵍ-eatʳ;
  ⇛ᴳ-adeq)
open import Symp.Model.Fupd.Ind using (envᴵⁿᵈ; Invᴵⁿᵈ; ⇛ᴵⁿᵈ_; Invᴵⁿᵈ-∅;
  ⇛ᴵⁿᵈ-intro)
open import Symp.Model.Fupd.Inv using (Invᴵⁿᵛ; ⇛ᴵⁿᵛ_; Invᴵⁿᵛ-∅; ⇛ᴵⁿᵛ-intro)
open import Symp.Model.Fupd.Bor using (Invᴮᵒʳ; ⇛ᴮᵒʳ_; Invᴮᵒʳ-∅; ⇛ᴮᵒʳ-intro)

private variable
  ł :  Level
  H H' H'' :  Heap
  Pᵒ Qᵒ :  SPropᵒ ł
  X :  Set ł
  Eᴵⁿ :  Envᴵⁿᴳ
  a :  Resᴳ

--------------------------------------------------------------------------------
-- Interpret the fancy update

infix 3 ⟨_⟩⇛ᴴ'⟨_⟩_ ⟨_⟩⇛ᴴ⟨_⟩_ ⇛ᵒ_ ⇛ᴺᵒ_

-- Invᴳ :  Global invariant

Invᴳ :  Envᴵⁿᴳ →  SPropᵒ 1ᴸ
Invᴳ Eᴵⁿ =  Invᴵⁿᵈ (envᴵⁿᵈ Eᴵⁿ)  ∗ᵒ  Invᴵⁿᵛ (Eᴵⁿ jᴵⁿᵛ)  ∗ᵒ  Invᴮᵒʳ (Eᴵⁿ jᴮᵒʳ)

-- ⇛ᴴ' :  Non-abstract version of ⇛ᴴ

⟨_⟩⇛ᴴ'⟨_⟩_ :  Heap →  Heap →  SPropᵒ ł →  SPropᵒ (1ᴸ ⊔ᴸ ł)
⟨ H ⟩⇛ᴴ'⟨ H' ⟩ Pᵒ =  ⟨ H ⟩[ id , const , Invᴳ ]⇛ᴳ'⟨ H' ⟩ Pᵒ

abstract

  -- ⇛ᴴ :  Semantic fancy update with a heap

  ⟨_⟩⇛ᴴ⟨_⟩_ :  Heap →  Heap →  SPropᵒ ł →  SPropᵒ (1ᴸ ⊔ᴸ ł)
  ⟨ H ⟩⇛ᴴ⟨ H' ⟩ Pᵒ =  ⟨ H ⟩[ id , const , Invᴳ ]⇛ᴳ⟨ H' ⟩ Pᵒ

-- ⇛ᵒ :  Semantic fancy update, i.e., ⇛ᴴ with any fixed heap

⇛ᵒ_ :  SPropᵒ ł →  SPropᵒ (1ᴸ ⊔ᴸ ł)
⇛ᵒ Pᵒ =  ∀ᵒ H , ⟨ H ⟩⇛ᴴ⟨ H ⟩ Pᵒ

-- ⇛ᴺᵒ :  ⇛ᵒ with [⊤]ᴺᵒ

⇛ᴺᵒ_ :  SPropᵒ ł →  SPropᵒ (1ᴸ ⊔ᴸ ł)
⇛ᴺᵒ Pᵒ =  [⊤]ᴺᵒ -∗ᵒ ⇛ᵒ [⊤]ᴺᵒ ∗ᵒ Pᵒ

abstract

  -- Get Invᴳ ∅ᴵⁿᴳ for free

  Invᴳ-∅ :  ⊨ Invᴳ ∅ᴵⁿᴳ
  Invᴳ-∅ =  Invᴮᵒʳ-∅ ▷ ?∗ᵒ-intro Invᴵⁿᵛ-∅ ▷ ?∗ᵒ-intro Invᴵⁿᵈ-∅

  -- ⇛ᴴ equals ⇛ᴴ'

  ⇛ᴴ≡⇛ᴴ' :  (⟨ H ⟩⇛ᴴ⟨ H' ⟩ Pᵒ)  ≡  (⟨ H ⟩⇛ᴴ'⟨ H' ⟩ Pᵒ)
  ⇛ᴴ≡⇛ᴴ' =  ⇛ᴳ≡⇛ᴳ'

  ⇛ᴴ⇒⇛ᴴ' :  ⟨ H ⟩⇛ᴴ⟨ H' ⟩ Pᵒ  ⊨  ⟨ H ⟩⇛ᴴ'⟨ H' ⟩ Pᵒ
  ⇛ᴴ⇒⇛ᴴ' =  substᵒ id ⇛ᴴ≡⇛ᴴ'

  ⇛ᴴ'⇒⇛ᴴ :  ⟨ H ⟩⇛ᴴ'⟨ H' ⟩ Pᵒ  ⊨  ⟨ H ⟩⇛ᴴ⟨ H' ⟩ Pᵒ
  ⇛ᴴ'⇒⇛ᴴ =  substᵒ id $ ◠ ⇛ᴴ≡⇛ᴴ'

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

  -- ⤇ᴱ⟨⟩ on iᴴᵉᵃᵖ into ⇛ᴴ

  ?⊨⤇ᴱᴴᵉᵃᵖ⇒?⊨⇛ᴴ :  Pᵒ  ⊨ ↑ H ⤇ᴱ⟨ iᴴᵉᵃᵖ ⟩ (λ (_ : ⊤₀) → ↑ H' ,  Qᵒ)  →
                  Pᵒ  ⊨ ⟨ H ⟩⇛ᴴ⟨ H' ⟩  Qᵒ
  ?⊨⤇ᴱᴴᵉᵃᵖ⇒?⊨⇛ᴴ {H = H} P⊨H⤇H'Q =  ⇛ᴳ-make $ ∗ᵒ-monoˡ (P⊨H⤇H'Q › _$ _) ›
    ⤇ᴱ-eatʳ › ⤇ᴱ-respᴱˡ (upd˙-mem-envᴳ {H = H}) › ⤇ᴱ-respᴱʳ upd˙-mem-envᴳ ›
    ⤇ᴱ-param

  ⊨⤇ᴱᴴᵉᵃᵖ⇒⊨⇛ᴴ :  ⊨ ↑ H ⤇ᴱ⟨ iᴴᵉᵃᵖ ⟩ (λ (_ : ⊤₀) → ↑ H' ,  Pᵒ)  →
                ⊨  ⟨ H ⟩⇛ᴴ⟨ H' ⟩ Pᵒ
  ⊨⤇ᴱᴴᵉᵃᵖ⇒⊨⇛ᴴ ⊨H⤇H'P =  ?⊨⤇ᴱᴴᵉᵃᵖ⇒?⊨⇛ᴴ {Pᵒ = ⊤ᵒ₀} (λ _ → ⊨H⤇H'P) _

  -- Monoᵒ for ⇛ᴴ/⇛ᵒ

  ⇛ᴴ-Mono :  Monoᵒ $ ⟨ H ⟩⇛ᴴ⟨ H' ⟩ Pᵒ
  ⇛ᴴ-Mono =  ⇛ᴳ-Mono

  ⇛ᵒ-Mono :  Monoᵒ $ ⇛ᵒ Pᵒ
  ⇛ᵒ-Mono =  ⇛ᵍ-Mono

  -- Monotonicity of ⇛ᴴ/⇛ᵒ

  ⇛ᴴ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  ⟨ H ⟩⇛ᴴ⟨ H' ⟩ Pᵒ  ⊨  ⟨ H ⟩⇛ᴴ⟨ H' ⟩ Qᵒ
  ⇛ᴴ-mono✓ =  ⇛ᴳ-mono✓

  ⇛ᴴ-mono :  Pᵒ ⊨ Qᵒ →  ⟨ H ⟩⇛ᴴ⟨ H' ⟩ Pᵒ  ⊨  ⟨ H ⟩⇛ᴴ⟨ H' ⟩ Qᵒ
  ⇛ᴴ-mono =  ⇛ᴳ-mono

  ⇛ᵒ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  ⇛ᵒ Pᵒ ⊨ ⇛ᵒ Qᵒ
  ⇛ᵒ-mono✓ =  ⇛ᵍ-mono✓

  ⇛ᵒ-mono :  Pᵒ ⊨ Qᵒ →  ⇛ᵒ Pᵒ ⊨ ⇛ᵒ Qᵒ
  ⇛ᵒ-mono =  ⇛ᵍ-mono

  -- ⊨✓ ⇛ᴴ/⇛ᵒ into ⊨ ⇛ᴴ/⇛ᵒ

  ⊨✓⇒⊨-⇛ᴴ :  Pᵒ ⊨✓ ⟨ H ⟩⇛ᴴ⟨ H' ⟩ Qᵒ →  Pᵒ ⊨ ⟨ H ⟩⇛ᴴ⟨ H' ⟩ Qᵒ
  ⊨✓⇒⊨-⇛ᴴ =  ⊨✓⇒⊨-⇛ᴳ

  ⊨✓⇒⊨-⇛ᵒ :  Pᵒ ⊨✓ ⇛ᵒ Qᵒ →  Pᵒ ⊨ ⇛ᵒ Qᵒ
  ⊨✓⇒⊨-⇛ᵒ =  ⊨✓⇒⊨-⇛ᵍ

  -- Introduce ⇛ᴴ/⇛ᵒ

  ⤇ᵒ⇒⇛ᴴ :  ⤇ᵒ Pᵒ  ⊨ ⟨ H ⟩⇛ᴴ⟨ H ⟩  Pᵒ
  ⤇ᵒ⇒⇛ᴴ =  ⤇ᵒ⇒⇛ᴳ refl˙

  ⇛ᴴ-intro :  Pᵒ  ⊨ ⟨ H ⟩⇛ᴴ⟨ H ⟩  Pᵒ
  ⇛ᴴ-intro =  ⇛ᴳ-intro refl˙

  ⤇ᵒ⇒⇛ᵒ :  ⤇ᵒ Pᵒ  ⊨ ⇛ᵒ  Pᵒ
  ⤇ᵒ⇒⇛ᵒ =  ⤇ᵒ⇒⇛ᵍ refl˙

  ⇛ᵒ-intro :  Pᵒ  ⊨ ⇛ᵒ  Pᵒ
  ⇛ᵒ-intro =  ⇛ᵍ-intro refl˙

  -- Introduce ⇛ᴴ with ✓ᴴ

  ⇛ᴴ-intro-✓ᴴ :  Pᵒ  ⊨ ⟨ H ⟩⇛ᴴ⟨ H ⟩  ⌜ ✓ᴴ H ⌝ᵒ×  Pᵒ
  ⇛ᴴ-intro-✓ᴴ =  ⇛ᴳ-intro-✓ᴴ refl˙

  -- Join ⇛ᴴ/⇛ᵒ

  ⇛ᴴ-join :  ⟨ H ⟩⇛ᴴ⟨ H' ⟩ ⟨ H' ⟩⇛ᴴ⟨ H'' ⟩ Pᵒ  ⊨ ⟨ H ⟩⇛ᴴ⟨ H'' ⟩  Pᵒ
  ⇛ᴴ-join =  ⇛ᴳ-join refl refl˙

  ⇛ᵒ-join :  ⇛ᵒ ⇛ᵒ Pᵒ  ⊨  ⇛ᵒ Pᵒ
  ⇛ᵒ-join =  ⇛ᵍ-join refl refl˙

  -- Let ⇛ᴴ/⇛ᵒ eat a proposition under ∗ᵒ

  ⇛ᴴ-eatˡ :  Qᵒ ∗ᵒ (⟨ H ⟩⇛ᴴ⟨ H' ⟩ Pᵒ)  ⊨ ⟨ H ⟩⇛ᴴ⟨ H' ⟩  Qᵒ ∗ᵒ Pᵒ
  ⇛ᴴ-eatˡ =  ⇛ᴳ-eatˡ

  ⇛ᴴ-eatʳ :  (⟨ H ⟩⇛ᴴ⟨ H' ⟩ Pᵒ) ∗ᵒ Qᵒ  ⊨ ⟨ H ⟩⇛ᴴ⟨ H' ⟩  Pᵒ ∗ᵒ Qᵒ
  ⇛ᴴ-eatʳ =  ⇛ᴳ-eatʳ

  ⇛ᵒ-eatˡ :  Qᵒ ∗ᵒ (⇛ᵒ Pᵒ)  ⊨ ⇛ᵒ  Qᵒ ∗ᵒ Pᵒ
  ⇛ᵒ-eatˡ =  ⇛ᵍ-eatˡ

  ⇛ᵒ-eatʳ :  (⇛ᵒ Pᵒ) ∗ᵒ Qᵒ  ⊨ ⇛ᵒ  Pᵒ ∗ᵒ Qᵒ
  ⇛ᵒ-eatʳ =  ⇛ᵍ-eatʳ

  -- Adequacy of ⇛ᴴ
  -- If we have X under [⊤]ᴺᵒ and ⟨ H ⟩⇛ᴴ⟨ _ ⟩ for valid H, then X holds purely

  ⇛ᴴ-adeq :  ✓ᴴ H →  [⊤]ᴺᵒ ⊨ ⟨ H ⟩⇛ᴴ⟨ H' ⟩ ⌜ X ⌝ᵒ →  X
  ⇛ᴴ-adeq =  ⇛ᴳ-adeq Invᴳ-∅

  -- Adequacy of ⇛ᵒ

  ⇛ᵒ-adeq :  [⊤]ᴺᵒ ⊨ ⇛ᵒ ⌜ X ⌝ᵒ →  X
  ⇛ᵒ-adeq [⊤]⊨X =  ⇛ᴴ-adeq ✓ᴴ-∅ $ [⊤]⊨X › _$ _

  -- Perform a step by ⇛ᴴ

  ⇛ᴴ-step :  envᴳ H Eᴵⁿ ✓ᴳ a  →  ((⟨ H ⟩⇛ᴴ⟨ H' ⟩ Pᵒ) ∗ᵒ Invᴳ Eᴵⁿ) a  →
             ∑ Fᴵⁿ , ∑ b ,  envᴳ H' Fᴵⁿ ✓ᴳ b  ×  (Pᵒ ∗ᵒ Invᴳ Fᴵⁿ) b
  ⇛ᴴ-step HE✓a ⇛P∗InvEa  with ⤇ᴱ-step HE✓a (⇛ᴳ-apply ⇛P∗InvEa)
  … | -, -, H'F✓b , P∗InvFb =  -, -, H'F✓b , P∗InvFb

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
