--------------------------------------------------------------------------------
-- Interpret the super update
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Interp where

open import Base.Level using (Level; _⊔ᴸ_; 1ᴸ)
open import Base.Func using (_$_; _▷_; _›_; id; const)
open import Base.Few using (⊤₀)
open import Base.Eq using (_≡_; refl; ◠_; refl˙)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_)
open import Base.Nat using ()
open import Syho.Lang.Reduce using (Mem; ✓ᴹ_)
open import Syho.Model.ERA.Glob using (Resᴳ; _✓ᴳ_; jᴵⁿᵛ; Envᴵⁿᴳ; envᴳ; empᴵⁿᴳ;
  empᴵⁿᴳ-✓; envᴳ-cong)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; ⊨_; ∀ᵒ-syntax;
  ⊤ᵒ₀; ⌜_⌝ᵒ; ⌜_⌝ᵒ×_; _∗ᵒ_; ⤇ᵒ_; _⤇ᴱ_; substᵒ; ∗ᵒ-monoˡ; ∗ᵒ?-intro; ⤇ᴱ-param;
  ⤇ᴱ-eatʳ; ⤇ᴱ-step)
open import Syho.Model.Supd.Base using (⟨_⟩[_]⇛ᵍ'⟨_⟩_; ⟨_⟩[_]⇛ᵍ⟨_⟩_; ⇛ᵍ≡⇛ᵍ';
  ⇛ᵍ-Mono; ⇛ᵍᶠ-Mono; ⇛ᵍ-mono✓; ⇛ᵍ-mono; ⇛ᵍᶠ-mono✓; ⇛ᵍᶠ-mono; ⇛ᵍ-make; ⇛ᵍ-apply;
  ⊨✓⇒⊨-⇛ᵍ; ⊨✓⇒⊨-⇛ᵍᶠ; ⇛ᵍ-all; ⇛ᵍᶠ-all; ⤇ᵒ⇒⇛ᵍ; ⇛ᵍ-intro; ⤇ᵒ⇒⇛ᵍᶠ; ⇛ᵍᶠ-intro;
  ⇛ᵍ-intro-✓ᴹ; ⇛ᵍ-join; ⇛ᵍᶠ-join; ⇛ᵍᶠ-join2; ⇛ᵍ-eatˡ; ⇛ᵍ-eatʳ; ⇛ᵍᶠ-eatˡ;
  ⇛ᵍᶠ-eatʳ; ⇛ᵍ-adeq)
open import Syho.Model.Supd.Ind using (envᴵⁿᵈ; Invᴵⁿᵈ; ⇛ᴵⁿᵈ_; Invᴵⁿᵈ-emp;
  ⇛ᴵⁿᵈ-intro)
open import Syho.Model.Supd.Inv using (Invᴵⁿᵛ; ⇛ᴵⁿᵛ_; Invᴵⁿᵛ-emp; ⇛ᴵⁿᵛ-intro)

private variable
  ł :  Level
  M M' M'' :  Mem
  Pᵒ Qᵒ :  Propᵒ ł
  X :  Set ł
  Eᴵⁿ :  Envᴵⁿᴳ
  a :  Resᴳ

--------------------------------------------------------------------------------
-- Interpret the super update

infix 3 ⟨_⟩⇛ᵒ'⟨_⟩_ ⟨_⟩⇛ᵒ⟨_⟩_ ⇛ᵒᶠ_

-- Invᴳ :  Global invariant

Invᴳ :  Envᴵⁿᴳ →  Propᵒ 1ᴸ
Invᴳ Eᴵⁿ =  Invᴵⁿᵈ (envᴵⁿᵈ Eᴵⁿ)  ∗ᵒ  Invᴵⁿᵛ (Eᴵⁿ jᴵⁿᵛ)

-- ⇛ᵒ' :  Non-abstract version of ⇛ᵒ

⟨_⟩⇛ᵒ'⟨_⟩_ :  Mem →  Mem →  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⟨ M ⟩⇛ᵒ'⟨ M' ⟩ Pᵒ =  ⟨ M ⟩[ id , const , Invᴳ ]⇛ᵍ'⟨ M' ⟩ Pᵒ

abstract

  -- ⇛ᵒ :  Interpret the super update

  ⟨_⟩⇛ᵒ⟨_⟩_ :  Mem →  Mem →  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ =  ⟨ M ⟩[ id , const , Invᴳ ]⇛ᵍ⟨ M' ⟩ Pᵒ

-- ⇛ᵒᶠ :  ⇛ᵒ with any fixed memory

⇛ᵒᶠ_ :  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⇛ᵒᶠ Pᵒ =  ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ

abstract

  -- Get Invᴳ empᴵⁿᴳ for free

  Invᴳ-emp :  ⊨ Invᴳ empᴵⁿᴳ
  Invᴳ-emp =  Invᴵⁿᵈ-emp ▷ ∗ᵒ?-intro Invᴵⁿᵛ-emp

  -- ⇛ᵒ equals ⇛ᵒ'

  ⇛ᵒ≡⇛ᵒ' :  (⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ)  ≡  (⟨ M ⟩⇛ᵒ'⟨ M' ⟩ Pᵒ)
  ⇛ᵒ≡⇛ᵒ' =  ⇛ᵍ≡⇛ᵍ'

  ⇛ᵒ⇒⇛ᵒ' :  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ'⟨ M' ⟩ Pᵒ
  ⇛ᵒ⇒⇛ᵒ' =  substᵒ id ⇛ᵒ≡⇛ᵒ'

  ⇛ᵒ'⇒⇛ᵒ :  ⟨ M ⟩⇛ᵒ'⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ
  ⇛ᵒ'⇒⇛ᵒ =  substᵒ id $ ◠ ⇛ᵒ≡⇛ᵒ'

  -- ⇛ᴵⁿᵈ into ⇛ᵒᶠ

  ⇛ᴵⁿᵈ⇒⇛ᵒᶠ :  ⇛ᴵⁿᵈ Pᵒ  ⊨  ⇛ᵒᶠ Pᵒ
  ⇛ᴵⁿᵈ⇒⇛ᵒᶠ =  ⇛ᵍᶠ-mono ⇛ᴵⁿᵛ-intro › ⇛ᵍᶠ-join2 refl › ⇛ᵍᶠ-all refl

  -- ⇛ᴵⁿᵛ into ⇛ᵒᶠ

  ⇛ᴵⁿᵛ⇒⇛ᵒᶠ :  ⇛ᴵⁿᵛ Pᵒ  ⊨  ⇛ᵒᶠ Pᵒ
  ⇛ᴵⁿᵛ⇒⇛ᵒᶠ =  ⇛ᴵⁿᵈ-intro › ⇛ᵍᶠ-join2 refl › ⇛ᵍᶠ-all refl

  -- ⤇ᴱ on the memory into ⇛ᵒ

  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᵒ :
    (∀{Eᴵⁿ} →  Pᵒ ⊨ envᴳ M Eᴵⁿ ⤇ᴱ λ (_ : ⊤₀) → envᴳ M' Eᴵⁿ , Qᵒ)  →
    Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Qᵒ
  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᵒ P⊨ME⤇M'EQ =  ⇛ᵍ-make $ ∗ᵒ-monoˡ P⊨ME⤇M'EQ › ⤇ᴱ-eatʳ › ⤇ᴱ-param

  ⊨⤇ᴱᴹᵉᵐ⇒⊨⇛ᵒ :  (∀{Eᴵⁿ} →  ⊨ envᴳ M Eᴵⁿ ⤇ᴱ λ (_ : ⊤₀) → envᴳ M' Eᴵⁿ , Pᵒ)  →
                ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ
  ⊨⤇ᴱᴹᵉᵐ⇒⊨⇛ᵒ ⊨ME⤇M'EP =  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᵒ {Pᵒ = ⊤ᵒ₀} (λ _ → ⊨ME⤇M'EP) _

  -- Monoᵒ for ⇛ᵒ/⇛ᵒᶠ

  ⇛ᵒ-Mono :  Monoᵒ $ ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ
  ⇛ᵒ-Mono =  ⇛ᵍ-Mono

  ⇛ᵒᶠ-Mono :  Monoᵒ $ ⇛ᵒᶠ Pᵒ
  ⇛ᵒᶠ-Mono =  ⇛ᵍᶠ-Mono

  -- Monotonicity of ⇛ᵒ/⇛ᵒᶠ

  ⇛ᵒ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Qᵒ
  ⇛ᵒ-mono✓ =  ⇛ᵍ-mono✓

  ⇛ᵒ-mono :  Pᵒ ⊨ Qᵒ →  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Qᵒ
  ⇛ᵒ-mono =  ⇛ᵍ-mono

  ⇛ᵒᶠ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  ⇛ᵒᶠ Pᵒ ⊨ ⇛ᵒᶠ Qᵒ
  ⇛ᵒᶠ-mono✓ =  ⇛ᵍᶠ-mono✓

  ⇛ᵒᶠ-mono :  Pᵒ ⊨ Qᵒ →  ⇛ᵒᶠ Pᵒ ⊨ ⇛ᵒᶠ Qᵒ
  ⇛ᵒᶠ-mono =  ⇛ᵍᶠ-mono

  -- ⊨✓ ⇛ᵒ/⇛ᵒᶠ into ⊨ ⇛ᵒ/⇛ᵒᶠ

  ⊨✓⇒⊨-⇛ᵒ :  Pᵒ ⊨✓ ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Qᵒ →  Pᵒ ⊨ ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Qᵒ
  ⊨✓⇒⊨-⇛ᵒ =  ⊨✓⇒⊨-⇛ᵍ

  ⊨✓⇒⊨-⇛ᵒᶠ :  Pᵒ ⊨✓ ⇛ᵒᶠ Qᵒ →  Pᵒ ⊨ ⇛ᵒᶠ Qᵒ
  ⊨✓⇒⊨-⇛ᵒᶠ =  ⊨✓⇒⊨-⇛ᵍᶠ

  -- Introduce ⇛ᵒ/⇛ᵒᶠ

  ⤇ᵒ⇒⇛ᵒ :  ⤇ᵒ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ
  ⤇ᵒ⇒⇛ᵒ =  ⤇ᵒ⇒⇛ᵍ refl˙

  ⇛ᵒ-intro :  Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ
  ⇛ᵒ-intro =  ⇛ᵍ-intro refl˙

  ⤇ᵒ⇒⇛ᵒᶠ :  ⤇ᵒ Pᵒ  ⊨  ⇛ᵒᶠ Pᵒ
  ⤇ᵒ⇒⇛ᵒᶠ =  ⤇ᵒ⇒⇛ᵍᶠ refl˙

  ⇛ᵒᶠ-intro :  Pᵒ  ⊨  ⇛ᵒᶠ Pᵒ
  ⇛ᵒᶠ-intro =  ⇛ᵍᶠ-intro refl˙

  -- Introduce ⇛ᵒ with ✓ᴹ

  ⇛ᵒ-intro-✓ᴹ :  Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M ⟩  ⌜ ✓ᴹ M ⌝ᵒ×  Pᵒ
  ⇛ᵒ-intro-✓ᴹ =  ⇛ᵍ-intro-✓ᴹ refl˙

  -- Join ⇛ᵒ/⇛ᵒᶠ

  ⇛ᵒ-join :  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ ⟨ M' ⟩⇛ᵒ⟨ M'' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M'' ⟩ Pᵒ
  ⇛ᵒ-join =  ⇛ᵍ-join refl refl˙

  ⇛ᵒᶠ-join :  ⇛ᵒᶠ ⇛ᵒᶠ Pᵒ  ⊨  ⇛ᵒᶠ Pᵒ
  ⇛ᵒᶠ-join =  ⇛ᵍᶠ-join refl refl˙

  -- Let ⇛ᵒ/⇛ᵒᶠ eat a proposition under ∗ᵒ

  ⇛ᵒ-eatˡ :  Qᵒ ∗ᵒ (⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ)  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩  Qᵒ ∗ᵒ Pᵒ
  ⇛ᵒ-eatˡ =  ⇛ᵍ-eatˡ

  ⇛ᵒ-eatʳ :  (⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ) ∗ᵒ Qᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩  Pᵒ ∗ᵒ Qᵒ
  ⇛ᵒ-eatʳ =  ⇛ᵍ-eatʳ

  ⇛ᵒᶠ-eatˡ :  Qᵒ ∗ᵒ (⇛ᵒᶠ Pᵒ)  ⊨ ⇛ᵒᶠ  Qᵒ ∗ᵒ Pᵒ
  ⇛ᵒᶠ-eatˡ =  ⇛ᵍᶠ-eatˡ

  ⇛ᵒᶠ-eatʳ :  (⇛ᵒᶠ Pᵒ) ∗ᵒ Qᵒ  ⊨ ⇛ᵒᶠ  Pᵒ ∗ᵒ Qᵒ
  ⇛ᵒᶠ-eatʳ =  ⇛ᵍᶠ-eatʳ

  -- Adequacy of ⇛ᵒ
  -- If we have X under ⟨ M ⟩⇛ᵒ⟨ M' ⟩ for valid M, then X holds purely

  ⇛ᵒ-adeq :  ✓ᴹ M →  ⊨ ⟨ M ⟩⇛ᵒ⟨ M' ⟩ ⌜ X ⌝ᵒ →  X
  ⇛ᵒ-adeq =  ⇛ᵍ-adeq Invᴳ-emp

  -- Perform a step by ⇛ᵒ

  ⇛ᵒ-step :  envᴳ M Eᴵⁿ ✓ᴳ a  →  ((⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ) ∗ᵒ Invᴳ Eᴵⁿ) a  →
             ∑ Fᴵⁿ , ∑ b ,  envᴳ M' Fᴵⁿ ✓ᴳ b  ×  (Pᵒ ∗ᵒ Invᴳ Fᴵⁿ) b
  ⇛ᵒ-step ME✓a ⇛P∗InvEa  with ⤇ᴱ-step ME✓a (⇛ᵍ-apply ⇛P∗InvEa)
  … | -, -, M'F✓b , P∗InvFb =  -, -, M'F✓b , P∗InvFb
