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
  ⊤ᵒ₀; ⌜_⌝ᵒ; ⌜_⌝ᵒ×_; _∗ᵒ_; _-∗ᵒ_; ⤇ᵒ_; _⤇ᴱ_; substᵒ; ∗ᵒ-monoˡ; ∗ᵒ-comm;
  ∗ᵒ?-intro; -∗ᵒ-intro; ⤇ᴱ-param; ⤇ᴱ-eatʳ; ⤇ᴱ-step)
open import Syho.Model.Prop.Names using ([⊤]ᴺᵒ)
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

infix 3 ⟨_⟩⇛ᴹ'⟨_⟩_ ⟨_⟩⇛ᴹ⟨_⟩_ ⇛ᵒ_ ⇛ᴺᵒ_

-- Invᴳ :  Global invariant

Invᴳ :  Envᴵⁿᴳ →  Propᵒ 1ᴸ
Invᴳ Eᴵⁿ =  Invᴵⁿᵈ (envᴵⁿᵈ Eᴵⁿ)  ∗ᵒ  Invᴵⁿᵛ (Eᴵⁿ jᴵⁿᵛ)

-- ⇛ᴹ' :  Non-abstract version of ⇛ᴹ

⟨_⟩⇛ᴹ'⟨_⟩_ :  Mem →  Mem →  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⟨ M ⟩⇛ᴹ'⟨ M' ⟩ Pᵒ =  ⟨ M ⟩[ id , const , Invᴳ ]⇛ᵍ'⟨ M' ⟩ Pᵒ

abstract

  -- ⇛ᴹ :  Semantic super update with a memory

  ⟨_⟩⇛ᴹ⟨_⟩_ :  Mem →  Mem →  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ =  ⟨ M ⟩[ id , const , Invᴳ ]⇛ᵍ⟨ M' ⟩ Pᵒ

-- ⇛ᵒ :  Semantic super update, i.e., ⇛ᴹ with any fixed memory

⇛ᵒ_ :  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⇛ᵒ Pᵒ =  ∀ᵒ M , ⟨ M ⟩⇛ᴹ⟨ M ⟩ Pᵒ

-- ⇛ᴺᵒ :  ⇛ᵒ with [⊤]ᴺᵒ

⇛ᴺᵒ_ :  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⇛ᴺᵒ Pᵒ =  [⊤]ᴺᵒ -∗ᵒ (⇛ᵒ Pᵒ ∗ᵒ [⊤]ᴺᵒ)

abstract

  -- Get Invᴳ empᴵⁿᴳ for free

  Invᴳ-emp :  ⊨ Invᴳ empᴵⁿᴳ
  Invᴳ-emp =  Invᴵⁿᵈ-emp ▷ ∗ᵒ?-intro Invᴵⁿᵛ-emp

  -- ⇛ᴹ equals ⇛ᴹ'

  ⇛ᴹ≡⇛ᴹ' :  (⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ)  ≡  (⟨ M ⟩⇛ᴹ'⟨ M' ⟩ Pᵒ)
  ⇛ᴹ≡⇛ᴹ' =  ⇛ᵍ≡⇛ᵍ'

  ⇛ᴹ⇒⇛ᴹ' :  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᴹ'⟨ M' ⟩ Pᵒ
  ⇛ᴹ⇒⇛ᴹ' =  substᵒ id ⇛ᴹ≡⇛ᴹ'

  ⇛ᴹ'⇒⇛ᴹ :  ⟨ M ⟩⇛ᴹ'⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ
  ⇛ᴹ'⇒⇛ᴹ =  substᵒ id $ ◠ ⇛ᴹ≡⇛ᴹ'

  -- ⇛ᴵⁿᵈ into ⇛ᵒ

  ⇛ᴵⁿᵈ⇒⇛ᵒ :  ⇛ᴵⁿᵈ Pᵒ  ⊨  ⇛ᵒ Pᵒ
  ⇛ᴵⁿᵈ⇒⇛ᵒ =  ⇛ᵍᶠ-mono ⇛ᴵⁿᵛ-intro › ⇛ᵍᶠ-join2 refl › ⇛ᵍᶠ-all refl

  -- ⇛ᴵⁿᵛ into ⇛ᵒ

  ⇛ᴵⁿᵛ⇒⇛ᵒ :  ⇛ᴵⁿᵛ Pᵒ  ⊨  ⇛ᵒ Pᵒ
  ⇛ᴵⁿᵛ⇒⇛ᵒ =  ⇛ᴵⁿᵈ-intro › ⇛ᵍᶠ-join2 refl › ⇛ᵍᶠ-all refl

  -- ⤇ᴱ on the memory into ⇛ᴹ

  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᴹ :
    (∀{Eᴵⁿ} →  Pᵒ ⊨ envᴳ M Eᴵⁿ ⤇ᴱ λ (_ : ⊤₀) → envᴳ M' Eᴵⁿ , Qᵒ)  →
    Pᵒ  ⊨  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Qᵒ
  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᴹ P⊨ME⤇M'EQ =  ⇛ᵍ-make $ ∗ᵒ-monoˡ P⊨ME⤇M'EQ › ⤇ᴱ-eatʳ › ⤇ᴱ-param

  ⊨⤇ᴱᴹᵉᵐ⇒⊨⇛ᴹ :  (∀{Eᴵⁿ} →  ⊨ envᴳ M Eᴵⁿ ⤇ᴱ λ (_ : ⊤₀) → envᴳ M' Eᴵⁿ , Pᵒ)  →
                ⊨  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ
  ⊨⤇ᴱᴹᵉᵐ⇒⊨⇛ᴹ ⊨ME⤇M'EP =  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᴹ {Pᵒ = ⊤ᵒ₀} (λ _ → ⊨ME⤇M'EP) _

  -- Monoᵒ for ⇛ᴹ/⇛ᵒ

  ⇛ᴹ-Mono :  Monoᵒ $ ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ
  ⇛ᴹ-Mono =  ⇛ᵍ-Mono

  ⇛ᵒ-Mono :  Monoᵒ $ ⇛ᵒ Pᵒ
  ⇛ᵒ-Mono =  ⇛ᵍᶠ-Mono

  -- Monotonicity of ⇛ᴹ/⇛ᵒ

  ⇛ᴹ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Qᵒ
  ⇛ᴹ-mono✓ =  ⇛ᵍ-mono✓

  ⇛ᴹ-mono :  Pᵒ ⊨ Qᵒ →  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Qᵒ
  ⇛ᴹ-mono =  ⇛ᵍ-mono

  ⇛ᵒ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  ⇛ᵒ Pᵒ ⊨ ⇛ᵒ Qᵒ
  ⇛ᵒ-mono✓ =  ⇛ᵍᶠ-mono✓

  ⇛ᵒ-mono :  Pᵒ ⊨ Qᵒ →  ⇛ᵒ Pᵒ ⊨ ⇛ᵒ Qᵒ
  ⇛ᵒ-mono =  ⇛ᵍᶠ-mono

  -- ⊨✓ ⇛ᴹ/⇛ᵒ into ⊨ ⇛ᴹ/⇛ᵒ

  ⊨✓⇒⊨-⇛ᴹ :  Pᵒ ⊨✓ ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Qᵒ →  Pᵒ ⊨ ⟨ M ⟩⇛ᴹ⟨ M' ⟩ Qᵒ
  ⊨✓⇒⊨-⇛ᴹ =  ⊨✓⇒⊨-⇛ᵍ

  ⊨✓⇒⊨-⇛ᵒ :  Pᵒ ⊨✓ ⇛ᵒ Qᵒ →  Pᵒ ⊨ ⇛ᵒ Qᵒ
  ⊨✓⇒⊨-⇛ᵒ =  ⊨✓⇒⊨-⇛ᵍᶠ

  -- Introduce ⇛ᴹ/⇛ᵒ

  ⤇ᵒ⇒⇛ᴹ :  ⤇ᵒ Pᵒ  ⊨  ⟨ M ⟩⇛ᴹ⟨ M ⟩ Pᵒ
  ⤇ᵒ⇒⇛ᴹ =  ⤇ᵒ⇒⇛ᵍ refl˙

  ⇛ᴹ-intro :  Pᵒ  ⊨  ⟨ M ⟩⇛ᴹ⟨ M ⟩ Pᵒ
  ⇛ᴹ-intro =  ⇛ᵍ-intro refl˙

  ⤇ᵒ⇒⇛ᵒ :  ⤇ᵒ Pᵒ  ⊨  ⇛ᵒ Pᵒ
  ⤇ᵒ⇒⇛ᵒ =  ⤇ᵒ⇒⇛ᵍᶠ refl˙

  ⇛ᵒ-intro :  Pᵒ  ⊨  ⇛ᵒ Pᵒ
  ⇛ᵒ-intro =  ⇛ᵍᶠ-intro refl˙

  -- Introduce ⇛ᴹ with ✓ᴹ

  ⇛ᴹ-intro-✓ᴹ :  Pᵒ  ⊨  ⟨ M ⟩⇛ᴹ⟨ M ⟩  ⌜ ✓ᴹ M ⌝ᵒ×  Pᵒ
  ⇛ᴹ-intro-✓ᴹ =  ⇛ᵍ-intro-✓ᴹ refl˙

  -- Join ⇛ᴹ/⇛ᵒ

  ⇛ᴹ-join :  ⟨ M ⟩⇛ᴹ⟨ M' ⟩ ⟨ M' ⟩⇛ᴹ⟨ M'' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᴹ⟨ M'' ⟩ Pᵒ
  ⇛ᴹ-join =  ⇛ᵍ-join refl refl˙

  ⇛ᵒ-join :  ⇛ᵒ ⇛ᵒ Pᵒ  ⊨  ⇛ᵒ Pᵒ
  ⇛ᵒ-join =  ⇛ᵍᶠ-join refl refl˙

  -- Let ⇛ᴹ/⇛ᵒ eat a proposition under ∗ᵒ

  ⇛ᴹ-eatˡ :  Qᵒ ∗ᵒ (⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ)  ⊨  ⟨ M ⟩⇛ᴹ⟨ M' ⟩  Qᵒ ∗ᵒ Pᵒ
  ⇛ᴹ-eatˡ =  ⇛ᵍ-eatˡ

  ⇛ᴹ-eatʳ :  (⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ) ∗ᵒ Qᵒ  ⊨  ⟨ M ⟩⇛ᴹ⟨ M' ⟩  Pᵒ ∗ᵒ Qᵒ
  ⇛ᴹ-eatʳ =  ⇛ᵍ-eatʳ

  ⇛ᵒ-eatˡ :  Qᵒ ∗ᵒ (⇛ᵒ Pᵒ)  ⊨ ⇛ᵒ  Qᵒ ∗ᵒ Pᵒ
  ⇛ᵒ-eatˡ =  ⇛ᵍᶠ-eatˡ

  ⇛ᵒ-eatʳ :  (⇛ᵒ Pᵒ) ∗ᵒ Qᵒ  ⊨ ⇛ᵒ  Pᵒ ∗ᵒ Qᵒ
  ⇛ᵒ-eatʳ =  ⇛ᵍᶠ-eatʳ

  -- ⇛ᵒ into ⇛ᴺᵒ

  ⇛ᵒ⇒⇛ᴺᵒ :  ⇛ᵒ Pᵒ ⊨ ⇛ᴺᵒ Pᵒ
  ⇛ᵒ⇒⇛ᴺᵒ =  -∗ᵒ-intro λ _ → ∗ᵒ-comm › ⇛ᵒ-eatʳ

  -- Adequacy of ⇛ᴹ
  -- If we have X under ⟨ M ⟩⇛ᴹ⟨ M' ⟩ for valid M, then X holds purely

  ⇛ᴹ-adeq :  ✓ᴹ M →  ⊨ ⟨ M ⟩⇛ᴹ⟨ M' ⟩ ⌜ X ⌝ᵒ →  X
  ⇛ᴹ-adeq =  ⇛ᵍ-adeq Invᴳ-emp

  -- Perform a step by ⇛ᴹ

  ⇛ᴹ-step :  envᴳ M Eᴵⁿ ✓ᴳ a  →  ((⟨ M ⟩⇛ᴹ⟨ M' ⟩ Pᵒ) ∗ᵒ Invᴳ Eᴵⁿ) a  →
             ∑ Fᴵⁿ , ∑ b ,  envᴳ M' Fᴵⁿ ✓ᴳ b  ×  (Pᵒ ∗ᵒ Invᴳ Fᴵⁿ) b
  ⇛ᴹ-step ME✓a ⇛P∗InvEa  with ⤇ᴱ-step ME✓a (⇛ᵍ-apply ⇛P∗InvEa)
  … | -, -, M'F✓b , P∗InvFb =  -, -, M'F✓b , P∗InvFb
