--------------------------------------------------------------------------------
-- Interpret the super update
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Interp where

open import Base.Level using (Level; _⊔ᴸ_; 2ᴸ)
open import Base.Func using (_$_; _▷_; _∘_; _›_; id)
open import Base.Few using (⊤₀)
open import Base.Eq using (_≡_; refl; ◠_; _◇˙_)
open import Base.Size using (∞)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_)
open import Base.Dec using (upd˙-self; upd˙²-self; upd˙²-2)
open import Base.Nat using ()
open import Syho.Lang.Reduce using (Mem; ✓ᴹ_)
open import Syho.Model.ERA.Glob using (Resᴳ; _✓ᴳ_; Envᴵⁿᴳ; envᴳ; empᴵⁿᴳ;
  empᴵⁿᴳ-✓; envᴳ-cong)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; ⊨_; ⊤ᵒ₀; ⌜_⌝ᵒ;
  ⌜_⌝ᵒ×_; _∗ᵒ_; ⤇ᵒ_; _⤇ᴱ_; ⊨⇒⊨✓; substᵒ; ∗ᵒ-monoˡ; ∗ᵒ-comm; ⤇ᵒ-intro; ⤇ᴱ-respᴱˡ;
  ⤇ᴱ-param; ⤇ᴱ-eatʳ; ⤇ᴱ-step)
open import Syho.Model.Supd.Base using (⟨_⟩[_]⇛ᵍ'⟨_⟩_; ⇛ᵍ≡⇛ᵍ'; ⇛ᵍ-Mono;
  ⇛ᵍ-mono✓; ⇛ᵍ-make; ⇛ᵍ-apply; ⊨✓⇒⊨-⇛ᵍ; ⤇ᵒ⇒⇛ᵍ; ⇛ᵍ-intro-✓ᴹ; ⇛ᵍ-join; ⇛ᵍ-eatˡ;
  ⇛ᵍ-adeq)
open import Syho.Model.Supd.Ind using (envᴵⁿᵈ; updᴱᴵⁿᵈ; Invᴵⁿᵈ; ⟨_⟩⇛ᴵⁿᵈ⟨_⟩_;
  Invᴵⁿᵈ-emp)

private variable
  ł :  Level
  M M' M'' :  Mem
  Pᵒ Qᵒ :  Propᵒ ł
  X :  Set ł
  Eᴵⁿ :  Envᴵⁿᴳ
  a :  Resᴳ

--------------------------------------------------------------------------------
-- Interpret the super update

infix 3 ⟨_⟩⇛ᵒ'⟨_⟩_ ⟨_⟩⇛ᵒ⟨_⟩_

-- ⇛ᵒ' :  Non-abstract version of ⇛ᵒ

⟨_⟩⇛ᵒ'⟨_⟩_ :  Mem →  Mem →  Propᵒ ł →  Propᵒ (2ᴸ ⊔ᴸ ł)
⟨ M ⟩⇛ᵒ'⟨ M' ⟩ Pᵒ =  ⟨ M ⟩[ envᴵⁿᵈ , updᴱᴵⁿᵈ , Invᴵⁿᵈ ]⇛ᵍ'⟨ M' ⟩ Pᵒ

-- The global invariant

Invᴳ :  Envᴵⁿᴳ →  Propᵒ 2ᴸ
Invᴳ =  Invᴵⁿᵈ ∘ envᴵⁿᵈ

abstract

  -- ⇛ᵒ :  Interpret the super update

  ⟨_⟩⇛ᵒ⟨_⟩_ :  Mem →  Mem →  Propᵒ ł →  Propᵒ (2ᴸ ⊔ᴸ ł)
  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ =  ⟨ M ⟩⇛ᴵⁿᵈ⟨ M' ⟩ Pᵒ

  -- Get Invᴳ empᴵⁿᴳ for free

  Invᴳ-emp :  ⊨ Invᴳ empᴵⁿᴳ
  Invᴳ-emp =  Invᴵⁿᵈ-emp

  -- ⇛ᵒ equals ⇛ᵒ'

  ⇛ᵒ≡⇛ᵒ' :  (⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ)  ≡  (⟨ M ⟩⇛ᵒ'⟨ M' ⟩ Pᵒ)
  ⇛ᵒ≡⇛ᵒ' =  ⇛ᵍ≡⇛ᵍ'

  ⇛ᵒ⇒⇛ᵒ' :  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ'⟨ M' ⟩ Pᵒ
  ⇛ᵒ⇒⇛ᵒ' =  substᵒ id ⇛ᵒ≡⇛ᵒ'

  ⇛ᵒ'⇒⇛ᵒ :  ⟨ M ⟩⇛ᵒ'⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ
  ⇛ᵒ'⇒⇛ᵒ =  substᵒ id $ ◠ ⇛ᵒ≡⇛ᵒ'

  -- ⇛ᴵⁿᵈ into ⇛ᵒ

  ⇛ᴵⁿᵈ⇒⇛ᵒ :  ⟨ M ⟩⇛ᴵⁿᵈ⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ
  ⇛ᴵⁿᵈ⇒⇛ᵒ =  id

  -- ⤇ᴱ on the memory into ⇛ᵒ

  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᵒ :  (∀{Eᴵⁿ} →  Pᵒ ⊨ envᴳ M Eᴵⁿ ⤇ᴱ λ(_ : ⊤₀) → envᴳ M' Eᴵⁿ , Qᵒ) →
                  Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Qᵒ
  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᵒ P⊨ME⤇M'EQ =  ⇛ᵍ-make $ ∗ᵒ-monoˡ P⊨ME⤇M'EQ › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-param › ⤇ᴱ-respᴱˡ $ envᴳ-cong $ upd˙-self ◇˙ upd˙-self

  ⊨⤇ᴱᴹᵉᵐ⇒⊨⇛ᵒ :  (∀{Eᴵⁿ} →  ⊨ envᴳ M Eᴵⁿ ⤇ᴱ λ(_ : ⊤₀) → envᴳ M' Eᴵⁿ , Pᵒ) →
                ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ
  ⊨⤇ᴱᴹᵉᵐ⇒⊨⇛ᵒ ⊨ME⤇M'EP =  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᵒ {Pᵒ = ⊤ᵒ₀} (λ _ → ⊨ME⤇M'EP) _

  -- Monoᵒ for ⇛ᵒ

  ⇛ᵒ-Mono :  Monoᵒ $ ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ
  ⇛ᵒ-Mono =  ⇛ᵍ-Mono

  -- Monotonicity of ⇛ᵒ

  ⇛ᵒ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Qᵒ
  ⇛ᵒ-mono✓ =  ⇛ᵍ-mono✓

  ⇛ᵒ-mono :  Pᵒ ⊨ Qᵒ →  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Qᵒ
  ⇛ᵒ-mono =  ⊨⇒⊨✓ › ⇛ᵒ-mono✓

  -- ⊨✓ ⇛ᵒ into ⊨ ⇛ᵒ

  ⊨✓⇒⊨-⇛ᵒ :  Pᵒ ⊨✓ ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Qᵒ →  Pᵒ ⊨ ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Qᵒ
  ⊨✓⇒⊨-⇛ᵒ =  ⊨✓⇒⊨-⇛ᵍ

  -- Introduce ⇛ᵒ

  ⤇ᵒ⇒⇛ᵒ :  ⤇ᵒ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ
  ⤇ᵒ⇒⇛ᵒ =  ⤇ᵒ⇒⇛ᵍ $ upd˙²-self λ ()

  ⇛ᵒ-intro :  Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ
  ⇛ᵒ-intro =  ⤇ᵒ-intro › ⤇ᵒ⇒⇛ᵒ

  -- Introduce ⇛ᵒ with ✓ᴹ

  ⇛ᵒ-intro-✓ᴹ :  Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M ⟩  ⌜ ✓ᴹ M ⌝ᵒ×  Pᵒ
  ⇛ᵒ-intro-✓ᴹ =  ⇛ᵍ-intro-✓ᴹ $ upd˙²-self λ ()

  -- Join ⇛ᵒ

  ⇛ᵒ-join :  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ ⟨ M' ⟩⇛ᵒ⟨ M'' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M'' ⟩ Pᵒ
  ⇛ᵒ-join =  ⇛ᵍ-join refl $ upd˙²-2 λ ()

  -- Let ⇛ᵒ eat a proposition under ∗ᵒ

  ⇛ᵒ-eatˡ :  Pᵒ  ∗ᵒ  (⟨ M ⟩⇛ᵒ⟨ M' ⟩ Qᵒ)  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩  Pᵒ ∗ᵒ Qᵒ
  ⇛ᵒ-eatˡ =  ⇛ᵍ-eatˡ

  ⇛ᵒ-eatʳ :  (⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ)  ∗ᵒ  Qᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩  Pᵒ ∗ᵒ Qᵒ
  ⇛ᵒ-eatʳ =  ∗ᵒ-comm › ⇛ᵒ-eatˡ › ⇛ᵒ-mono ∗ᵒ-comm

  -- Adequacy of ⇛ᵒ
  -- If we have X under ⟨ M ⟩⇛ᵒ⟨ M' ⟩ for valid M, then X holds purely

  ⇛ᵒ-adeq :  ✓ᴹ M →  ⊨ ⟨ M ⟩⇛ᵒ⟨ M' ⟩ ⌜ X ⌝ᵒ →  X
  ⇛ᵒ-adeq =  ⇛ᵍ-adeq Invᴳ-emp

  -- Perform a step using ⇛ᵒ

  ⇛ᵒ-step :  envᴳ M Eᴵⁿ ✓ᴳ a  ×  ((⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ) ∗ᵒ Invᴳ Eᴵⁿ) a  →
             ∑ Fᴵⁿ , ∑ b ,  envᴳ M' Fᴵⁿ ✓ᴳ b  ×  (Pᵒ ∗ᵒ Invᴳ Fᴵⁿ) b
  ⇛ᵒ-step (ME✓a , ⇛P∗InvEa)  with ⤇ᴱ-step (ME✓a , ⇛ᵍ-apply ⇛P∗InvEa)
  … | -, -, M'F✓b , P∗InvFb =  -, -, M'F✓b , P∗InvFb
