--------------------------------------------------------------------------------
-- Interpret the super update
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Interp where

open import Base.Level using (Level; _⊔ᴸ_; 2ᴸ)
open import Base.Func using (_$_; _›_; id)
open import Base.Few using (⊤₀)
open import Base.Eq using (_≡_; refl; ◠_; _◇˙_)
open import Base.Size using (∞)
open import Base.Prod using (_,_)
open import Base.Dec using (upd˙-self; upd˙²-self; upd˙²-2)
open import Base.Nat using ()
open import Syho.Lang.Reduce using (Mem)
open import Syho.Model.ERA.Glob using (envᴳ; envᴳ-cong)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; ⊨_; ⊤ᵒ₀; _∗ᵒ_;
  ⤇ᵒ_; _⤇ᴱ_; ⊨⇒⊨✓; substᵒ; ∗ᵒ-monoˡ; ∗ᵒ-comm; ⤇ᵒ-intro; ⤇ᴱ-respᴱˡ; ⤇ᴱ-param;
  ⤇ᴱ-eatʳ)
open import Syho.Model.Supd.Base using (⟨_⟩[_]⇛ᵍ'⟨_⟩_; ⇛ᵍ≡⇛ᵍ'; ⇛ᵍ-Mono;
  ⇛ᵍ-mono✓; ⇛ᵍ-make; ⊨✓⇛ᵍ⇒⊨⇛ᵍ; ⤇ᵒ⇒⇛ᵍ; ⇛ᵍ-join; ⇛ᵍ-eatˡ)
open import Syho.Model.Supd.Ind using (envᴵⁿᵈ; updᴱᴵⁿᵈ; Invᴵⁿᵈ; ⟨_⟩⇛ᴵⁿᵈ⟨_⟩_)

private variable
  ł :  Level
  M M' M'' :  Mem
  Pᵒ Qᵒ :  Propᵒ ł

--------------------------------------------------------------------------------
-- Interpret the super update

infix 3 ⟨_⟩⇛ᵒ'⟨_⟩_ ⟨_⟩⇛ᵒ⟨_⟩_

-- ⇛ᵒ' :  Non-abstract version of ⇛ᵒ

⟨_⟩⇛ᵒ'⟨_⟩_ :  Mem →  Mem →  Propᵒ ł →  Propᵒ (2ᴸ ⊔ᴸ ł)
⟨ M ⟩⇛ᵒ'⟨ M' ⟩ Pᵒ =  ⟨ M ⟩[ envᴵⁿᵈ , updᴱᴵⁿᵈ , Invᴵⁿᵈ ]⇛ᵍ'⟨ M' ⟩ Pᵒ

abstract

  -- ⇛ᵒ :  Interpret the super update

  ⟨_⟩⇛ᵒ⟨_⟩_ :  Mem →  Mem →  Propᵒ ł →  Propᵒ (2ᴸ ⊔ᴸ ł)
  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ =  ⟨ M ⟩⇛ᴵⁿᵈ⟨ M' ⟩ Pᵒ

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
  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᵒ P⊨ME⤇M'EQ =  ⇛ᵍ-make λ _ → ∗ᵒ-monoˡ P⊨ME⤇M'EQ › ⤇ᴱ-eatʳ ›
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

  ⊨✓⇛ᵒ⇒⊨⇛ᵒ :  Pᵒ ⊨✓ ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Qᵒ →  Pᵒ ⊨ ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Qᵒ
  ⊨✓⇛ᵒ⇒⊨⇛ᵒ =  ⊨✓⇛ᵍ⇒⊨⇛ᵍ

  -- Introduce ⇛ᵒ

  ⤇ᵒ⇒⇛ᵒ :  ⤇ᵒ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ
  ⤇ᵒ⇒⇛ᵒ =  ⤇ᵒ⇒⇛ᵍ $ upd˙²-self λ ()

  ⇛ᵒ-intro :  Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ
  ⇛ᵒ-intro =  ⤇ᵒ-intro › ⤇ᵒ⇒⇛ᵒ

  -- Join ⇛ᵒ

  ⇛ᵒ-join :  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ ⟨ M' ⟩⇛ᵒ⟨ M'' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M'' ⟩ Pᵒ
  ⇛ᵒ-join =  ⇛ᵍ-join refl $ upd˙²-2 λ ()

  -- Let ⇛ᵒ eat a proposition under ∗ᵒ

  ⇛ᵒ-eatˡ :  Pᵒ  ∗ᵒ  (⟨ M ⟩⇛ᵒ⟨ M' ⟩ Qᵒ)  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩  Pᵒ ∗ᵒ Qᵒ
  ⇛ᵒ-eatˡ =  ⇛ᵍ-eatˡ

  ⇛ᵒ-eatʳ :  (⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ)  ∗ᵒ  Qᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩  Pᵒ ∗ᵒ Qᵒ
  ⇛ᵒ-eatʳ =  ∗ᵒ-comm › ⇛ᵒ-eatˡ › ⇛ᵒ-mono ∗ᵒ-comm
