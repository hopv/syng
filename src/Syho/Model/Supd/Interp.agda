--------------------------------------------------------------------------------
-- Interpret the super update
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Interp where

open import Base.Level using (Level; _⊔ᴸ_; 2ᴸ)
open import Base.Func using (_$_; _›_; id)
open import Base.Eq using (_≡_; refl; ◠_)
open import Base.Size using (∞)
open import Base.Prod using (_,_)
open import Base.Dec using (upd˙²-self; upd˙²-2)
open import Base.Nat using ()
open import Syho.Lang.Reduce using (Mem)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; _∗ᵒ_; ⤇ᵒ_;
  ⊨⇒⊨✓; substᵒ; ∗ᵒ-comm; ⤇ᵒ-intro)
open import Syho.Model.Supd.Base using (⟨_⟩[_]⇛ᵍ'⟨_⟩_; ⇛ᵍ≡⇛ᵍ'; ⇛ᵍ-Mono;
  ⇛ᵍ-mono✓; ⊨✓⇛ᵍ⇒⊨⇛ᵍ; ⤇ᵒ⇒⇛ᵍ; ⇛ᵍ-join; ⇛ᵍ-eatˡ)
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

  ⇛ᵒ-eatˡ :  Pᵒ ∗ᵒ (⟨ M ⟩⇛ᵒ⟨ M' ⟩ Qᵒ)  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ ∗ᵒ Qᵒ
  ⇛ᵒ-eatˡ =  ⇛ᵍ-eatˡ

  ⇛ᵒ-eatʳ :  (⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ) ∗ᵒ Qᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ ∗ᵒ Qᵒ
  ⇛ᵒ-eatʳ =  ∗ᵒ-comm › ⇛ᵒ-eatˡ › ⇛ᵒ-mono ∗ᵒ-comm
