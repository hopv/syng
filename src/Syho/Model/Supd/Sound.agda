--------------------------------------------------------------------------------
-- Prove semantic soundness of the super update
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Sound where

open import Base.Level using (Level; _⊔ᴸ_; 2ᴸ)
open import Base.Func using (_$_; _›_; id)
open import Base.Eq using (_≡_; refl; ◠_)
open import Base.Size using (∞)
open import Base.Prod using (∑-case; _,_)
open import Base.Dec using (upd˙²-self; upd˙²-2)
open import Base.Nat using (ℕ)
open import Syho.Lang.Reduce using (Mem)
open import Syho.Logic.Prop using (Prop')
open import Syho.Logic.Core using (_»_; ∃₁-elim)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_; ⇛-ṡ; ⇛-refl-⤇; _ᵘ»ᵘ_; ⇛-frameˡ)
open import Syho.Logic.Ind using (○-alloc; □○-alloc-rec; ○-use; ↪⇛-use)
open import Syho.Model.Prop.Base using (Propᵒ; _⊨_; ⤇ᵒ_; substᵒ; ∗ᵒ-monoʳ;
  ∗ᵒ∃ᵒ-out; ⤇ᵒ-intro)
open import Syho.Model.Prop.Interp using (⸨_⸩)
open import Syho.Model.Prop.Sound using (⊢⇒⊨✓)
open import Syho.Model.Supd.Base using (⟨_⟩[_]⇛ᵍ'⟨_⟩_; ⇛ᵍ≡⇛ᵍ'; ⊨✓⇛ᵍ⇒⊨⇛ᵍ;
  ⇛ᵍ-mono; ⤇ᵒ⇒⇛ᵍ; ⇛ᵍ-join; ⇛ᵍ-eatˡ)
open import Syho.Model.Supd.Ind using (envᴵⁿᵈ; updᴱᴵⁿᵈ; Invᴵⁿᵈ; ⟨_⟩⇛ᴵⁿᵈ⟨_⟩_;
  ○ᵒ-alloc; □ᵒ○ᵒ-alloc-rec; ○ᵒ-use; ↪⇛ᵒ-use)

private variable
  ł :  Level
  P Q :  Prop' ∞
  i :  ℕ
  M M' M'' :  Mem
  Pᵒ :  Propᵒ ł

--------------------------------------------------------------------------------
-- Super update

infix 3 ⟨_⟩⇛ᵒ⟨_⟩_ ⟨_⟩⇛ᵒ'⟨_⟩_

-- ⇛ᵒ :  Super update

⟨_⟩⇛ᵒ⟨_⟩_ :  Mem →  Mem →  Propᵒ ł →  Propᵒ (2ᴸ ⊔ᴸ ł)
⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ =  ⟨ M ⟩⇛ᴵⁿᵈ⟨ M' ⟩ Pᵒ

-- ⇛ᵒ' :  Non-abstract version of ⇛ᵒ

⟨_⟩⇛ᵒ'⟨_⟩_ :  Mem →  Mem →  Propᵒ ł →  Propᵒ (2ᴸ ⊔ᴸ ł)
⟨ M ⟩⇛ᵒ'⟨ M' ⟩ Pᵒ =  ⟨ M ⟩[ envᴵⁿᵈ , updᴱᴵⁿᵈ , Invᴵⁿᵈ ]⇛ᵍ'⟨ M' ⟩ Pᵒ

abstract

  -- ⇛ᵒ equals ⇛ᵒ'

  ⇛ᵒ≡⇛ᵒ' :  (⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ)  ≡  (⟨ M ⟩⇛ᵒ'⟨ M' ⟩ Pᵒ)
  ⇛ᵒ≡⇛ᵒ' =  ⇛ᵍ≡⇛ᵍ'

  ⇛ᵒ⇒⇛ᵒ' :  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ'⟨ M' ⟩ Pᵒ
  ⇛ᵒ⇒⇛ᵒ' =  substᵒ id ⇛ᵒ≡⇛ᵒ'

  ⇛ᵒ'⇒⇛ᵒ :  ⟨ M ⟩⇛ᵒ'⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ
  ⇛ᵒ'⇒⇛ᵒ =  substᵒ id $ ◠ ⇛ᵒ≡⇛ᵒ'

  -- ⤇ᵒ into ⇛ᵒ

  ⤇ᵒ⇒⇛ᵒ :  ⤇ᵒ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ
  ⤇ᵒ⇒⇛ᵒ =  ⤇ᵒ⇒⇛ᵍ $ upd˙²-self λ ()

  -- Introduce ⇛ᵒ

  ⇛ᵒ-intro :  Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ
  ⇛ᵒ-intro =  ⤇ᵒ-intro › ⤇ᵒ⇒⇛ᵒ

  -- Join ⇛ᵒ

  ⇛ᵒ-join :  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ ⟨ M' ⟩⇛ᵒ⟨ M'' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M'' ⟩ Pᵒ
  ⇛ᵒ-join =  ⇛ᵍ-join refl $ upd˙²-2 λ ()

--------------------------------------------------------------------------------
-- ⊢⇛⇒⊨⇛ᵒ :  Semantic soundness of the super update

⊢⇛⇒⊨⇛ᵒ :  P ⊢[ ∞ ][ i ]⇛ Q →  ⸨ P ⸩ ⊨ ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⸨ Q ⸩

-- _»_ :  P ⊢[ ∞ ][ i ] Q →  Q ⊢[ ∞ ][ i ]⇛ R →  P ⊢[ ∞ ][ i ]⇛ R

⊢⇛⇒⊨⇛ᵒ (P⊢Q » Q⊢⇛R) =  ⊨✓⇛ᵍ⇒⊨⇛ᵍ λ ✓∙ → ⊢⇒⊨✓ P⊢Q ✓∙ › ⊢⇛⇒⊨⇛ᵒ Q⊢⇛R

-- ∃₁-elim :  (∀ x →  P˙ x ⊢[ ∞ ][ i ]⇛ Q) →  ∃₁˙ P˙ ⊢[ ∞ ][ i ]⇛ Q

⊢⇛⇒⊨⇛ᵒ (∃₁-elim Px⊢⇛Q) =   ∑-case λ x → ⊢⇛⇒⊨⇛ᵒ (Px⊢⇛Q x)

-- ⇛-ṡ :  P ⊢[ ∞ ][ i ]⇛ Q →  P ⊢[ ∞ ][ ṡ i ]⇛ Q

⊢⇛⇒⊨⇛ᵒ (⇛-ṡ P⊢⇛Q) =  ⊢⇛⇒⊨⇛ᵒ P⊢⇛Q

-- ⇛-refl-⤇ :  ⤇ P ⊢[ ∞ ][ i ]⇛ P

⊢⇛⇒⊨⇛ᵒ ⇛-refl-⤇ =  ⤇ᵒ⇒⇛ᵒ

-- _ᵘ»ᵘ_ :  P ⊢[ ∞ ][ i ]⇛ Q →  Q ⊢[ ∞ ][ i ]⇛ R →  P ⊢[ ∞ ][ i ]⇛ R

⊢⇛⇒⊨⇛ᵒ (P⊢⇛Q ᵘ»ᵘ Q⊢⇛R) =  ⊢⇛⇒⊨⇛ᵒ P⊢⇛Q › ⇛ᵍ-mono (⊢⇛⇒⊨⇛ᵒ Q⊢⇛R) › ⇛ᵒ-join

-- ⇛-frameˡ :  Q ⊢[ ∞ ][ i ]⇛ R →  P ∗ Q ⊢[ ∞ ][ i ]⇛ P ∗ R

⊢⇛⇒⊨⇛ᵒ (⇛-frameˡ Q⊢⇛R) =  ∗ᵒ-monoʳ (⊢⇛⇒⊨⇛ᵒ Q⊢⇛R) › ⇛ᵍ-eatˡ

-- ○-alloc :  P˂ .! ⊢[ ∞ ][ i ]⇛ ○ P˂

⊢⇛⇒⊨⇛ᵒ ○-alloc =  ○ᵒ-alloc

-- □○-alloc-rec :  □ ○ P˂ -∗ □ P˂ .! ⊢[ ∞ ][ i ]⇛ □ ○ P˂

⊢⇛⇒⊨⇛ᵒ □○-alloc-rec =  □ᵒ○ᵒ-alloc-rec

-- ○-use :  ○ P˂ ⊢[ ∞ ][ i ]⇛ P˂ .!

⊢⇛⇒⊨⇛ᵒ ○-use =  ○ᵒ-use

-- ↪⇛-use :  P˂ .! ∗ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ∞ ][ ṡ i ]⇛  Q˂ .!
---- The counter increment ṡ i makes the recursive call of ⊢⇛⇒⊨⇛ᵒ inductive

⊢⇛⇒⊨⇛ᵒ ↪⇛-use =  ∗ᵒ-monoʳ ↪⇛ᵒ-use › ⇛ᵍ-eatˡ ›
  ⇛ᵍ-mono (∗ᵒ∃ᵒ-out › ∑-case λ _ → ∗ᵒ∃ᵒ-out › ∑-case λ P∗R⊢⇛Q → ⊢⇛⇒⊨⇛ᵒ P∗R⊢⇛Q) ›
  ⇛ᵒ-join
