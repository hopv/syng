--------------------------------------------------------------------------------
-- Prove the semantic soundness of the super update
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Sound where

open import Base.Func using (_›_)
open import Base.Size using (∞)
open import Base.Prod using (∑-case; _,_)
open import Base.Nat using (ℕ)
open import Syho.Lang.Reduce using (Mem)
open import Syho.Logic.Prop using (Prop')
open import Syho.Logic.Core using (_»_; ∃₁-elim)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_; ⇛-ṡ; ⇛-refl-⤇; _ᵘ»ᵘ_; ⇛-frameˡ)
open import Syho.Logic.Ind using (○-alloc; □○-alloc-rec; ○-use; ↪⇛-use)
open import Syho.Model.Prop.Base using (_⊨_; ∗ᵒ-monoʳ; ∗ᵒ∃ᵒ-out)
open import Syho.Model.Prop.Interp using (⸨_⸩)
open import Syho.Model.Prop.Sound using (⊢⇒⊨✓)
open import Syho.Model.Supd.Ind using (○ᵒ-alloc; □ᵒ○ᵒ-alloc-rec; ○ᵒ-use;
  ↪⇛ᵒ-use)
open import Syho.Model.Supd.Interp using (⟨_⟩⇛ᵒ⟨_⟩_; ⇛ᴵⁿᵈ⇒⇛ᵒ; ⇛ᵒ-mono; ⊨✓⇒⊨-⇛ᵒ;
  ⤇ᵒ⇒⇛ᵒ; ⇛ᵒ-join; ⇛ᵒ-eatˡ)

private variable
  P Q :  Prop' ∞
  i :  ℕ
  M :  Mem

--------------------------------------------------------------------------------
-- ⊢⇛⇒⊨⇛ᵒ :  Semantic soundness of the super update

⊢⇛⇒⊨⇛ᵒ :  P ⊢[ ∞ ][ i ]⇛ Q →  ⸨ P ⸩ ⊨ ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⸨ Q ⸩

-- _»_ :  P ⊢[ ∞ ] Q →  Q ⊢[ ∞ ][ i ]⇛ R →  P ⊢[ ∞ ][ i ]⇛ R

⊢⇛⇒⊨⇛ᵒ (P⊢Q » Q⊢⇛R) =  ⊨✓⇒⊨-⇛ᵒ λ ✓∙ → ⊢⇒⊨✓ P⊢Q ✓∙ › ⊢⇛⇒⊨⇛ᵒ Q⊢⇛R

-- ∃₁-elim :  (∀ x →  P˙ x ⊢[ ∞ ][ i ]⇛ Q) →  ∃₁˙ P˙ ⊢[ ∞ ][ i ]⇛ Q

⊢⇛⇒⊨⇛ᵒ (∃₁-elim Px⊢⇛Q) =   ∑-case λ x → ⊢⇛⇒⊨⇛ᵒ (Px⊢⇛Q x)

-- ⇛-ṡ :  P ⊢[ ∞ ][ i ]⇛ Q →  P ⊢[ ∞ ][ ṡ i ]⇛ Q

⊢⇛⇒⊨⇛ᵒ (⇛-ṡ P⊢⇛Q) =  ⊢⇛⇒⊨⇛ᵒ P⊢⇛Q

-- ⇛-refl-⤇ :  ⤇ P ⊢[ ∞ ][ i ]⇛ P

⊢⇛⇒⊨⇛ᵒ ⇛-refl-⤇ =  ⤇ᵒ⇒⇛ᵒ

-- _ᵘ»ᵘ_ :  P ⊢[ ∞ ][ i ]⇛ Q →  Q ⊢[ ∞ ][ i ]⇛ R →  P ⊢[ ∞ ][ i ]⇛ R

⊢⇛⇒⊨⇛ᵒ (P⊢⇛Q ᵘ»ᵘ Q⊢⇛R) =  ⊢⇛⇒⊨⇛ᵒ P⊢⇛Q › ⇛ᵒ-mono (⊢⇛⇒⊨⇛ᵒ Q⊢⇛R) › ⇛ᵒ-join

-- ⇛-frameˡ :  Q ⊢[ ∞ ][ i ]⇛ R →  P ∗ Q ⊢[ ∞ ][ i ]⇛ P ∗ R

⊢⇛⇒⊨⇛ᵒ (⇛-frameˡ Q⊢⇛R) =  ∗ᵒ-monoʳ (⊢⇛⇒⊨⇛ᵒ Q⊢⇛R) › ⇛ᵒ-eatˡ

-- ○-alloc :  P˂ .! ⊢[ ∞ ][ i ]⇛ ○ P˂

⊢⇛⇒⊨⇛ᵒ ○-alloc =  ○ᵒ-alloc › ⇛ᴵⁿᵈ⇒⇛ᵒ

-- □○-alloc-rec :  □ ○ P˂ -∗ □ P˂ .! ⊢[ ∞ ][ i ]⇛ □ ○ P˂

⊢⇛⇒⊨⇛ᵒ □○-alloc-rec =  □ᵒ○ᵒ-alloc-rec › ⇛ᴵⁿᵈ⇒⇛ᵒ

-- ○-use :  ○ P˂ ⊢[ ∞ ][ i ]⇛ P˂ .!

⊢⇛⇒⊨⇛ᵒ ○-use =  ○ᵒ-use › ⇛ᴵⁿᵈ⇒⇛ᵒ

-- ↪⇛-use :  P˂ .! ∗ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ∞ ][ ṡ i ]⇛  Q˂ .!
---- The counter increment ṡ i makes the recursive call of ⊢⇛⇒⊨⇛ᵒ inductive

⊢⇛⇒⊨⇛ᵒ ↪⇛-use =  ∗ᵒ-monoʳ (↪⇛ᵒ-use › ⇛ᴵⁿᵈ⇒⇛ᵒ) › ⇛ᵒ-eatˡ ›
  ⇛ᵒ-mono (∗ᵒ∃ᵒ-out › ∑-case λ _ → ∗ᵒ∃ᵒ-out › ∑-case λ P∗R⊢⇛Q → ⊢⇛⇒⊨⇛ᵒ P∗R⊢⇛Q) ›
  ⇛ᵒ-join
