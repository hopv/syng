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
open import Syho.Model.Prop.Sound using (⊢-sem)
open import Syho.Model.Supd.Ind using (○ᵒ-alloc; □ᵒ○ᵒ-alloc-rec; ○ᵒ-use;
  ↪⇛ᵒ-use)
open import Syho.Model.Supd.Interp using (⟨_⟩⇛ᵒ⟨_⟩_; ⇛ᴵⁿᵈ⇒⇛ᵒ; ⇛ᵒ-mono; ⊨✓⇒⊨-⇛ᵒ;
  ⤇ᵒ⇒⇛ᵒ; ⇛ᵒ-join; ⇛ᵒ-eatˡ)

private variable
  P Q :  Prop' ∞
  i :  ℕ
  M :  Mem

--------------------------------------------------------------------------------
-- ⊢⇛-sem :  Semantic soundness of the super update

⊢⇛-sem :  P ⊢[ ∞ ][ i ]⇛ Q →  ⸨ P ⸩ ⊨ ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⸨ Q ⸩

-- _»_ :  P ⊢[ ∞ ] Q →  Q ⊢[ ∞ ][ i ]⇛ R →  P ⊢[ ∞ ][ i ]⇛ R

⊢⇛-sem (P⊢Q » Q⊢⇛R) =  ⊨✓⇒⊨-⇛ᵒ λ ✓∙ → ⊢-sem P⊢Q ✓∙ › ⊢⇛-sem Q⊢⇛R

-- ∃₁-elim :  (∀ x →  P˙ x ⊢[ ∞ ][ i ]⇛ Q) →  ∃₁˙ P˙ ⊢[ ∞ ][ i ]⇛ Q

⊢⇛-sem (∃₁-elim Px⊢⇛Q) =   ∑-case λ x → ⊢⇛-sem (Px⊢⇛Q x)

-- ⇛-ṡ :  P ⊢[ ∞ ][ i ]⇛ Q →  P ⊢[ ∞ ][ ṡ i ]⇛ Q

⊢⇛-sem (⇛-ṡ P⊢⇛Q) =  ⊢⇛-sem P⊢⇛Q

-- ⇛-refl-⤇ :  ⤇ P ⊢[ ∞ ][ i ]⇛ P

⊢⇛-sem ⇛-refl-⤇ =  ⤇ᵒ⇒⇛ᵒ

-- _ᵘ»ᵘ_ :  P ⊢[ ∞ ][ i ]⇛ Q →  Q ⊢[ ∞ ][ i ]⇛ R →  P ⊢[ ∞ ][ i ]⇛ R

⊢⇛-sem (P⊢⇛Q ᵘ»ᵘ Q⊢⇛R) =  ⊢⇛-sem P⊢⇛Q › ⇛ᵒ-mono (⊢⇛-sem Q⊢⇛R) › ⇛ᵒ-join

-- ⇛-frameˡ :  Q ⊢[ ∞ ][ i ]⇛ R →  P ∗ Q ⊢[ ∞ ][ i ]⇛ P ∗ R

⊢⇛-sem (⇛-frameˡ Q⊢⇛R) =  ∗ᵒ-monoʳ (⊢⇛-sem Q⊢⇛R) › ⇛ᵒ-eatˡ

-- ○-alloc :  P˂ .! ⊢[ ∞ ][ i ]⇛ ○ P˂

⊢⇛-sem ○-alloc =  ○ᵒ-alloc › ⇛ᴵⁿᵈ⇒⇛ᵒ

-- □○-alloc-rec :  □ ○ P˂ -∗ □ P˂ .! ⊢[ ∞ ][ i ]⇛ □ ○ P˂

⊢⇛-sem □○-alloc-rec =  □ᵒ○ᵒ-alloc-rec › ⇛ᴵⁿᵈ⇒⇛ᵒ

-- ○-use :  ○ P˂ ⊢[ ∞ ][ i ]⇛ P˂ .!

⊢⇛-sem ○-use =  ○ᵒ-use › ⇛ᴵⁿᵈ⇒⇛ᵒ

-- ↪⇛-use :  P˂ .! ∗ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ∞ ][ ṡ i ]⇛  Q˂ .!
---- The counter increment ṡ i makes the recursive call of ⊢⇛-sem inductive

⊢⇛-sem ↪⇛-use =  ∗ᵒ-monoʳ (↪⇛ᵒ-use › ⇛ᴵⁿᵈ⇒⇛ᵒ) › ⇛ᵒ-eatˡ ›
  ⇛ᵒ-mono (∗ᵒ∃ᵒ-out › ∑-case λ _ → ∗ᵒ∃ᵒ-out › ∑-case λ P∗R⊢⇛Q → ⊢⇛-sem P∗R⊢⇛Q) ›
  ⇛ᵒ-join
