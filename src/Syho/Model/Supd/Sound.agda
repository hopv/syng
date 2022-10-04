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
open import Syho.Logic.Prop using (Prop∞)
open import Syho.Logic.Core using (_»_; ∃-elim)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_; ⇛-ṡ; ⇛-refl-⤇; _ᵘ»ᵘ_; ⇛-frameˡ)
open import Syho.Logic.Ind using (○-alloc; □○-alloc-rec; ○-use; ↪⇛-use)
open import Syho.Logic.Inv using (Inv-alloc-rec; Inv-open; OInv-close)
open import Syho.Model.Prop.Base using (_⊨_; ∗ᵒ-monoʳ; ∗ᵒ∃ᵒ-out)
open import Syho.Model.Prop.Interp using (⸨_⸩)
open import Syho.Model.Prop.Sound using (⊢-sem)
open import Syho.Model.Supd.Ind using (○ᵒ-alloc; □ᵒ○ᵒ-alloc-rec; ○ᵒ-use;
  ↪⇛ᵒ-use)
open import Syho.Model.Supd.Inv using (Invᵒ-alloc-rec; Invᵒ-open; OInvᵒ-close)
open import Syho.Model.Supd.Interp using (⇛ᵒᶠ_; ⇛ᴵⁿᵈ⇒⇛ᵒᶠ; ⇛ᴵⁿᵛ⇒⇛ᵒᶠ; ⇛ᵒᶠ-mono;
  ⊨✓⇒⊨-⇛ᵒᶠ; ⤇ᵒ⇒⇛ᵒᶠ; ⇛ᵒᶠ-join; ⇛ᵒᶠ-eatˡ)

private variable
  P Q :  Prop∞
  i :  ℕ
  M :  Mem

--------------------------------------------------------------------------------
-- ⊢⇛-sem :  Semantic soundness of the super update

⊢⇛-sem :  P ⊢[ ∞ ][ i ]⇛ Q →  ⸨ P ⸩ ⊨ ⇛ᵒᶠ ⸨ Q ⸩

-- _»_ :  P ⊢[ ∞ ] Q →  Q ⊢[ ∞ ][ i ]⇛ R →  P ⊢[ ∞ ][ i ]⇛ R

⊢⇛-sem (P⊢Q » Q⊢⇛R) =  ⊨✓⇒⊨-⇛ᵒᶠ λ ✓∙ → ⊢-sem P⊢Q ✓∙ › ⊢⇛-sem Q⊢⇛R

-- ∃-elim :  (∀ x →  P˙ x ⊢[ ∞ ][ i ]⇛ Q) →  ∃˙ P˙ ⊢[ ∞ ][ i ]⇛ Q

⊢⇛-sem (∃-elim Px⊢⇛Q) =   ∑-case λ x → ⊢⇛-sem (Px⊢⇛Q x)

-- ⇛-ṡ :  P ⊢[ ∞ ][ i ]⇛ Q →  P ⊢[ ∞ ][ ṡ i ]⇛ Q

⊢⇛-sem (⇛-ṡ P⊢⇛Q) =  ⊢⇛-sem P⊢⇛Q

-- ⇛-refl-⤇ :  ⤇ P ⊢[ ∞ ][ i ]⇛ P

⊢⇛-sem ⇛-refl-⤇ =  ⤇ᵒ⇒⇛ᵒᶠ

-- _ᵘ»ᵘ_ :  P ⊢[ ∞ ][ i ]⇛ Q →  Q ⊢[ ∞ ][ i ]⇛ R →  P ⊢[ ∞ ][ i ]⇛ R

⊢⇛-sem (P⊢⇛Q ᵘ»ᵘ Q⊢⇛R) =  ⊢⇛-sem P⊢⇛Q › ⇛ᵒᶠ-mono (⊢⇛-sem Q⊢⇛R) › ⇛ᵒᶠ-join

-- ⇛-frameˡ :  P ⊢[ ∞ ][ i ]⇛ Q →  R ∗ P ⊢[ ∞ ][ i ]⇛ R ∗ Q

⊢⇛-sem (⇛-frameˡ Q⊢⇛R) =  ∗ᵒ-monoʳ (⊢⇛-sem Q⊢⇛R) › ⇛ᵒᶠ-eatˡ

-- ○-alloc :  P˂ .! ⊢[ ∞ ][ i ]⇛ ○ P˂

⊢⇛-sem ○-alloc =  ○ᵒ-alloc › ⇛ᴵⁿᵈ⇒⇛ᵒᶠ

-- □○-alloc-rec :  □ ○ P˂ -∗ □ P˂ .! ⊢[ ∞ ][ i ]⇛ □ ○ P˂

⊢⇛-sem □○-alloc-rec =  □ᵒ○ᵒ-alloc-rec › ⇛ᴵⁿᵈ⇒⇛ᵒᶠ

-- ○-use :  ○ P˂ ⊢[ ∞ ][ i ]⇛ P˂ .!

⊢⇛-sem ○-use =  ○ᵒ-use › ⇛ᴵⁿᵈ⇒⇛ᵒᶠ

-- ↪⇛-use :  P˂ .!  ∗  (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ∞ ][ ṡ i ]⇛  Q˂ .!
-- The counter increment ṡ i makes the recursive call of ⊢⇛-sem inductive

⊢⇛-sem ↪⇛-use =  ∗ᵒ-monoʳ (↪⇛ᵒ-use › ⇛ᴵⁿᵈ⇒⇛ᵒᶠ) › ⇛ᵒᶠ-eatˡ ›
  ⇛ᵒᶠ-mono (∗ᵒ∃ᵒ-out › ∑-case λ _ →
    ∗ᵒ∃ᵒ-out › ∑-case λ P∗R⊢⇛Q → ⊢⇛-sem P∗R⊢⇛Q) › ⇛ᵒᶠ-join

-- Inv-alloc-rec :  Inv nm P˂ -∗ P˂ .!  ⊢[ ∞ ][ i ]⇛  Inv nm P˂

⊢⇛-sem Inv-alloc-rec =  Invᵒ-alloc-rec › ⇛ᴵⁿᵛ⇒⇛ᵒᶠ

-- Inv-open :  Inv nm P˂  ∗  [^ nm ]ᴺ  ⊢[ ∞ ][ i ]⇛  P˂ .!  ∗  OInv nm P˂

⊢⇛-sem Inv-open =  Invᵒ-open › ⇛ᴵⁿᵛ⇒⇛ᵒᶠ

-- OInv-close :  P˂ .!  ∗  OInv nm P˂  ⊢[ ∞ ][ i ]⇛  [^ nm ]ᴺ

⊢⇛-sem OInv-close =  OInvᵒ-close › ⇛ᴵⁿᵛ⇒⇛ᵒᶠ
