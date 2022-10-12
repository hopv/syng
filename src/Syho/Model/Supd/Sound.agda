--------------------------------------------------------------------------------
-- Prove the semantic soundness of the super update
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Sound where

open import Base.Func using (_›_)
open import Base.Size using (∞; !)
open import Base.Prod using (∑-case; _,_)
open import Base.Nat using (ℕ)
open import Syho.Lang.Expr using (Mem)
open import Syho.Logic.Prop using (Prop∞)
open import Syho.Logic.Core using (_»_; ∃-elim)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_; _⊢[_][_]⇛ᴺ_; ⇛-ṡ; ⇛-refl-⤇;
  _ᵘ»ᵘ_; ⇛-frameˡ)
open import Syho.Logic.Ind using (○-new; □○-new-rec; ○-use; ↪⇛-use)
open import Syho.Logic.Inv using (&ⁱ-new-rec; &ⁱ-open; %ⁱ-close)
open import Syho.Logic.Bor using (⟨†⟩-back; &ˢ-new; &ˢ-open; %ˢ-close)
open import Syho.Model.Prop.Base using (_⊨_; ∗ᵒ-monoʳ; ∗ᵒ∃ᵒ-out; -∗ᵒ-introˡ)
open import Syho.Model.Prop.Interp using (⸨_⸩)
open import Syho.Model.Prop.Sound using (⊢-sem)
open import Syho.Model.Supd.Ind using (○ᵒ-new; □ᵒ○ᵒ-new-rec; ○ᵒ-use; ↪⇛ᵒ-use)
open import Syho.Model.Supd.Inv using (&ⁱᵒ-new-rec; &ⁱᵒ-open; %ⁱᵒ-close)
open import Syho.Model.Supd.Interp using (⇛ᵒ_; ⇛ᴺᵒ_; ⇛ᴵⁿᵈ⇒⇛ᵒ; ⇛ᴵⁿᵛ⇒⇛ᵒ; ⇛ᵒ-mono;
  ⊨✓⇒⊨-⇛ᵒ; ⤇ᵒ⇒⇛ᵒ; ⇛ᵒ-join; ⇛ᵒ-eatˡ)

private variable
  P Q :  Prop∞
  i :  ℕ
  M :  Mem

postulate
  WIP :  ∀{ł} {A : Set ł} →  A  -- Just for now

--------------------------------------------------------------------------------
-- ⊢⇛-sem :  Semantic soundness of the super update

abstract

  ⊢⇛-sem :  P ⊢[ ∞ ][ i ]⇛ Q →  ⸨ P ⸩ ⊨ ⇛ᵒ ⸨ Q ⸩

  -- _»_ :  P ⊢[ ∞ ] Q →  Q ⊢[ ∞ ][ i ]⇛ R →  P ⊢[ ∞ ][ i ]⇛ R

  ⊢⇛-sem (P⊢Q » Q⊢⇛R) =  ⊨✓⇒⊨-⇛ᵒ λ ✓∙ → ⊢-sem P⊢Q ✓∙ › ⊢⇛-sem Q⊢⇛R

  -- ∃-elim :  (∀ x →  P˙ x ⊢[ ∞ ][ i ]⇛ Q) →  ∃˙ P˙ ⊢[ ∞ ][ i ]⇛ Q

  ⊢⇛-sem (∃-elim Px⊢⇛Q) =   ∑-case λ x → ⊢⇛-sem (Px⊢⇛Q x)

  -- ⇛-ṡ :  P ⊢[< ∞ ][ i ]⇛ Q →  P ⊢[ ∞ ][ ṡ i ]⇛ Q

  ⊢⇛-sem (⇛-ṡ P⊢⇛Q) =  ⊢⇛-sem (P⊢⇛Q .!)

  -- ⇛-refl-⤇ :  ⤇ P ⊢[ ∞ ][ i ]⇛ P

  ⊢⇛-sem ⇛-refl-⤇ =  ⤇ᵒ⇒⇛ᵒ

  -- _ᵘ»ᵘ_ :  P ⊢[ ∞ ][ i ]⇛ Q →  Q ⊢[ ∞ ][ i ]⇛ R →  P ⊢[ ∞ ][ i ]⇛ R

  ⊢⇛-sem (P⊢⇛Q ᵘ»ᵘ Q⊢⇛R) =  ⊢⇛-sem P⊢⇛Q › ⇛ᵒ-mono (⊢⇛-sem Q⊢⇛R) › ⇛ᵒ-join

  -- ⇛-frameˡ :  P ⊢[ ∞ ][ i ]⇛ Q →  R ∗ P ⊢[ ∞ ][ i ]⇛ R ∗ Q

  ⊢⇛-sem (⇛-frameˡ Q⊢⇛R) =  ∗ᵒ-monoʳ (⊢⇛-sem Q⊢⇛R) › ⇛ᵒ-eatˡ

  -- ○-new :  P˂ .! ⊢[ ∞ ][ i ]⇛ ○ P˂

  ⊢⇛-sem ○-new =  ○ᵒ-new › ⇛ᴵⁿᵈ⇒⇛ᵒ

  -- □○-new-rec :  □ ○ P˂ -∗ □ P˂ .! ⊢[ ∞ ][ i ]⇛ □ ○ P˂

  ⊢⇛-sem □○-new-rec =  □ᵒ○ᵒ-new-rec › ⇛ᴵⁿᵈ⇒⇛ᵒ

  -- ○-use :  ○ P˂ ⊢[ ∞ ][ i ]⇛ P˂ .!

  ⊢⇛-sem ○-use =  ○ᵒ-use › ⇛ᴵⁿᵈ⇒⇛ᵒ

  -- ↪⇛-use :  P˂ .!  ∗  (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ∞ ][ ṡ i ]⇛  Q˂ .!
  -- The level increment ṡ i makes the recursive call of ⊢⇛-sem inductive

  ⊢⇛-sem ↪⇛-use =  ∗ᵒ-monoʳ (↪⇛ᵒ-use › ⇛ᴵⁿᵈ⇒⇛ᵒ) › ⇛ᵒ-eatˡ ›
    ⇛ᵒ-mono (∗ᵒ∃ᵒ-out › ∑-case λ _ →
      ∗ᵒ∃ᵒ-out › ∑-case λ P∗R⊢⇛Q → ⊢⇛-sem P∗R⊢⇛Q) › ⇛ᵒ-join

  -- &ⁱ-new-rec :  &ⁱ⟨ nm ⟩ P˂ -∗ P˂ .!  ⊢[ ∞ ][ i ]⇛  &ⁱ⟨ nm ⟩ P˂

  ⊢⇛-sem &ⁱ-new-rec =  &ⁱᵒ-new-rec › ⇛ᴵⁿᵛ⇒⇛ᵒ

  -- &ⁱ-open :  &ⁱ⟨ nm ⟩ P˂  ∗  [^ nm ]ᴺ  ⊢[ ∞ ][ i ]⇛  P˂ .!  ∗  %ⁱ⟨ nm ⟩ P˂

  ⊢⇛-sem &ⁱ-open =  &ⁱᵒ-open › ⇛ᴵⁿᵛ⇒⇛ᵒ

  -- %ⁱ-close :  P˂ .!  ∗  %ⁱ⟨ nm ⟩ P˂  ⊢[ ∞ ][ i ]⇛  [^ nm ]ᴺ

  ⊢⇛-sem %ⁱ-close =  %ⁱᵒ-close › ⇛ᴵⁿᵛ⇒⇛ᵒ

  -- ⟨†⟩-back :  †ᴸ α  ∗  ⟨† α ⟩ P˂  ⊢[ ι ][ i ]⇛  P˂ .!

  ⊢⇛-sem ⟨†⟩-back =  WIP

  -- &ˢ-new :  P˂˙ 1ᴿ⁺ .!  ⊢[ ι ][ i ]⇛  &ˢ⟨ α ⟩ P˂˙  ∗  ⟨† α ⟩ P˂˙ 1ᴿ⁺

  ⊢⇛-sem &ˢ-new =  WIP

  -- &ˢ-open :  &ˢ⟨ α ⟩ P˂˙  ∗  [ α ]ᴸ⟨ p ⟩  ⊢[ ι ][ i ]⇛
  --              ∃ q ,  P˂˙ q .!  ∗  %ˢ⟨ α , p ⟩ P˂˙ q

  ⊢⇛-sem &ˢ-open =  WIP

  -- %ˢ-close :  P˂˙ q .!  ∗  %ˢ⟨ α , p ⟩ P˂˙ q  ⊢[ ι ][ i ]⇛  [ α ]ᴸ⟨ p ⟩

  ⊢⇛-sem %ˢ-close =  WIP

  -- Utility for ⇛ᴺ

  ⊢⇛ᴺ-sem :  P ⊢[ ∞ ][ i ]⇛ᴺ Q →  ⸨ P ⸩ ⊨ ⇛ᴺᵒ ⸨ Q ⸩
  ⊢⇛ᴺ-sem P⊢⇛Q =  -∗ᵒ-introˡ λ _ → ⊢⇛-sem P⊢⇛Q
