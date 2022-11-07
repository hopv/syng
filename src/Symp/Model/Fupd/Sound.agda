--------------------------------------------------------------------------------
-- Prove the semantic soundness and adequacy of the fancy update
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Symp.Model.Fupd.Sound where

open import Base.Func using (_$_; _›_)
open import Base.Few using (absurd)
open import Base.Size using (∞; !)
open import Base.Prod using (∑-case; π₀; _,_)
open import Base.Nat using (ℕ)
open import Symp.Lang.Expr using (Heap)
open import Symp.Logic.Prop using (Name; SProp∞; ⊤'; ⌜_⌝; [⊤]ᴺ; [^_]ᴺ)
open import Symp.Logic.Core using (_»_; ∃-elim; ⊤-intro)
open import Symp.Logic.Fupd using (_⊢[_][_]⇛_; _⊢[_][_]⇛ᴺ_; ⇛-ṡ; ⤇⇒⇛; _ᵘ»ᵘ_;
  ⇛-frameʳ)
open import Symp.Logic.Names using (ᴺ⇒[^])
open import Symp.Logic.Ind using (○-new; □○-new-rec; ○-use; ⊸⇛-use)
open import Symp.Logic.Inv using (&ⁱ-new-rec; &ⁱ-open; ⅋ⁱ-close)
open import Symp.Logic.Bor using (&ᵐ-new; &ᵐ-open; ⅋ᵐ-close; ⟨†⟩-back)
open import Symp.Model.Prop.Base using (_⊨_; ∗ᵒ-monoʳ; ∗ᵒ∃ᵒ-out; -∗ᵒ-introˡ)
open import Symp.Model.Prop.Interp using (⸨_⸩)
open import Symp.Model.Prop.Sound using (⊢-sem)
open import Symp.Model.Fupd.Ind using (○ᵒ-new; □ᵒ○ᵒ-new-rec; ○ᵒ-use; ⊸⇛ᵒ-use)
open import Symp.Model.Fupd.Inv using (&ⁱᵒ-new-rec; &ⁱᵒ-open; ⅋ⁱᵒ-close)
open import Symp.Model.Fupd.Bor using (&ᵐᵒ-new; &ᵐᵒ-open; ⅋ᵐᵒ-close; ⟨†⟩ᵒ-back)
open import Symp.Model.Fupd.Interp using (⇛ᵒ_; ⇛ᴺᵒ_; ⇛ᴵⁿᵈ⇒⇛ᵒ; ⇛ᴵⁿᵛ⇒⇛ᵒ; ⇛ᴮᵒʳ⇒⇛ᵒ;
  ⇛ᵒ-mono; ⊨✓⇒⊨-⇛ᵒ; ⤇ᵒ⇒⇛ᵒ; ⇛ᵒ-join; ⇛ᵒ-eatˡ; ⇛ᵒ-adeq)

private variable
  P Q :  SProp∞
  i :  ℕ
  X :  Set₀
  nm :  Name

--------------------------------------------------------------------------------
-- ⊢⇛-sem :  Semantic soundness of the fancy update

abstract

  ⊢⇛-sem :  P ⊢[ ∞ ][ i ]⇛ Q →  ⸨ P ⸩ ⊨ ⇛ᵒ ⸨ Q ⸩

  -- _»_ :  P ⊢[ ∞ ] Q →  Q ⊢[ ∞ ][ i ]⇛ R →  P ⊢[ ∞ ][ i ]⇛ R

  ⊢⇛-sem (P⊢Q » Q⊢⇛R) =  ⊨✓⇒⊨-⇛ᵒ λ ✓∙ → ⊢-sem P⊢Q ✓∙ › ⊢⇛-sem Q⊢⇛R

  -- ∃-elim :  (∀ x →  P˙ x ⊢[ ∞ ][ i ]⇛ Q) →  ∃˙ P˙ ⊢[ ∞ ][ i ]⇛ Q

  ⊢⇛-sem (∃-elim Px⊢⇛Q) =   ∑-case λ x → ⊢⇛-sem (Px⊢⇛Q x)

  -- ⇛-ṡ :  P ⊢[< ∞ ][ i ]⇛ Q →  P ⊢[ ∞ ][ ṡ i ]⇛ Q

  ⊢⇛-sem (⇛-ṡ P⊢⇛Q) =  ⊢⇛-sem (P⊢⇛Q .!)

  -- ⤇⇒⇛ :  ⤇ P ⊢[ ∞ ][ i ]⇛ P

  ⊢⇛-sem ⤇⇒⇛ =  ⤇ᵒ⇒⇛ᵒ

  -- _ᵘ»ᵘ_ :  P ⊢[ ∞ ][ i ]⇛ Q →  Q ⊢[ ∞ ][ i ]⇛ R →  P ⊢[ ∞ ][ i ]⇛ R

  ⊢⇛-sem (P⊢⇛Q ᵘ»ᵘ Q⊢⇛R) =  ⊢⇛-sem P⊢⇛Q › ⇛ᵒ-mono (⊢⇛-sem Q⊢⇛R) › ⇛ᵒ-join

  -- ⇛-frameʳ :  P ⊢[ ∞ ][ i ]⇛ Q →  R ∗ P ⊢[ ∞ ][ i ]⇛ R ∗ Q

  ⊢⇛-sem (⇛-frameʳ Q⊢⇛R) =  ∗ᵒ-monoʳ (⊢⇛-sem Q⊢⇛R) › ⇛ᵒ-eatˡ

  -- ○-new :  P˂ .! ⊢[ ∞ ][ i ]⇛ ○ P˂

  ⊢⇛-sem ○-new =  ○ᵒ-new › ⇛ᴵⁿᵈ⇒⇛ᵒ

  -- □○-new-rec :  □ ○ P˂ -∗ □ P˂ .! ⊢[ ∞ ][ i ]⇛ □ ○ P˂

  ⊢⇛-sem □○-new-rec =  □ᵒ○ᵒ-new-rec › ⇛ᴵⁿᵈ⇒⇛ᵒ

  -- ○-use :  ○ P˂ ⊢[ ∞ ][ i ]⇛ P˂ .!

  ⊢⇛-sem ○-use =  ○ᵒ-use › ⇛ᴵⁿᵈ⇒⇛ᵒ

  -- ⊸⇛-use :  P˂ .!  ∗  (P˂ ⊸[ i ]⇛ Q˂)  ⊢[ ∞ ][ ṡ i ]⇛  Q˂ .!
  -- The level increment ṡ i makes the recursive call of ⊢⇛-sem inductive

  ⊢⇛-sem ⊸⇛-use =  ∗ᵒ-monoʳ (⊸⇛ᵒ-use › ⇛ᴵⁿᵈ⇒⇛ᵒ) › ⇛ᵒ-eatˡ ›
    ⇛ᵒ-mono (∗ᵒ∃ᵒ-out › ∑-case λ _ →
      ∗ᵒ∃ᵒ-out › ∑-case λ P∗R⊢⇛Q → ⊢⇛-sem P∗R⊢⇛Q) › ⇛ᵒ-join

  -- &ⁱ-new-rec :  &ⁱ⟨ nm ⟩ P˂ -∗ P˂ .!  ⊢[ ∞ ][ i ]⇛  &ⁱ⟨ nm ⟩ P˂

  ⊢⇛-sem &ⁱ-new-rec =  &ⁱᵒ-new-rec › ⇛ᴵⁿᵛ⇒⇛ᵒ

  -- &ⁱ-open :  &ⁱ⟨ nm ⟩ P˂  ∗  [^ nm ]ᴺ  ⊢[ ∞ ][ i ]⇛  P˂ .!  ∗  ⅋ⁱ⟨ nm ⟩ P˂

  ⊢⇛-sem &ⁱ-open =  &ⁱᵒ-open › ⇛ᴵⁿᵛ⇒⇛ᵒ

  -- ⅋ⁱ-close :  P˂ .!  ∗  ⅋ⁱ⟨ nm ⟩ P˂  ⊢[ ∞ ][ i ]⇛  [^ nm ]ᴺ

  ⊢⇛-sem ⅋ⁱ-close =  ⅋ⁱᵒ-close › ⇛ᴵⁿᵛ⇒⇛ᵒ

  -- &ᵐ-new :  P˂ .!  ⊢[ ∞ ][ i ]⇛  &ᵐ⟨ α ⟩ P˂  ∗  ⟨† α ⟩ P˂

  ⊢⇛-sem &ᵐ-new =  &ᵐᵒ-new › ⇛ᴮᵒʳ⇒⇛ᵒ

  -- &ᵐ-open :
  --   [ α ]ᴸ⟨ p ⟩  ∗  &ᵐ⟨ α ⟩ P˂  ⊢[ ∞ ][ i ]⇛  P˂ .!  ∗  ⅋ᵐ⟨ α , p ⟩ P˂

  ⊢⇛-sem &ᵐ-open =  &ᵐᵒ-open › ⇛ᴮᵒʳ⇒⇛ᵒ

  -- ⅋ᵐ-close :
  --   P˂ .!  ∗  ⅋ᵐ⟨ α , p ⟩ P˂  ⊢[ ∞ ][ i ]⇛  [ α ]ᴸ⟨ p ⟩  ∗  &ᵐ⟨ α ⟩ P˂

  ⊢⇛-sem ⅋ᵐ-close =  ⅋ᵐᵒ-close › ⇛ᴮᵒʳ⇒⇛ᵒ

  -- ⟨†⟩-back :  †ᴸ α  ∗  ⟨† α ⟩ P˂  ⊢[ ∞ ][ i ]⇛  P˂ .!

  ⊢⇛-sem ⟨†⟩-back =  ⟨†⟩ᵒ-back › ⇛ᴮᵒʳ⇒⇛ᵒ

  -- Utility for ⇛ᴺ

  ⊢⇛ᴺ-sem :  P ⊢[ ∞ ][ i ]⇛ᴺ Q →  ⸨ P ⸩ ⊨ ⇛ᴺᵒ ⸨ Q ⸩
  ⊢⇛ᴺ-sem P⊢⇛Q =  -∗ᵒ-introˡ λ _ → ⊢⇛-sem P⊢⇛Q

--------------------------------------------------------------------------------
-- Aadequacy of the fancy update

abstract

  -- Under the premise [⊤]ᴺ

  ⊢⇛-adeqᴺ :  [⊤]ᴺ ⊢[ ∞ ][ i ]⇛ ⌜ X ⌝ →  X
  ⊢⇛-adeqᴺ ᴺ⊢⇛X =  ⇛ᵒ-adeq $ ⊢⇛-sem ᴺ⊢⇛X › ⇛ᵒ-mono π₀

  -- Under the premise [^ nm ]ᴺ

  ⊢⇛-adeq-[^]ᴺ :  [^ nm ]ᴺ ⊢[ ∞ ][ i ]⇛ ⌜ X ⌝ →  X
  ⊢⇛-adeq-[^]ᴺ [nm]⊢⇛X =  ⊢⇛-adeqᴺ $ ᴺ⇒[^] » [nm]⊢⇛X

  -- Under the trivial premise

  ⊢⇛-adeq :  ⊤' ⊢[ ∞ ][ i ]⇛ ⌜ X ⌝ →  X
  ⊢⇛-adeq ⊢⇛X =  ⊢⇛-adeqᴺ $ ⊤-intro » ⊢⇛X
