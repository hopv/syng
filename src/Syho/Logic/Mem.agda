--------------------------------------------------------------------------------
-- Memory
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Mem where

-- Import and re-export
open import Syho.Logic.Judg public using (↦⟨⟩-agree; ↦⟨⟩-≤1; ↦⟨⟩-merge;
  ↦⟨⟩-split; hor-🞰; hor-←; hor-alloc; hor-free)

  -->  ↦⟨⟩-agree :  θ ↦⟨ p ⟩ av ∗ θ ↦⟨ q ⟩ av' ⊢[ ι ]  ⌜ av ≡ av' ⌝₁

  -->  ↦⟨⟩-≤1 :  θ ↦⟨ p ⟩ av ⊢[ ι ]  ⌜ p ≤1ᴿ⁺ ⌝₀

  -->  ↦⟨⟩-merge :  θ ↦⟨ p ⟩ av ∗ θ ↦⟨ q ⟩ av ⊢[ ι ]  θ ↦⟨ p +ᴿ⁺ q ⟩ av

  -->  ↦⟨⟩-split :  θ ↦⟨ p +ᴿ⁺ q ⟩ av ⊢[ ι ]  θ ↦⟨ p ⟩ av ∗ θ ↦⟨ q ⟩ av

  -->  hor-🞰 :  θ ↦⟨ p ⟩ (V , v)  ∗  P  ⊢[ ι ]⟨ K ᴷ◁ V⇒E v ⟩[ wκ ]  Q˙  →
  -->           θ ↦⟨ p ⟩ (-, v)  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| 🞰ᴿ θ) ⟩[ wκ ]  Q˙

  -->  hor-← :  θ ↦ (V , v)  ∗  P  ⊢[ ι ]⟨ K ᴷ◁ ∇ _ ⟩[ wκ ]  Q˙  →
  -->           θ ↦ av  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| θ ←ᴿ v) ⟩[ wκ ]  Q˙

  -->  hor-alloc :
  -->    (∀ θ →  θ ↦ˡ rep n ⊤ṽ  ∗  Free n θ  ∗  P
  -->              ⊢[ ι ]⟨ K ᴷ◁ ∇ θ ⟩[ wκ ]  Q˙)  →
  -->    P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| allocᴿ n) ⟩[ wκ ]  Q˙

  -->  hor-free :
  -->    len avs ≡ n  →   P  ⊢[ ι ]⟨ K ᴷ◁ ∇ _ ⟩[ wκ ]  Q˙  →
  -->    θ ↦ˡ avs  ∗  Free n θ  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| freeᴿ θ) ⟩[ wκ ]  Q˙
