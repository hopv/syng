--------------------------------------------------------------------------------
-- Memory
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Mem where

-- Import and re-export
open import Syho.Logic.Judg public using (↦⟨⟩-agree; ↦⟨⟩-≤1; ↦⟨⟩-merge;
  ↦⟨⟩-split; hor-🞰; hor-←; hor-alloc; hor-free)

  -->  ↦⟨⟩-agree :  θ ↦⟨ p ⟩ ᵗu ∗ θ ↦⟨ q ⟩ ᵗv ⊢[ ι ]  ⌜ ᵗu ≡ ᵗv ⌝₁

  -->  ↦⟨⟩-≤1 :  θ ↦⟨ p ⟩ ᵗv ⊢[ ι ]  ⌜ p ≤1ᴿ⁺ ⌝₀

  -->  ↦⟨⟩-merge :  θ ↦⟨ p ⟩ ᵗv ∗ θ ↦⟨ q ⟩ ᵗv ⊢[ ι ]  θ ↦⟨ p +ᴿ⁺ q ⟩ ᵗv

  -->  ↦⟨⟩-split :  θ ↦⟨ p +ᴿ⁺ q ⟩ ᵗv ⊢[ ι ]  θ ↦⟨ p ⟩ ᵗv ∗ θ ↦⟨ q ⟩ ᵗv

  -->  hor-🞰 :  θ ↦⟨ p ⟩ (V , v)  ∗  P  ⊢[ ι ]⟨ K ᴷ◁ V⇒E v ⟩[ wκ ]  Q˙  →
  -->           θ ↦⟨ p ⟩ (-, v)  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| 🞰ᴿ θ) ⟩[ wκ ]  Q˙

  -->  hor-← :  θ ↦ (V , v)  ∗  P  ⊢[ ι ]⟨ K ᴷ◁ ∇ _ ⟩[ wκ ]  Q˙  →
  -->           θ ↦ ᵗv  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| θ ←ᴿ v) ⟩[ wκ ]  Q˙

  -->  hor-alloc :
  -->    (∀ θ →  θ ↦ˡ rep n ⊤ṽ  ∗  Free n θ  ∗  P
  -->              ⊢[ ι ]⟨ K ᴷ◁ ∇ θ ⟩[ wκ ]  Q˙)  →
  -->    P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| allocᴿ n) ⟩[ wκ ]  Q˙

  -->  hor-free :
  -->    len ᵗvs ≡ n  →   P  ⊢[ ι ]⟨ K ᴷ◁ ∇ _ ⟩[ wκ ]  Q˙  →
  -->    θ ↦ˡ ᵗvs  ∗  Free n θ  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| freeᴿ θ) ⟩[ wκ ]  Q˙
