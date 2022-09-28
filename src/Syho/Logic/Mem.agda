--------------------------------------------------------------------------------
-- Memory
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Mem where

open import Base.Func using (_$_)
open import Base.Eq using (_≡_; refl)
open import Base.Size using (Size; ∞)
open import Base.Prod using (_,_; -,_)
open import Base.Sum using (ĩ₁_)
open import Base.Nat using (ℕ)
open import Base.List using (List; len; rep)
open import Base.RatPos using (ℚ⁺)
open import Syho.Lang.Expr using (Addr; Type; ∇_; Val; ṽ_; V⇒E; TyVal;
  ⊤ṽ)
open import Syho.Lang.Ktxred using (🞰ᴿ_; _←ᴿ_; allocᴿ; freeᴿ; Ktx; _ᴷ◁_)
open import Syho.Logic.Prop using (Prop'; _∗_; _↦⟨_⟩_; _↦_; _↦ᴸ_; Free)
open import Syho.Logic.Core using (_»_; ∗-assocˡ; ∗-assocʳ; ⊤∗-intro; ∗-elimʳ;
  ∃∗-elim)
open import Syho.Logic.Hor using (WpKind; _⊢[_]⁺⟨_⟩[_]_; _⊢[_]⟨_⟩[_]_;
  ahor-frameʳ; ahor-hor)

-- Import and re-export
open import Syho.Logic.Judg public using (↦⟨⟩-agree; ↦⟨⟩-≤1; ↦⟨⟩-merge;
  ↦⟨⟩-split; ahor-🞰; ahor-←; ahor-alloc; ahor-free)

private variable
  ι :  Size
  T U :  Type
  wκ :  WpKind
  K :  Ktx T U
  n :  ℕ
  p :  ℚ⁺
  θ :  Addr
  v :  Val T
  ᵗu :  TyVal
  ᵗvs :  List TyVal
  P :  Prop' ∞
  Q˙ :  Val T → Prop' ∞

abstract

  -->  ↦⟨⟩-agree :  θ ↦⟨ p ⟩ ᵗu  ∗  θ ↦⟨ q ⟩ ᵗv  ⊢[ ι ]  ⌜ ᵗu ≡ ᵗv ⌝

  -->  ↦⟨⟩-≤1 :  θ ↦⟨ p ⟩ ᵗv  ⊢[ ι ]  ⌜ p ≤1ᴿ⁺ ⌝

  -->  ↦⟨⟩-merge :  θ ↦⟨ p ⟩ ᵗv  ∗  θ ↦⟨ q ⟩ ᵗv  ⊢[ ι ]  θ ↦⟨ p +ᴿ⁺ q ⟩ ᵗv

  -->  ↦⟨⟩-split :  θ ↦⟨ p +ᴿ⁺ q ⟩ ᵗv  ⊢[ ι ]  θ ↦⟨ p ⟩ ᵗv  ∗  θ ↦⟨ q ⟩ ᵗv

  -- Memory read

  -->  ahor-🞰 :  θ ↦⟨ p ⟩ (-, v)  ⊢[ ι ][ i ]ᵃ⟨ 🞰ᴿ θ ⟩ λ u →
  -->              ⌜ u ≡ v ⌝∧  θ ↦⟨ p ⟩ (-, v)

  hor-🞰 :  θ ↦⟨ p ⟩ (-, v)  ∗  P  ⊢[ ι ]⟨ K ᴷ◁ V⇒E v ⟩[ wκ ]  Q˙  →
           θ ↦⟨ p ⟩ (-, v)  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , 🞰ᴿ θ) ⟩[ wκ ]  Q˙
  hor-🞰 θ↦v∗P⊢⟨Kv⟩Q =  ahor-hor (ahor-frameʳ $ ahor-frameʳ $ ahor-🞰 {i = 0})
    λ v →  ∃∗-elim λ{ refl → θ↦v∗P⊢⟨Kv⟩Q }

  -- Memory write

  -->  ahor-← :  θ ↦ ᵗu  ⊢[ ι ][ i ]ᵃ⟨ θ ←ᴿ v ⟩ λ _ →  θ ↦ (-, v)

  hor-← :  θ ↦ (-, v)  ∗  P  ⊢[ ι ]⟨ K ᴷ◁ ∇ _ ⟩[ wκ ]  Q˙  →
           θ ↦ ᵗu  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , θ ←ᴿ v) ⟩[ wκ ]  Q˙
  hor-← θ↦v∗P⊢⟨K⟩Q =  ahor-hor (ahor-frameʳ $ ahor-frameʳ $ ahor-← {i = 0})
    λ{ (ṽ _) → θ↦v∗P⊢⟨K⟩Q }

  -- Memory allocation

  -->  ahor-alloc :  ⊤'  ⊢[ ι ][ i ]ᵃ⟨ allocᴿ n ⟩ λᵛ θ ,
  -->                  θ ↦ᴸ rep n ⊤ṽ  ∗  Free n θ

  hor-alloc :
    (∀ θ →  θ ↦ᴸ rep n ⊤ṽ  ∗  Free n θ  ∗  P  ⊢[ ι ]⟨ K ᴷ◁ ∇ θ ⟩[ wκ ]  Q˙)  →
    P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , allocᴿ n) ⟩[ wκ ]  Q˙
  hor-alloc θ↦∗Freeθ∗P⊢⟨Kθ⟩Q =  ahor-hor
    (ahor-frameʳ $ ⊤∗-intro » ahor-frameʳ $ ahor-alloc {i = 0})
    λ{ (ṽ θ) → ∗-assocˡ » θ↦∗Freeθ∗P⊢⟨Kθ⟩Q θ }

  -- Memory freeing

  -->  ahor-free :  len ᵗvs ≡ n  →
  -->    θ ↦ᴸ ᵗvs  ∗  Free n θ  ⊢[ ι ][ i ]ᵃ⟨ freeᴿ θ ⟩ λ _ →  ⊤'

  hor-free :  len ᵗvs ≡ n  →   P  ⊢[ ι ]⟨ K ᴷ◁ ∇ _ ⟩[ wκ ]  Q˙  →
     θ ↦ᴸ ᵗvs  ∗  Free n θ  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , freeᴿ θ) ⟩[ wκ ]  Q˙
  hor-free lenvs≡n P⊢⟨K⟩Q =  ∗-assocʳ » ahor-hor
    (ahor-frameʳ $ ahor-frameʳ $ ahor-free {i = 0} lenvs≡n) $
    λ{ (ṽ θ) → ∗-elimʳ » P⊢⟨K⟩Q }
