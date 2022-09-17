--------------------------------------------------------------------------------
-- Hoare triple
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Hor where

open import Base.Func using (_$_; const)
open import Base.Size using (Size; ∞)
open import Base.Prod using (_,_; -,_)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Syho.Logic.Prop using (Prop'; _∗_)
open import Syho.Logic.Core using (_⊢[_]_; _»_; ∗-comm)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_; ⊢⇒⊢⇛; ⇛-refl)
open import Syho.Lang.Expr using (Type; Expr; Val; _⁏_; let˙; ṽ_; ṽ↷_)
open import Syho.Lang.Ktxred using (ndᴿ; Ktx; •ᴷ; _◁ᴷʳ_; _⁏ᴷ_; _ᴷ|_;
  Val/Ktxred)

-- Import and re-export
open import Syho.Logic.Judg public using (WpKind; par; tot; ⁺⟨_⟩[_]_;
  _⊢[_]⁺⟨_⟩[_]_; _⊢[_]⁺⟨_⟩ᴾ_; _⊢[_]⁺⟨_⟩ᵀ[_]_; _⊢[_]⟨_⟩[_]_; _⊢[_]⟨_⟩ᴾ_;
  _⊢[<_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ[_]_; _⊢[<_]⟨_⟩ᵀ[_]_; hor-ᵀ⇒ᴾ; horᵀ-ṡ; _ᵘ»ʰ_; _ʰ»ᵘ_;
  hor-frameˡ; hor-bind; hor-valᵘ; hor-nd; horᴾ-▶; horᵀ-▶; hor-◁; hor-⁏)

private variable
  ι :  Size
  A :  Set₀
  T U :  Type
  wκ :  WpKind
  P P' Q R :  Prop' ∞
  Q˙ Q'˙ R˙ :  Val T → Prop' ∞
  vk :  Val/Ktxred T
  K :  Ktx U T
  e e' e₀ :  Expr ∞ T
  e˙ :  A → Expr ∞ T
  v :  Val T

infixr -1 _ʰ»_

abstract

  -->  hor-ᵀ⇒ᴾ :  P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ  Q˙  →   P  ⊢[ ι ]⁺⟨ vk ⟩ᴾ  Q˙

  -->  horᵀ-ṡ :  P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ i ]  Q˙  →
  -->              P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ ṡ i ]  Q˙

  -->  hor-bind :  P  ⊢[ ι ]⟨ e ⟩[ wκ ]  Q˙  →
  -->              (∀ v →  Q˙ v  ⊢[ ι ]⟨ K ᴷ◁ V⇒E v ⟩[ wκ ]  R˙)  →
  -->              P  ⊢[ ι ]⟨ K ᴷ◁ e ⟩[ wκ ]  R˙

  -->  hor-nd :  {{Inh X}} →  (∀(x : X) →  P  ⊢[ ι ]⟨ K ᴷ◁ ∇ x ⟩[ wκ ]  Q˙)  →
  -->            P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| ndᴿ) ⟩[ wκ ]  Q˙

  -->  horᴾ-▶ :  P  ⊢[< ι ]⟨ K ᴷ◁ e˂ .! ⟩ᴾ  Q˙  →
  -->            P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| ▶ᴿ e˂) ⟩ᴾ  Q˙

  -->  horᵀ-▶ :  P  ⊢[ ι ]⟨ K ᴷ◁ e˂ .! ⟩ᵀ[ i ]  Q˙  →
  -->            P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| ▶ᴿ e˂) ⟩ᵀ[ i ]  Q˙

  -->  hor-◁ :  P  ⊢[ ι ]⟨ K ᴷ◁ e˙ x ⟩[ wκ ]  Q˙  →
  -->           P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| e˙ ◁ᴿ x) ⟩[ wκ ]  Q˙

  -- Compose

  -->  _ᵘ»ʰ_ :  P  ⊢[ ι ][ i ]⇛  Q  →   Q  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  R˙  →
  -->           P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  R˙

  -->  _ʰ»ᵘ_ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  Q˙  →
  -->           (∀ v →  Q˙ v  ⊢[ ι ][ i ]⇛  R˙ v)  →
  -->           P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  R˙

  _ʰ»_ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  Q˙  →   (∀ v →  Q˙ v  ⊢[ ι ]  R˙ v)  →
          P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  R˙
  P⊢⟨vk⟩Q ʰ» ∀vQ⊢R =  P⊢⟨vk⟩Q ʰ»ᵘ λ _ → ⊢⇒⊢⇛ {i = 0} $ ∀vQ⊢R _

  -- Frame

  -->  hor-frameˡ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  Q˙  →
  -->                R  ∗  P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  λ v →  R  ∗  Q˙ v

  hor-frameʳ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  Q˙  →
                P  ∗  R  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  λ v →  Q˙ v  ∗  R
  hor-frameʳ P⊢⟨vk⟩Q =  ∗-comm » hor-frameˡ P⊢⟨vk⟩Q ʰ» λ _ → ∗-comm

  -- Value

  -->  hor-valᵘ :  P  ⊢[ ι ]⇛  Q˙ v  →   P  ⊢[ ι ]⁺⟨ ĩ₀ v ⟩[ wκ ]  Q˙

  hor-val :  P  ⊢[ ι ]  Q˙ v  →   P  ⊢[ ι ]⁺⟨ ĩ₀ v ⟩[ wκ ]  Q˙
  hor-val P⊢Q =  hor-valᵘ $ ⊢⇒⊢⇛ {i = 0} P⊢Q

  -- Sequential execution

  -->  hor-⁏ :  P  ⊢[ ι ]⟨ K ᴷ◁ e ⟩[ wκ ]  Q˙  →
  -->           P  ⊢[ ι ]⁺⟨ ĩ₁ (K ᴷ| v ⁏ᴿ e) ⟩[ wκ ]  Q˙

  hor-⁏-bind :  P  ⊢[ ι ]⟨ e ⟩[ wκ ]  const Q  →   Q  ⊢[ ι ]⟨ e' ⟩[ wκ ]  R˙  →
                P  ⊢[ ι ]⟨ e ⁏ e' ⟩[ wκ ]  R˙
  hor-⁏-bind P⊢⟨e⟩Q Q⊢⟨e'⟩R =  hor-bind {K = •ᴷ ⁏ᴷ _} P⊢⟨e⟩Q
    λ{ (ṽ _) → hor-⁏ Q⊢⟨e'⟩R; (ṽ↷ _) → hor-⁏ Q⊢⟨e'⟩R }

  -- Let binding

  hor-let-bind :  P  ⊢[ ι ]⟨ e₀ ⟩[ wκ ]  Q˙  →
                  (∀ x →  Q˙ (ṽ x)  ⊢[ ι ]⟨ e˙ x ⟩[ wκ ]  R˙) →
                  P  ⊢[ ι ]⟨ let˙ e₀ e˙ ⟩[ wκ ]  R˙
  hor-let-bind P⊢⟨e₀⟩Q ∀xQ⊢⟨e˙⟩R =
    hor-bind {K = _ ◁ᴷʳ •ᴷ} P⊢⟨e₀⟩Q λ{ (ṽ x) → hor-◁ $ ∀xQ⊢⟨e˙⟩R x }
