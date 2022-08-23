--------------------------------------------------------------------------------
-- Hoare triple
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Hor where

open import Base.Size using (Size; ∞)
open import Base.Func using (_$_; const)
open import Base.Prod using (_,_; -,_)
open import Base.Sum using (inj₀; inj₁)
open import Syho.Logic.Prop using (Prop'; _∗_)
open import Syho.Logic.Core using (_⊢[_]_; _»_; ∗-comm)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_; ⊢⇒⊢⇛; ⇛-refl)
open import Syho.Lang.Expr using (Type; Expr; Val; _⁏_; let˙; val; val→*)
open import Syho.Lang.Ktxred using (ndᴿ; Ktx; •ᴷ; _◁ᴷʳ_; _⁏ᴷ_; _ᴷ|ᴿ_;
  Val/Ktxred)

-- Import and re-export
open import Syho.Logic.Judg public using (WpKind; par; tot; _⊢[_]⁺⟨_⟩[_]_;
  _⊢[_]⁺⟨_⟩ᴾ_; _⊢[_]⁺⟨_⟩ᵀ[_]_; _⊢[_]⟨_⟩[_]_; _⊢[_]⟨_⟩ᴾ_; _⊢[<_]⟨_⟩ᴾ_;
  _⊢[_]⟨_⟩ᵀ[_]_; _⊢[<_]⟨_⟩ᵀ[_]_; hor-ᵀ⇒ᴾ; horᵀ-suc; _ᵘ»ʰ_; _ʰ»ᵘ_; hor-frameˡ;
  hor-bind; hor-valᵘ; hor-nd; horᴾ-▶; horᵀ-▶; hor-◁; hor-⁏ᴿ; hor-🞰; hor-←;
  hor-alloc; hor-free)

private variable
  ι :  Size
  A :  Set₀
  T U :  Type
  wκ :  WpKind
  P P' Q R :  Prop' ∞
  Qᵛ Q'ᵛ Rᵛ :  Val T → Prop' ∞
  vk :  Val/Ktxred T
  ktx :  Ktx U T
  e e' e₀ :  Expr ∞ T
  e˙ :  A → Expr ∞ T
  v :  Val T

infixr -1 _ʰ»_

abstract

  -->  hor-ᵀ⇒ᴾ :  P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ  Qᵛ  →   P  ⊢[ ι ]⁺⟨ vk ⟩ᴾ  Qᵛ

  -->  horᵀ-suc :  P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ i ]  Qᵛ  →
  -->              P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ suc i ]  Qᵛ

  -->  hor-bind :  P  ⊢[ ι ]⟨ e ⟩[ wκ ]  Qᵛ  →
  -->              (∀ v →  Qᵛ v  ⊢[ ι ]⟨ ktx ᴷ◁ V⇒E v ⟩[ wκ ]  Rᵛ)  →
  -->              P  ⊢[ ι ]⟨ ktx ᴷ◁ e ⟩[ wκ ]  Rᵛ

  -->  hor-nd :  (∀ x →  P  ⊢[ ι ]⟨ ktx ᴷ◁ ∇ x ⟩[ wκ ]  Qᵛ)  →
  -->            P  ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ ndᴿ ⟩[ wκ ]  Qᵛ

  -->  horᴾ-▶ :  P  ⊢[< ι ]⟨ ktx ᴷ◁ e˂ .! ⟩ᴾ  Qᵛ  →
  -->            P  ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ ▶ᴿ e˂ ⟩ᴾ  Qᵛ

  -->  horᵀ-▶ :  P  ⊢[ ι ]⟨ ktx ᴷ◁ e˂ .! ⟩ᵀ[ i ]  Qᵛ  →
  -->            P  ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ ▶ᴿ e˂ ⟩ᵀ[ i ]  Qᵛ

  -->  hor-◁ :  P  ⊢[ ι ]⟨ ktx ᴷ◁ e˙ x ⟩[ wκ ]  Qᵛ  →
  -->           P  ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ e˙ ◁ᴿ x ⟩[ wκ ]  Qᵛ

  -->  hor-🞰 :  θ ↦⟨ p ⟩ (V , v)  ∗  P  ⊢[ ι ]⟨ ktx ᴷ◁ V⇒E v ⟩[ wκ ]  Qᵛ  →
  -->           θ ↦⟨ p ⟩ (-, v)  ∗  P  ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ 🞰ᴿ θ ⟩[ wκ ]  Qᵛ

  -->  hor-← :  θ ↦ (V , v)  ∗  P  ⊢[ ι ]⟨ ktx ᴷ◁ ∇ _ ⟩[ wκ ]  Qᵛ  →
  -->           θ ↦ av  ∗  P  ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ θ ←ᴿ v ⟩[ wκ ]  Qᵛ

  -->  hor-alloc :
  -->    (∀ θ →  θ ↦ˡ rep n ⊤-val  ∗  Free n θ  ∗  P
  -->              ⊢[ ι ]⟨ ktx ᴷ◁ ∇ θ ⟩[ wκ ]  Qᵛ)  →
  -->    P  ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ allocᴿ n ⟩[ wκ ]  Qᵛ

  -->  hor-free :
  -->    len avs ≡ n →  P  ⊢[ ι ]⟨ ktx ᴷ◁ ∇ _ ⟩[ wκ ]  Qᵛ  →
  -->    θ ↦ˡ avs  ∗  Free n θ  ∗  P
  -->      ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ freeᴿ θ ⟩[ wκ ]  Qᵛ

  -- Compose

  -->  _ᵘ»ʰ_ :  P  ⊢[ ι ][ i ]⇛  Q  →   Q  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  Rᵛ  →
  -->           P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  Rᵛ

  -->  _ʰ»ᵘ_ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  Qᵛ  →
  -->           (∀ v →  Qᵛ v  ⊢[ ι ][ i ]⇛  Rᵛ v)  →
  -->           P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  Rᵛ

  _ʰ»_ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  Qᵛ  →   (∀ v →  Qᵛ v  ⊢[ ι ]  Rᵛ v)  →
          P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  Rᵛ
  P⊢⟨vk⟩Q ʰ» ∀vQ⊢R =  P⊢⟨vk⟩Q ʰ»ᵘ λ _ → ⊢⇒⊢⇛ {i = 0} $ ∀vQ⊢R _

  -- Frame

  -->  hor-frameˡ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  Qᵛ  →
  -->                R  ∗  P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  λ v →  R  ∗  Qᵛ v

  hor-frameʳ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  Qᵛ  →
                P  ∗  R  ⊢[ ι ]⁺⟨ vk ⟩[ wκ ]  λ v →  Qᵛ v  ∗  R
  hor-frameʳ P⊢⟨vk⟩Q =  ∗-comm » hor-frameˡ P⊢⟨vk⟩Q ʰ» λ _ → ∗-comm

  -- Value

  -->  hor-valᵘ :  P  ⊢[ ι ]⇛  Qᵛ v  →   P  ⊢[ ι ]⁺⟨ inj₀ v ⟩[ wκ ]  Qᵛ

  hor-val :  P  ⊢[ ι ]  Qᵛ v  →   P  ⊢[ ι ]⁺⟨ inj₀ v ⟩[ wκ ]  Qᵛ
  hor-val P⊢Q =  hor-valᵘ $ ⊢⇒⊢⇛ {i = 0} P⊢Q

  -- Sequential execution

  -->  hor-⁏ᴿ :  P  ⊢[ ι ]⟨ ktx ᴷ◁ e ⟩[ wκ ]  Qᵛ  →
  -->            P  ⊢[ ι ]⁺⟨ inj₁ $ ktx ᴷ|ᴿ v ⁏ᴿ e ⟩[ wκ ]  Qᵛ

  hor-⁏ :  P  ⊢[ ι ]⟨ e ⟩[ wκ ]  const Q  →   Q  ⊢[ ι ]⟨ e' ⟩[ wκ ]  Rᵛ  →
           P  ⊢[ ι ]⟨ e ⁏ e' ⟩[ wκ ]  Rᵛ
  hor-⁏ P⊢⟨e⟩Q Q⊢⟨e'⟩R =  hor-bind {ktx = •ᴷ ⁏ᴷ _} P⊢⟨e⟩Q
    λ{ (val _) → hor-⁏ᴿ Q⊢⟨e'⟩R; (val→* _) → hor-⁏ᴿ Q⊢⟨e'⟩R }

  -- Let binding

  hor-let :  P  ⊢[ ι ]⟨ e₀ ⟩[ wκ ]  Qᵛ  →
             (∀ x →  Qᵛ (val x)  ⊢[ ι ]⟨ e˙ x ⟩[ wκ ]  Rᵛ) →
             P  ⊢[ ι ]⟨ let˙ e₀ e˙ ⟩[ wκ ]  Rᵛ
  hor-let P⊢⟨e₀⟩Q ∀xQ⊢⟨e˙⟩R =
    hor-bind {ktx = _ ◁ᴷʳ •ᴷ} P⊢⟨e₀⟩Q λ{ (val x) → hor-◁ $ ∀xQ⊢⟨e˙⟩R x }
