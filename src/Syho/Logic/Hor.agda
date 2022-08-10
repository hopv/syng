--------------------------------------------------------------------------------
-- Hoare triple
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Hor where

open import Base.Level using (↑_)
open import Base.Size using (Size; ∞)
open import Base.Func using (_$_)
open import Base.Prod using (_,_)
open import Base.Sum using (inj₀; inj₁)
open import Syho.Logic.Prop using (Prop'; _∗_)
open import Syho.Logic.Core using (_⊢[_]_; _»_; ∗-comm)
open import Syho.Logic.Supd using (_⊢[_]=>>_; ⇒=>>; =>>-refl)
open import Syho.Lang.Expr using (Type; Expr; Val; let˙)
open import Syho.Lang.Ktxred using (ndᴿ; Ktx; •ᴷ; _◁ᴷʳ_; _ᴷ|ᴿ_; Val/Ktxred)

-- Import and re-export
open import Syho.Logic.Judg public using (WpKind; par; tot; Wp'; _⊢[_]'⟨_⟩[_]_;
  _⊢[_]'⟨_⟩ᴾ_; _⊢[_]'⟨_⟩ᵀ_; _⊢[_]⟨_⟩[_]_; _⊢[_]⟨_⟩ᴾ_; _⊢[<_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ_;
  hor-ᵀ⇒ᴾ; _ᵘ»ʰ_; _ʰ»ᵘ_; hor-frameˡ; hor-bind; hor-valᵘ; hor-ndᵘ; horᴾ-▶;
  horᵀ-▶; hor-◁)

private variable
  ι :  Size
  A :  Set₀
  T U :  Type
  wk :  WpKind
  P P' R :  Prop' ∞
  Qᵛ Q'ᵛ Rᵛ :  Val T → Prop' ∞
  vk :  Val/Ktxred T
  ktx :  Ktx U T
  e₀ :  Expr ∞ T
  e˙ :  A → Expr ∞ T

infixr -1 _ʰ»_

abstract

  -- Compose

  _ʰ»_ :  ∀{Qᵛ : Val T → _} →
    P ⊢[ ι ]'⟨ vk ⟩[ wk ] Qᵛ →  (∀ v → Qᵛ v ⊢[ ι ] Rᵛ v) →
    P ⊢[ ι ]'⟨ vk ⟩[ wk ] Rᵛ
  P⊢⟨vk⟩Q ʰ» ∀vQ⊢R =  P⊢⟨vk⟩Q ʰ»ᵘ λ _ → ⇒=>> $ ∀vQ⊢R _

  -- Frame

  hor-frameʳ :  ∀{Qᵛ : _} →  P ⊢[ ι ]'⟨ vk ⟩[ wk ] Qᵛ →
                             P ∗ R ⊢[ ι ]'⟨ vk ⟩[ wk ] λ v → Qᵛ v ∗ R
  hor-frameʳ P⊢⟨vk⟩Q =  ∗-comm » hor-frameˡ P⊢⟨vk⟩Q ʰ» λ _ → ∗-comm

  -- Non-deterministic value

  hor-nd :  (∀ x →  P ⊢[ ι ] Qᵛ (↑ x)) →
            P ⊢[ ι ]'⟨ inj₁ $ ktx ᴷ|ᴿ ndᴿ ⟩[ wk ] Qᵛ
  hor-nd ∀xP⊢Q =  hor-ndᵘ $ λ _ → ⇒=>> $ ∀xP⊢Q _

  -- Let binding

  hor-let :  ∀{Rᵛ : _} →
    P ⊢[ ι ]⟨ e₀ ⟩[ wk ] Qᵛ →  (∀ x → Qᵛ (↑ x) ⊢[ ι ]⟨ e˙ x ⟩[ wk ] Rᵛ) →
    P ⊢[ ι ]⟨ let˙ e₀ e˙ ⟩[ wk ] Rᵛ
  hor-let P⊢⟨e₀⟩Q ∀xQ⊢⟨e˙⟩R =
    hor-bind {ktx = _ ◁ᴷʳ •ᴷ} P⊢⟨e₀⟩Q $ λ (↑ x) → hor-◁ $ ∀xQ⊢⟨e˙⟩R x

  -- Value

  hor-val :  ∀{v : Val T} →  P ⊢[ ι ] Qᵛ v →  P ⊢[ ι ]'⟨ inj₀ v ⟩[ wk ] Qᵛ
  hor-val P⊢Q =  hor-valᵘ $ ⇒=>> P⊢Q
