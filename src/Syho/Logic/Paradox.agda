--------------------------------------------------------------------------------
-- Paradoxes on plausible proof rules
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Paradox where

open import Base.Size using (Size; ∞)
open import Base.Thunk using (¡_; !)
open import Base.Func using (_$_)
open import Base.Few using (0⊤)
open import Base.Nat using (ℕ)
open import Syho.Lang.Expr using (Type; Expr; Val)
open import Syho.Logic.Prop using (Prop'; Prop˂; ⊤'; ⊥'; □_; _∗_; ○_; _↪[_]⇛_;
  _↪⟨_⟩ᴾ_; _↪⟨_⟩ᵀ[_]_)
open import Syho.Logic.Core using (_⊢[_]_; _»_; -∗-intro; ∗-elimˡ; ∗⊤-intro;
  □-mono; □-elim)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_; _ᵘ»ᵘ_; _ᵘ»_; ⇛-frameˡ)
open import Syho.Logic.Hor using (_⊢[_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ[_]_; _ᵘ»ʰ_)
open import Syho.Logic.Ind using (○-mono; □○-alloc-rec; ○-use; ○⇒↪⇛; ○⇒↪⟨⟩ᴾ;
  ○⇒↪⟨⟩ᵀ)

private variable
  ι :  Size
  i :  ℕ
  T :  Type
  e :  Expr ∞ T
  P Q :  Prop' ∞
  P˂ Q˂ :  Prop˂ ∞
  Qᵛ :  Val T → Prop' ∞
  Q˂ᵛ :  Val T → Prop˂ ∞

--------------------------------------------------------------------------------
-- Utility

-- If we can turn ○ P into P, then we get P after a super update,
-- thanks to □○-alloc-rec

○-rec :  ○ ¡ P ⊢[ ι ] P →  ⊤' ⊢[ ι ][ i ]⇛ P
○-rec {P} ○P⊢P =  -∗-intro (∗-elimˡ » □-mono $ ○-mono (¡ □-elim) » ○P⊢P) »
    □○-alloc-rec {P˂ = ¡ □ P} ᵘ»ᵘ □-elim » ○-use ᵘ» □-elim

--------------------------------------------------------------------------------
-- If we can use ↪⇛ without counter increment, then we get a paradox

module _
  -- ↪⇛-use without counter increment
  (↪⇛-use' :  ∀{P˂ Q˂ ι i} →
    P˂ .! ∗ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ][ i ]⇛  Q˂ .!)
  where abstract

  -- We can strip ○ from ↪⇛, using ↪⇛-use'

  ○⇒-↪⇛/↪⇛-use' :  ○ ¡ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ]  P˂ ↪[ i ]⇛ Q˂
  ○⇒-↪⇛/↪⇛-use' =  ○⇒↪⇛ λ{ .! → ↪⇛-use' }

  -- Therefore, by ○-rec, we can do any super update --- a paradox!

  ⇛/↪⇛-use' :  P ⊢[ ι ][ i ]⇛ Q
  ⇛/↪⇛-use' {P} {Q = Q} =  ∗⊤-intro »
    ⇛-frameˡ (○-rec ○⇒-↪⇛/↪⇛-use') ᵘ»ᵘ ↪⇛-use' {¡ P} {¡ Q}

--------------------------------------------------------------------------------
-- If we can use ↪⟨ ⟩ᴾ without ▶, then we get a paradox

module _
  -- ↪⟨⟩ᴾ-use without ▶
  (↪⟨⟩ᴾ-use' :  ∀{e : Expr ∞ T} {P˂ Q˂ᵛ ι} →
    P˂ .! ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ)  ⊢[ ι ]⟨ e ⟩ᴾ  λ v → Q˂ᵛ v .!)
  where abstract

  -- We can strip ○ from ↪⟨⟩ᴾ, using ↪⟨⟩ᴾ-use'

  ○⇒-↪⟨⟩ᴾ/↪⟨⟩ᴾ-use' :  ∀{e : Expr ∞ T} →
    ○ ¡ (P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ)  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ
  ○⇒-↪⟨⟩ᴾ/↪⟨⟩ᴾ-use' =  ○⇒↪⟨⟩ᴾ λ{ .! → ↪⟨⟩ᴾ-use' }

  -- Therefore, by ○-rec, we have any partial Hoare triple --- a paradox!

  horᴾ/↪⟨⟩ᴾ-use' :  ∀{e : Expr ∞ T} →  P ⊢[ ι ]⟨ e ⟩ᴾ Qᵛ
  horᴾ/↪⟨⟩ᴾ-use' {P} {Qᵛ = Qᵛ} =  ∗⊤-intro »
    ⇛-frameˡ (○-rec {i = 0} ○⇒-↪⟨⟩ᴾ/↪⟨⟩ᴾ-use') ᵘ»ʰ
    ↪⟨⟩ᴾ-use' {P˂ = ¡ P} {λ v → ¡ Qᵛ v}

--------------------------------------------------------------------------------
-- If we can use ↪⟨ ⟩ᵀ without counter increment, then we get a paradox

module _
  -- ↪⟨⟩ᵀ-use without counter increment
  (↪⟨⟩ᵀ-use' :  ∀{e : Expr ∞ T} {P˂ Q˂ᵛ i ι} →
    P˂ .! ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ)  ⊢[ ι ]⟨ e ⟩ᵀ[ i ]  λ v → Q˂ᵛ v .!)
  where abstract

  -- We can strip ○ from ↪⟨⟩ᵀ, using ↪⟨⟩ᵀ-use'

  ○⇒-↪⟨⟩ᵀ/↪⟨⟩ᵀ-use' :  ∀{e : Expr ∞ T} →
    ○ ¡ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ)  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ
  ○⇒-↪⟨⟩ᵀ/↪⟨⟩ᵀ-use' =  ○⇒↪⟨⟩ᵀ λ{ .! → ↪⟨⟩ᵀ-use' }

  -- Therefore, by ○-rec, we have any total Hoare triple --- a paradox!

  horᵀ/↪⟨⟩ᵀ-use' :  ∀{e : Expr ∞ T} →  P ⊢[ ι ]⟨ e ⟩ᵀ[ i ] Qᵛ
  horᵀ/↪⟨⟩ᵀ-use' {P} {Qᵛ = Qᵛ} =  ∗⊤-intro »
    ⇛-frameˡ (○-rec {i = 0} ○⇒-↪⟨⟩ᵀ/↪⟨⟩ᵀ-use') ᵘ»ʰ
    ↪⟨⟩ᵀ-use' {P˂ = ¡ P} {λ v → ¡ Qᵛ v}
