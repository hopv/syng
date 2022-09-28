--------------------------------------------------------------------------------
-- Paradoxes on plausible proof rules
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Paradox where

open import Base.Func using (_$_)
open import Base.Size using (Size; ∞; ¡_; !)
open import Base.Nat using (ℕ)
open import Syho.Lang.Expr using (Type; Expr; Expr˂; ▶_; loop; Val)
open import Syho.Logic.Prop using (Prop'; Prop˂; ⊤'; □_; _∗_; ○_; _↪[_]⇛_;
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
  Q˙ :  Val T →  Prop' ∞
  Q˂˙ :  Val T →  Prop˂ ∞

--------------------------------------------------------------------------------
-- Utility

-- If we can turn ○ P into P, then we get P after a super update,
-- thanks to □○-alloc-rec

○-rec :  ○ ¡ P ⊢[ ι ] P →  ⊤' ⊢[ ι ][ i ]⇛ P
○-rec ○P⊢P =  -∗-intro (∗-elimˡ » □-mono ○P⊢P) » □○-alloc-rec ᵘ»ᵘ □-elim » ○-use

--------------------------------------------------------------------------------
-- If we can use ↪⇛ without counter increment, then we get a paradox

module _
  -- ↪⇛-use without counter increment
  (↪⇛-use' :  ∀{P˂ Q˂ ι i} →  P˂ .! ∗ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ][ i ]⇛  Q˂ .!)
  where abstract

  -- We can strip ○ from ↪⇛, using ↪⇛-use'

  ○⇒-↪⇛/↪⇛-use' :  ○ ¡ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ]  P˂ ↪[ i ]⇛ Q˂
  ○⇒-↪⇛/↪⇛-use' =  ○⇒↪⇛ λ{ .! → ↪⇛-use' }

  -- Therefore, by ○-rec, we can do any super update --- a paradox!

  ⇛/↪⇛-use' :  P  ⊢[ ι ][ i ]⇛  Q
  ⇛/↪⇛-use' {P} {Q = Q} =  ∗⊤-intro »
    ⇛-frameˡ (○-rec ○⇒-↪⇛/↪⇛-use') ᵘ»ᵘ ↪⇛-use' {¡ P} {¡ Q}

--------------------------------------------------------------------------------
-- If we can use ↪⟨ ⟩ᴾ without ▶, then we get a paradox

module _
  -- ↪⟨⟩ᴾ-use without ▶
  (↪⟨⟩ᴾ-use' :  ∀{T} {e : Expr ∞ T} {P˂ Q˂˙ ι} →
    P˂ .! ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂˙)  ⊢[ ι ]⟨ e ⟩ᴾ λ v →  Q˂˙ v .!)
  where abstract

  -- We can strip ○ from ↪⟨⟩ᴾ, using ↪⟨⟩ᴾ-use'

  ○⇒-↪⟨⟩ᴾ/↪⟨⟩ᴾ-use' :  ○ ¡ (P˂ ↪⟨ e ⟩ᴾ Q˂˙)  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q˂˙
  ○⇒-↪⟨⟩ᴾ/↪⟨⟩ᴾ-use' =  ○⇒↪⟨⟩ᴾ λ{ .! → ↪⟨⟩ᴾ-use' }

  -- Therefore, by ○-rec, we have any partial Hoare triple --- a paradox!

  horᴾ/↪⟨⟩ᴾ-use' :  P  ⊢[ ι ]⟨ e ⟩ᴾ  Q˙
  horᴾ/↪⟨⟩ᴾ-use' {P} {Q˙ = Q˙} =  ∗⊤-intro »
    ⇛-frameˡ (○-rec {i = 0} ○⇒-↪⟨⟩ᴾ/↪⟨⟩ᴾ-use') ᵘ»ʰ
    ↪⟨⟩ᴾ-use' {P˂ = ¡ P} {λ v → ¡ Q˙ v}

--------------------------------------------------------------------------------
-- If we can use ↪⟨ ⟩ᵀ without counter increment, then we get a paradox

module _
  -- ↪⟨⟩ᵀ-use without counter increment
  (↪⟨⟩ᵀ-use' :  ∀{T} {e : Expr ∞ T} {P˂ Q˂˙ i ι} →
    P˂ .! ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙)  ⊢[ ι ]⟨ e ⟩ᵀ[ i ] λ v →  Q˂˙ v .!)
  where abstract

  -- We can strip ○ from ↪⟨⟩ᵀ, using ↪⟨⟩ᵀ-use'

  ○⇒-↪⟨⟩ᵀ/↪⟨⟩ᵀ-use' :  ○ ¡ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙)  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙
  ○⇒-↪⟨⟩ᵀ/↪⟨⟩ᵀ-use' =  ○⇒↪⟨⟩ᵀ λ{ .! → ↪⟨⟩ᵀ-use' }

  -- Therefore, by ○-rec, we have any total Hoare triple --- a paradox!

  horᵀ/↪⟨⟩ᵀ-use' :  P  ⊢[ ι ]⟨ e ⟩ᵀ[ i ]  Q˙
  horᵀ/↪⟨⟩ᵀ-use' {P} {Q˙ = Q˙} =  ∗⊤-intro »
    ⇛-frameˡ (○-rec {i = 0} ○⇒-↪⟨⟩ᵀ/↪⟨⟩ᵀ-use') ᵘ»ʰ
    ↪⟨⟩ᵀ-use' {P˂ = ¡ P} {λ v → ¡ Q˙ v}

--------------------------------------------------------------------------------
-- If we can use ↪⟨ ⟩ᵀ with ▶, not counter increment, then we get a paradox

module _
  -- ↪⟨⟩ᵀ-use with ▶, not counter increment
  (↪⟨⟩ᵀ-use▶ :  ∀{T} {e˂ : Expr˂ ∞ T} {P˂ Q˂˙ i ι} →
    P˂ .! ∗ (P˂ ↪⟨ e˂ .! ⟩ᵀ[ i ] Q˂˙)  ⊢[ ι ]⟨ ▶ e˂ ⟩ᵀ[ i ] λ v →  Q˂˙ v .!)
  where abstract

  -- We can strip ○ from ↪⟨ loop ⟩ᵀ, using ↪⟨⟩ᵀ-use▶

  ○⇒-↪⟨loop⟩ᵀ/↪⟨⟩ᵀ-use▶ :
    ○ ¡ (P˂ ↪⟨ loop ⟩ᵀ[ i ] Q˂˙)  ⊢[ ι ]  P˂ ↪⟨ loop ⟩ᵀ[ i ] Q˂˙
  ○⇒-↪⟨loop⟩ᵀ/↪⟨⟩ᵀ-use▶ =  ○⇒↪⟨⟩ᵀ λ{ .! → ↪⟨⟩ᵀ-use▶ }

  -- Therefore, by ○-rec, we have any total Hoare triple for the expression
  -- loop, which is a paradox: Although the total Hoare triple should ensure
  -- termination, loop does not terminate!

  horᵀ-loop/↪⟨⟩ᵀ-use▶ :  P  ⊢[ ι ]⟨ loop ⟩ᵀ[ i ]  Q˙
  horᵀ-loop/↪⟨⟩ᵀ-use▶ {P} {Q˙ = Q˙} =  ∗⊤-intro »
    ⇛-frameˡ (○-rec {i = 0} ○⇒-↪⟨loop⟩ᵀ/↪⟨⟩ᵀ-use▶) ᵘ»ʰ
    ↪⟨⟩ᵀ-use▶ {P˂ = ¡ P} {λ v → ¡ Q˙ v}
