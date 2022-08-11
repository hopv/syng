--------------------------------------------------------------------------------
-- Paradoxes on plausible proof rules
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Paradox where

open import Base.Size using (∞)
open import Base.Thunk using (¡_; !)
open import Base.Func using (_$_)
open import Base.Few using (0⊤)
open import Syho.Lang.Expr using (∇_)
open import Syho.Logic.Prop using (Prop'; ⊤'; ⊥'; □_; _∗_; ○_; _↪[_]=>>_;
  _↪⟨_⟩ᴾ_)
open import Syho.Logic.Core using (_⊢[_]_; _»_; ∧-elimˡ; →-intro; ∗-elimˡ;
  ⊤∗-intro; □-mono; □-elim)
open import Syho.Logic.Supd using (_⊢[_][_]=>>_; _ᵘ»ᵘ_; _ᵘ»_)
open import Syho.Logic.Hor using (_⊢[_]⟨_⟩ᴾ_; _ᵘ»ʰ_)
open import Syho.Logic.Ind using (○-mono; □○-alloc-rec; ○-use; ○⇒↪=>>; ○⇒↪⟨⟩ᴾ)

private variable
  P :  Prop' ∞

--------------------------------------------------------------------------------
-- Utility

-- If we can turn ○ P into P, then we get P after a super update,
-- thanks to □○-alloc-rec

○-rec :  ○ ¡ P ⊢[ ∞ ] P →  ⊤' ⊢[ ∞ ][ 0 ]=>> P
○-rec {P} ○P⊢P =  →-intro (∧-elimˡ » □-mono $ ○-mono (¡ □-elim) » ○P⊢P) »
    □○-alloc-rec {P˂ = ¡ □ P} ᵘ»ᵘ □-elim » ○-use ᵘ» □-elim

--------------------------------------------------------------------------------
-- If we can use ↪=>> without counter increment, then we get a paradox

module _
  -- ↪=>>-use without counter increment
  (↪=>>-use' :  ∀{P˂ Q˂ ι} →  P˂ .! ∗ (P˂ ↪[ 0 ]=>> Q˂)  ⊢[ ι ][ 0 ]=>>  Q˂ .!)
  where abstract

  -- Precursor that gets ⊥' after super update

  ↪=>>⊥ :  Prop' ∞
  ↪=>>⊥ =  ¡ ⊤' ↪[ 0 ]=>> ¡ ⊥'

  -- We can turn ○ ↪=>>⊥ into ↪=>>⊥, using ↪=>>-use'

  ○⇒-↪=>>⊥ :  ○ ¡ ↪=>>⊥ ⊢[ ∞ ] ↪=>>⊥
  ○⇒-↪=>>⊥ =  ○⇒↪=>> λ{ .! → ∗-elimˡ » ⊤∗-intro » ↪=>>-use' }

  -- Therefore, by ○-rec, we get ⊥ after super update --- a paradox!

  =>>⊥ :  ⊤' ⊢[ ∞ ][ 0 ]=>> ⊥'
  =>>⊥ =  ○-rec ○⇒-↪=>>⊥ ᵘ»ᵘ ⊤∗-intro » ↪=>>-use'

--------------------------------------------------------------------------------
-- If we can use ↪⟨ ⟩ᴾ without ▶, then we get a paradox

module _
  -- ↪⟨⟩ᴾ-use without ▶
  (↪⟨⟩ᴾ-use' :  ∀{e P˂ Q˂ᵛ ι} →
    P˂ .! ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ)  ⊢[ ι ]⟨ e ⟩ᴾ  λ v → Q˂ᵛ v .!)
  where abstract

  -- Precursor that gets ⊥' after executing just a literal, ∇ 0⊤

  ↪⟨⟩ᴾ⊥ :  Prop' ∞
  ↪⟨⟩ᴾ⊥ =  ¡ ⊤' ↪⟨ ∇ 0⊤ ⟩ᴾ λ _ → ¡ ⊥'

  -- We can turn ○ ↪⟨⟩ᴾ⊥ into ↪⟨⟩ᴾ⊥, using ↪⟨⟩ᴾ-use'

  ○⇒-↪⟨⟩ᴾ⊥ :  ○ ¡ ↪⟨⟩ᴾ⊥ ⊢[ ∞ ] ↪⟨⟩ᴾ⊥
  ○⇒-↪⟨⟩ᴾ⊥ =  ○⇒↪⟨⟩ᴾ λ{ .! → ∗-elimˡ » ⊤∗-intro » ↪⟨⟩ᴾ-use' }

  -- Therefore, by ○-rec, we get ⊥ after executing a literal --- a paradox!

  ⟨⟩ᴾ⊥ :  ⊤' ⊢[ ∞ ]⟨ ∇ 0⊤ ⟩ᴾ λ _ → ⊥'
  ⟨⟩ᴾ⊥ =  ○-rec ○⇒-↪⟨⟩ᴾ⊥ ᵘ»ʰ ⊤∗-intro » ↪⟨⟩ᴾ-use'
