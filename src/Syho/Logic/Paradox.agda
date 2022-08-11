--------------------------------------------------------------------------------
-- Paradoxes on plausible proof rules
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Paradox where

open import Base.Size using (∞)
open import Base.Thunk using (¡_; !)
open import Base.Func using (_$_)
open import Syho.Logic.Prop using (Prop'; ⊤'; ⊥'; □_; _∗_; ○_; _↪[_]=>>_)
open import Syho.Logic.Core using (_⊢[_]_; _»_; ∧-elimˡ; →-intro; ∗-elimˡ;
  ⊤∗-intro; □-mono; □-elim)
open import Syho.Logic.Supd using (_⊢[_][_]=>>_; _ᵘ»ᵘ_; _ᵘ»_)
open import Syho.Logic.Ind using (○-mono; □○-alloc-rec; ○⇒↪=>>; ○-use)

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

  ↪=>>⊥ :  Prop' ∞
  ↪=>>⊥ =  ¡ ⊤' ↪[ 0 ]=>> ¡ ⊥'

  -- We can turn ○ ↪=>>⊥ into ↪=>>⊥, using ↪=>>-use'

  ○⇒-↪=>>⊥ :  ○ ¡ ↪=>>⊥ ⊢[ ∞ ] ↪=>>⊥
  ○⇒-↪=>>⊥ =  ○⇒↪=>> λ{ .! → ∗-elimˡ » ⊤∗-intro » ↪=>>-use' }

  -- Therefore, by ○-rec, we get ⊥ after super update --- a paradox!

  =>>⊥ :  ⊤' ⊢[ ∞ ][ 0 ]=>> ⊥'
  =>>⊥ =  ○-rec ○⇒-↪=>>⊥ ᵘ»ᵘ ⊤∗-intro » ↪=>>-use'
