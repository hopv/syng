--------------------------------------------------------------------------------
-- Paradoxes on plausible proof rules
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Paradox where

open import Base.Size using (∞)
open import Base.Thunk using (thunk; !)
open import Base.Func using (_$_)
open import Syho.Logic.Prop using (Prop'; ⊤'; ⊥'; □_; _∗_; ○_; _↪[_]=>>_)
open import Syho.Logic.Core using (_⊢[_]_; _»_; ∧-elimˡ; →-intro; ∗-elimˡ;
  ⊤∗-intro; □-mono; □-elim)
open import Syho.Logic.Supd using (_⊢[_][_]=>>_; _ᵘ»ᵘ_; _ᵘ»_)
open import Syho.Logic.Ind using (□○-alloc-rec; ○⇒↪=>>; ○-use)

--------------------------------------------------------------------------------
-- If we can use ↪=>> without counter increment, then we get a paradox

module _
  -- ↪=>>-use without counter increment
  (↪=>>-use' :  ∀{P˂ Q˂} →  P˂ .! ∗ (P˂ ↪[ 0 ]=>> Q˂)  ⊢[ ∞ ][ 0 ]=>>  Q˂ .!)
  where abstract

  ↪=>>⊥ :  Prop' ∞
  ↪=>>⊥ =  thunk ⊤' ↪[ 0 ]=>> thunk ⊥'

  -- We can turn ○ □ ↪=>>⊥ into ↪=>>⊥, using ↪=>>-use'

  ○□↪=>>⊥⇒↪=>>⊥ :  ○ thunk (□ ↪=>>⊥) ⊢[ ∞ ] ↪=>>⊥
  ○□↪=>>⊥⇒↪=>>⊥ =  ○⇒↪=>> $ ∗-elimˡ » □-elim » ⊤∗-intro » ↪=>>-use'

  -- Thus we can allocate ↪=>>⊥

  ↪=>>⊥-alloc :  ⊤' ⊢[ ∞ ][ 0 ]=>> ↪=>>⊥
  ↪=>>⊥-alloc =  →-intro (∧-elimˡ » □-mono ○□↪=>>⊥⇒↪=>>⊥) »
    □○-alloc-rec ᵘ»ᵘ □-elim » ○-use ᵘ» □-elim

  -- Finally, we get ⊥ after super update --- a paradox!

  =>>⊥ :  ⊤' ⊢[ ∞ ][ 0 ]=>> ⊥'
  =>>⊥ =  ↪=>>⊥-alloc ᵘ»ᵘ ⊤∗-intro » ↪=>>-use'
