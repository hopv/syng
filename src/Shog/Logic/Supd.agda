------------------------------------------------------------------------
-- Shog proof rules on the super update
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Logic.Supd where

open import Level using (Level; suc)
open import Size using (Size; ∞)
open import Codata.Thunk using (force)
open import Function.Base using (_$_)

open import Shog.Logic.Prop using (Prop'; _∗_; |=>)
open import Shog.Logic.Judg using (∗-comm; |=>-intro)
open import Shog.Logic.Judg public using (
  _⊢[_]_; _⊢[<_]_; _⊢[_]=>>_; _»_; ^|=>⇒=>>; _ᵘ»ᵘ_; =>>-frameˡ)

private variable
  ℓ : Level
  ι : Size
  P Q R : Prop' ℓ ∞

-- Lifting a thunk sequent into a super update =>>
^⇒=>> : P ⊢[< ι ] Q → P ⊢[ ι ]=>> Q
^⇒=>> P⊢^Q = ^|=>⇒=>> λ{ .force → P⊢^Q .force » |=>-intro }

-- Lifting a sequent under |=> into a super update =>>
|=>⇒=>> : P ⊢[ ι ] |=> Q → P ⊢[ ι ]=>> Q
|=>⇒=>> P⊢Q = ^|=>⇒=>> λ{ .force → P⊢Q }

-- Lifting a sequent into a super update =>>
⇒=>> : P ⊢[ ι ] Q → P ⊢[ ι ]=>> Q
⇒=>> P⊢Q = ^⇒=>> λ{ .force → P⊢Q }

-- Modifying the succedent of a super update with a sequent

infixr -1 _ᵘ»_ -- the same fixity with _$_

_ᵘ»_ : P ⊢[ ι ]=>> Q → Q ⊢[ ι ] R → P ⊢[ ι ]=>> R
P⊢=>>Q ᵘ» Q⊢R = P⊢=>>Q ᵘ»ᵘ ⇒=>> Q⊢R

-- The super update =>> can frame
=>>-frameʳ : P ⊢[ ι ]=>> Q → P ∗ R ⊢[ ι ]=>> Q ∗ R
=>>-frameʳ P⊢=>>Q = ∗-comm » =>>-frameˡ P⊢=>>Q ᵘ» ∗-comm
