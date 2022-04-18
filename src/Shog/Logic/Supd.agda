------------------------------------------------------------------------
-- Shog proof rules on the super update
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Logic.Supd where

open import Level using (Level; suc)
open import Size using (Size; ∞)
open import Codata.Sized.Thunk using (force)
open import Function.Base using (_$_)

open import Shog.Logic.Prop using (Propₛ; _∗_; |=>)
open import Shog.Logic.Judg using (∗-comm; |=>-intro)
open import Shog.Logic.Judg public using (
  _⊢[_]_; _⊢[<_]_; _⊢[_]=>>_; _»_; <'|=>⇒=>>; _[=>>]»[=>>]_; =>>-frame₀)

private variable
  ℓ : Level
  i : Size
  P Q R : Propₛ ℓ ∞

<⇒=>> : P ⊢[< i ] Q → P ⊢[ i ]=>> Q
<⇒=>> P⊢<Q = <'|=>⇒=>> $ λ where .force → P⊢<Q .force » |=>-intro

|=>⇒=>> : P ⊢[ i ] |=> Q → P ⊢[ i ]=>> Q
|=>⇒=>> P⊢Q = <'|=>⇒=>> $ λ where .force → P⊢Q

⇒=>> : P ⊢[ i ] Q → P ⊢[ i ]=>> Q
⇒=>> P⊢Q = <⇒=>> λ where .force → P⊢Q

infixr -1 _[=>>]»_ -- the same fixity with _$_

_[=>>]»_ : P ⊢[ i ]=>> Q → Q ⊢[ i ] R → P ⊢[ i ]=>> R
P⊢=>>Q [=>>]» Q⊢R = P⊢=>>Q [=>>]»[=>>] ⇒=>> Q⊢R

=>>-frame₁ : P ⊢[ i ]=>> Q → P ∗ R ⊢[ i ]=>> Q ∗ R
=>>-frame₁ P⊢=>>Q = ∗-comm » =>>-frame₀ P⊢=>>Q [=>>]» ∗-comm
