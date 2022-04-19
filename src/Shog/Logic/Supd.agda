------------------------------------------------------------------------
-- Shog proof rules on the super update
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Logic.Supd where

open import Level using (Level; suc)
open import Size using (Size; ∞)
open import Codata.Thunk using (force)
open import Function.Base using (_$_)

open import Shog.Logic.Prop using (Propˢ; _∗_; |=>)
open import Shog.Logic.Judg using (∗-comm; |=>-intro)
open import Shog.Logic.Judg public using (
  _⊢[_]_; _⊢[<_]_; _⊢[_]=>>_; _»_; ᵗ|=>⇒=>>; _ᵘ»ᵘ_; =>>-frame₀)

private variable
  ℓ : Level
  i : Size
  P Q R : Propˢ ℓ ∞

ᵗ⇒=>> : P ⊢[< i ] Q → P ⊢[ i ]=>> Q
ᵗ⇒=>> P⊢ᵗQ = ᵗ|=>⇒=>> $ λ where .force → P⊢ᵗQ .force » |=>-intro

|=>⇒=>> : P ⊢[ i ] |=> Q → P ⊢[ i ]=>> Q
|=>⇒=>> P⊢Q = ᵗ|=>⇒=>> $ λ where .force → P⊢Q

⇒=>> : P ⊢[ i ] Q → P ⊢[ i ]=>> Q
⇒=>> P⊢Q = ᵗ⇒=>> λ where .force → P⊢Q

infixr -1 _ᵘ»_ -- the same fixity with _$_

_ᵘ»_ : P ⊢[ i ]=>> Q → Q ⊢[ i ] R → P ⊢[ i ]=>> R
P⊢=>>Q ᵘ» Q⊢R = P⊢=>>Q ᵘ»ᵘ ⇒=>> Q⊢R

=>>-frame₁ : P ⊢[ i ]=>> Q → P ∗ R ⊢[ i ]=>> Q ∗ R
=>>-frame₁ P⊢=>>Q = ∗-comm » =>>-frame₀ P⊢=>>Q ᵘ» ∗-comm
