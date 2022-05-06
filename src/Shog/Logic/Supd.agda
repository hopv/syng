--------------------------------------------------------------------------------
-- Shog proof rules on the super update
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Logic.Supd (ℓ : Level) where

open import Base.Size using (Size; ∞)
open import Base.Thunk using (!)
open import Base.Func using (_$_)

open import Shog.Logic.Prop ℓ using (Prop'; _∗_; |=>)
open import Shog.Logic.Judg ℓ public using (
  _⊢[_]_; _⊢[<_]_; _⊢[_]=>>_; _»_; ^|=>⇒=>>; _ᵘ»ᵘ_; =>>-frameˡ)
open import Shog.Logic.Judg ℓ using (∗-comm; |=>-intro)

private variable
  ι : Size
  P Q R : Prop' ∞

abstract

  -- Lifting a thunk sequent into a super update =>>
  ^⇒=>> : P ⊢[< ι ] Q → P ⊢[ ι ]=>> Q
  ^⇒=>> P⊢^Q = ^|=>⇒=>> λ{ .! → P⊢^Q .! » |=>-intro }

  -- Lifting a sequent under |=> into a super update =>>
  |=>⇒=>> : P ⊢[ ι ] |=> Q → P ⊢[ ι ]=>> Q
  |=>⇒=>> P⊢Q = ^|=>⇒=>> λ{ .! → P⊢Q }

  -- Lifting a sequent into a super update =>>
  ⇒=>> : P ⊢[ ι ] Q → P ⊢[ ι ]=>> Q
  ⇒=>> P⊢Q = ^⇒=>> λ{ .! → P⊢Q }

  -- Modifying the succedent of a super update with a sequent

  infixr -1 _ᵘ»_ -- the same fixity with _$_

  _ᵘ»_ : P ⊢[ ι ]=>> Q → Q ⊢[ ι ] R → P ⊢[ ι ]=>> R
  P⊢=>>Q ᵘ» Q⊢R = P⊢=>>Q ᵘ»ᵘ ⇒=>> Q⊢R

  -- The super update =>> can frame
  =>>-frameʳ : P ⊢[ ι ]=>> Q → P ∗ R ⊢[ ι ]=>> Q ∗ R
  =>>-frameʳ P⊢=>>Q = ∗-comm » =>>-frameˡ P⊢=>>Q ᵘ» ∗-comm
