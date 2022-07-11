--------------------------------------------------------------------------------
-- Proof rules on the super update
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Logic.Supd (ℓ : Level) where

open import Base.Size using (Size; ∞)
open import Base.Thunk using (!)
open import Base.Func using (_$_)
open import Shog.Logic.Prop ℓ using (Prop'; _∗_; |=>_)
open import Shog.Logic.Core ℓ using (_⊢[_]_; _⊢[<_]_; ⊢-refl; _»_; ∗-comm;
  |=>-intro)

-- Import and re-export
open import Shog.Logic.Judg ℓ public using (|=>>_; _⊢[_]=>>_; ˂|=>⇒=>>; _ᵘ»ᵘ_;
  =>>-frameˡ)

private variable
  ι :  Size
  P Q R :  Prop' ∞

abstract

  -- Lifting a thunk sequent into a super update =>>
  ˂⇒=>> :  P ⊢[< ι ] Q →  P ⊢[ ι ]=>> Q
  ˂⇒=>> P⊢˂Q =  ˂|=>⇒=>> λ{ .! → P⊢˂Q .! » |=>-intro }

  -- Lifting a sequent under |=> into a super update =>>
  |=>⇒=>> :  P ⊢[ ι ] |=> Q →  P ⊢[ ι ]=>> Q
  |=>⇒=>> P⊢Q =  ˂|=>⇒=>> λ{ .! → P⊢Q }

  -- Lifting a sequent into a super update =>>
  ⇒=>> :  P ⊢[ ι ] Q →  P ⊢[ ι ]=>> Q
  ⇒=>> P⊢Q =  ˂⇒=>> λ{ .! → P⊢Q }

  -- Reflexivity
  =>>-refl :  P ⊢[ ι ]=>> P
  =>>-refl =  ⇒=>> ⊢-refl

  -- Modifying the succedent of a super update with a sequent

  infixr -1 _ᵘ»_

  _ᵘ»_ :  P ⊢[ ι ]=>> Q →  Q ⊢[ ι ] R →  P ⊢[ ι ]=>> R
  P⊢=>>Q ᵘ» Q⊢R =  P⊢=>>Q ᵘ»ᵘ ⇒=>> Q⊢R

  -- The super update =>> can frame
  =>>-frameʳ :  P ⊢[ ι ]=>> Q →  P ∗ R ⊢[ ι ]=>> Q ∗ R
  =>>-frameʳ P⊢=>>Q =  ∗-comm » =>>-frameˡ P⊢=>>Q ᵘ» ∗-comm
