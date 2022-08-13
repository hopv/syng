--------------------------------------------------------------------------------
-- Proof rules on =>>
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Supd where

open import Base.Size using (Size; ∞)
open import Base.Func using (_$_; _∘_; id)
open import Base.Nat using (ℕ; _≤ᵈ_; ≤ᵈ-refl; ≤ᵈsuc; _≤_; ≤⇒≤ᵈ)
open import Syho.Logic.Prop using (Prop'; _∗_; |=>_)
open import Syho.Logic.Core using (_⊢[_]_; ⊢-refl; _»_; ∗-comm; |=>-intro)

-- Import and re-export
open import Syho.Logic.Judg public using ([_]=>>_; _⊢[_][_]=>>_; _⊢[<_][_]=>>_;
  =>>-suc; |=>⇒=>>; _ᵘ»ᵘ_; =>>-frameˡ)

private variable
  ι :  Size
  i j :  ℕ
  P Q R :  Prop' ∞

abstract

  -->  |=>⇒=>> :  P ⊢[ ι ] |=> Q →  P ⊢[ ι ][ i ]=>> Q

  -- Counter tweak

  -->  =>>-suc :  P ⊢[ ι ][ i ]=>> Q →  P ⊢[ ι ][ suc i ]=>> Q

  =>>-≤ᵈ :  i ≤ᵈ j →  P ⊢[ ι ][ i ]=>> Q →  P ⊢[ ι ][ j ]=>> Q
  =>>-≤ᵈ ≤ᵈ-refl =  id
  =>>-≤ᵈ (≤ᵈsuc i≤ᵈj') =  =>>-suc ∘ =>>-≤ᵈ i≤ᵈj'

  =>>-≤ :  i ≤ j →  P ⊢[ ι ][ i ]=>> Q →  P ⊢[ ι ][ j ]=>> Q
  =>>-≤ =  =>>-≤ᵈ ∘ ≤⇒≤ᵈ

  -- Lift a sequent into a super update =>>

  ⇒=>> :  P ⊢[ ι ] Q →  P ⊢[ ι ][ i ]=>> Q
  ⇒=>> P⊢Q =  |=>⇒=>> $ P⊢Q » |=>-intro

  -- Reflexivity

  =>>-refl :  P ⊢[ ι ][ i ]=>> P
  =>>-refl =  ⇒=>> ⊢-refl

  -->  _ᵘ»ᵘ_ :  P ⊢[ ι ][ i ]=>> Q →  Q ⊢[ ι ][ i ]=>> R →  P ⊢[ ι ][ i ]=>> R

  -- Modifying the succedent of a super update with a sequent

  infixr -1 _ᵘ»_

  _ᵘ»_ :  P ⊢[ ι ][ i ]=>> Q →  Q ⊢[ ι ] R →  P ⊢[ ι ][ i ]=>> R
  P⊢=>>Q ᵘ» Q⊢R =  P⊢=>>Q ᵘ»ᵘ ⇒=>> Q⊢R

  -- The super update =>> can frame

  -->  =>>-frameˡ :  Q ⊢[ ι ][ i ]=>> R →  P ∗ Q ⊢[ ι ][ i ]=>> P ∗ R

  =>>-frameʳ :  P ⊢[ ι ][ i ]=>> Q →  P ∗ R ⊢[ ι ][ i ]=>> Q ∗ R
  =>>-frameʳ P⊢=>>Q =  ∗-comm » =>>-frameˡ P⊢=>>Q ᵘ» ∗-comm
