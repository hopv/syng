--------------------------------------------------------------------------------
-- Proof rules on ⇛
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Supd where

open import Base.Func using (_$_; _∘_; id)
open import Base.Size using (Size; ∞)
open import Base.Nat using (ℕ; _≤ᵈ_; ≤ᵈ-refl; ≤ᵈṡ; _≤_; ≤⇒≤ᵈ)
open import Syho.Logic.Prop using (Prop'; _∗_; ⤇_)
open import Syho.Logic.Core using (_⊢[_]_; ⊢-refl; _»_; ∗-comm; ⤇-intro)

-- Import and re-export
open import Syho.Logic.Judg public using ([_]⇛_; _⊢[_][_]⇛_; _⊢[<_][_]⇛_; ⇛-ṡ;
  ⇛-refl-⤇; _ᵘ»ᵘ_; ⇛-frameˡ)

private variable
  ι :  Size
  i j :  ℕ
  P Q R :  Prop' ∞

abstract

  -- Counter tweak

  -->  ⇛-ṡ :  P ⊢[ ι ][ i ]⇛ Q →  P ⊢[ ι ][ ṡ i ]⇛ Q

  ⇛-≤ᵈ :  i ≤ᵈ j →  P ⊢[ ι ][ i ]⇛ Q →  P ⊢[ ι ][ j ]⇛ Q
  ⇛-≤ᵈ ≤ᵈ-refl =  id
  ⇛-≤ᵈ (≤ᵈṡ i≤ᵈj') =  ⇛-ṡ ∘ ⇛-≤ᵈ i≤ᵈj'

  ⇛-≤ :  i ≤ j →  P ⊢[ ι ][ i ]⇛ Q →  P ⊢[ ι ][ j ]⇛ Q
  ⇛-≤ =  ⇛-≤ᵈ ∘ ≤⇒≤ᵈ

  -- Reflexivity of ⇛

  -->  ⇛-refl-⤇ :  ⤇ P ⊢[ ι ][ i ]⇛ P

  ⇛-refl :  P ⊢[ ι ][ i ]⇛ P
  ⇛-refl =  ⤇-intro » ⇛-refl-⤇

  -- Lift a sequent into a super update ⇛

  ⊢⇒⊢⇛ :  P ⊢[ ι ] Q →  P ⊢[ ι ][ i ]⇛ Q
  ⊢⇒⊢⇛ P⊢Q =  P⊢Q » ⇛-refl

  -- Compose with ⇛

  -->  _ᵘ»ᵘ_ :  P ⊢[ ι ][ i ]⇛ Q →  Q ⊢[ ι ][ i ]⇛ R →  P ⊢[ ι ][ i ]⇛ R

  infixr -1 _ᵘ»_

  _ᵘ»_ :  P ⊢[ ι ][ i ]⇛ Q →  Q ⊢[ ι ] R →  P ⊢[ ι ][ i ]⇛ R
  P⊢⇛Q ᵘ» Q⊢R =  P⊢⇛Q ᵘ»ᵘ ⊢⇒⊢⇛ Q⊢R

  -- Framing of ⇛

  -->  ⇛-frameˡ :  Q ⊢[ ι ][ i ]⇛ R →  P ∗ Q ⊢[ ι ][ i ]⇛ P ∗ R

  ⇛-frameʳ :  P ⊢[ ι ][ i ]⇛ Q →  P ∗ R ⊢[ ι ][ i ]⇛ Q ∗ R
  ⇛-frameʳ P⊢⇛Q =  ∗-comm » ⇛-frameˡ P⊢⇛Q ᵘ» ∗-comm
