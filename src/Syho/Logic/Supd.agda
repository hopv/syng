--------------------------------------------------------------------------------
-- Proof rules on the super-update sequent
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Supd where

open import Base.Func using (_$_; _∘_; id)
open import Base.Size using (Size)
open import Base.Nat using (ℕ; _≤ᵈ_; _<ᵈ_; ≤ᵈ-refl; ≤ᵈṡ; _≤_; _<_; ṡ≤ᵈṡ; ≤⇒≤ᵈ)
open import Syho.Logic.Prop using (Prop∞; _∗_; ⤇_)
open import Syho.Logic.Core using (_⊢[_]_; ⇒<; ⊢-refl; _»_; ∗-comm; ∗-assocˡ;
  ∗-assocʳ; ⤇-intro)

-- Import and re-export
open import Syho.Logic.Judg public using ([_]⇛_; _⊢[_][_]⇛_; _⊢[<_][_]⇛_;
  _⊢[_][_]⇛ᴺ_; _⊢[<_][_]⇛ᴺ_; ⇛-ṡ; ⇛-refl-⤇; _ᵘ»ᵘ_; ⇛-frameˡ)

private variable
  ι :  Size
  i j :  ℕ
  P Q R :  Prop∞

abstract

  -- Level increment

  -->  ⇛-ṡ :  P ⊢[< ι ][ i ]⇛ Q →  P ⊢[ ι ][ ṡ i ]⇛ Q

  ⇛-<ᵈ :  i <ᵈ j →  P ⊢[< ι ][ i ]⇛ Q →  P ⊢[ ι ][ j ]⇛ Q
  ⇛-<ᵈ ≤ᵈ-refl =  ⇛-ṡ
  ⇛-<ᵈ (≤ᵈṡ i<j') =  ⇛-ṡ ∘ ⇒< ∘ ⇛-<ᵈ i<j'

  ⇛-≤ᵈ :  i ≤ᵈ j →  P ⊢[ ι ][ i ]⇛ Q →  P ⊢[ ι ][ j ]⇛ Q
  ⇛-≤ᵈ ≤ᵈ-refl =  id
  ⇛-≤ᵈ (≤ᵈṡ i≤j') =  ⇛-<ᵈ (ṡ≤ᵈṡ i≤j') ∘ ⇒<

  ⇛-< :  i < j →  P ⊢[< ι ][ i ]⇛ Q →  P ⊢[ ι ][ j ]⇛ Q
  ⇛-< =  ⇛-<ᵈ ∘ ≤⇒≤ᵈ

  ⇛-≤ :  i ≤ j →  P ⊢[ ι ][ i ]⇛ Q →  P ⊢[ ι ][ j ]⇛ Q
  ⇛-≤ =  ⇛-≤ᵈ ∘ ≤⇒≤ᵈ

  -- Reflexivity of ⇛

  -->  ⇛-refl-⤇ :  ⤇ P ⊢[ ι ][ i ]⇛ P

  ⇛-refl :  P ⊢[ ι ][ i ]⇛ P
  ⇛-refl =  ⤇-intro » ⇛-refl-⤇

  -- Lift ⊢ into ⊢⇛

  ⇒⇛ :  P ⊢[ ι ] Q →  P ⊢[ ι ][ i ]⇛ Q
  ⇒⇛ P⊢Q =  P⊢Q » ⇛-refl

  -- Compose ⇛

  -->  _ᵘ»ᵘ_ :  P ⊢[ ι ][ i ]⇛ Q →  Q ⊢[ ι ][ i ]⇛ R →  P ⊢[ ι ][ i ]⇛ R

  infixr -1 _ᵘ»_

  _ᵘ»_ :  P ⊢[ ι ][ i ]⇛ Q →  Q ⊢[ ι ] R →  P ⊢[ ι ][ i ]⇛ R
  P⊢⇛Q ᵘ» Q⊢R =  P⊢⇛Q ᵘ»ᵘ ⇒⇛ Q⊢R

  -- Frame for ⇛

  -->  ⇛-frameˡ :  P ⊢[ ι ][ i ]⇛ Q →  R ∗ P ⊢[ ι ][ i ]⇛ R ∗ Q

  ⇛-frameʳ :  P ⊢[ ι ][ i ]⇛ Q →  P ∗ R ⊢[ ι ][ i ]⇛ Q ∗ R
  ⇛-frameʳ P⊢⇛Q =  ∗-comm » ⇛-frameˡ P⊢⇛Q ᵘ» ∗-comm

  -- ⇛ into ⇛ᴺ

  ⇛⇒⇛ᴺ :  P ⊢[ ι ][ i ]⇛ Q →  P ⊢[ ι ][ i ]⇛ᴺ Q
  ⇛⇒⇛ᴺ =  ⇛-frameʳ

  -- Reflexivity of ⇛ᴺ

  ⇛ᴺ-refl :  P ⊢[ ι ][ i ]⇛ᴺ P
  ⇛ᴺ-refl =  ⇛-refl

  -- Lift a pure sequent into ⇛ᴺ

  ⇒⇛ᴺ :  P ⊢[ ι ] Q →  P ⊢[ ι ][ i ]⇛ᴺ Q
  ⇒⇛ᴺ P⊢Q =  ⇛⇒⇛ᴺ $ ⇒⇛ P⊢Q

  -- Compose with ⇛ᴺ

  infixr -1 _ᵘᴺ»ᵘᴺ_ _ᵘᴺ»_ _»ᵘᴺ_

  _ᵘᴺ»ᵘᴺ_ :  P ⊢[ ι ][ i ]⇛ᴺ Q →  Q ⊢[ ι ][ i ]⇛ᴺ R →  P ⊢[ ι ][ i ]⇛ᴺ R
  _ᵘᴺ»ᵘᴺ_ =  _ᵘ»ᵘ_

  _ᵘᴺ»_ :  P ⊢[ ι ][ i ]⇛ᴺ Q →  Q ⊢[ ι ] R →  P ⊢[ ι ][ i ]⇛ᴺ R
  P⊢⇛Q ᵘᴺ» Q⊢R =  P⊢⇛Q ᵘᴺ»ᵘᴺ ⇒⇛ᴺ Q⊢R

  _»ᵘᴺ_ :  P ⊢[ ι ] Q →  Q ⊢[ ι ][ i ]⇛ᴺ R →  P ⊢[ ι ][ i ]⇛ᴺ R
  P⊢Q »ᵘᴺ Q⊢⇛R =  ⇒⇛ᴺ P⊢Q ᵘᴺ»ᵘᴺ Q⊢⇛R

  -- Frame for ⇛ᴺ

  ⇛ᴺ-frameˡ :  P ⊢[ ι ][ i ]⇛ᴺ Q →  R ∗ P ⊢[ ι ][ i ]⇛ᴺ R ∗ Q
  ⇛ᴺ-frameˡ P⊢⇛Q =  ∗-assocˡ » ⇛-frameˡ P⊢⇛Q ᵘ» ∗-assocʳ

  ⇛ᴺ-frameʳ :  P ⊢[ ι ][ i ]⇛ᴺ Q →  P ∗ R ⊢[ ι ][ i ]⇛ᴺ Q ∗ R
  ⇛ᴺ-frameʳ P⊢⇛Q =  ∗-comm »ᵘᴺ ⇛ᴺ-frameˡ P⊢⇛Q ᵘᴺ» ∗-comm
