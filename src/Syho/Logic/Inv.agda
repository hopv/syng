--------------------------------------------------------------------------------
-- Proof rules on the impredicative invariant
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Inv where

open import Base.Func using (_$_)
open import Base.Size using (Size; ∞; !; ¡_; _$ᵀʰ_)
open import Base.Nat using (ℕ)
open import Syho.Logic.Prop using (Name; Prop'; Prop˂; _∗_; _-∗_; Inv; OInv;
  Basic)
open import Syho.Logic.Core using (_⊢[_]_; _⊢[<_]_; Pers; Pers-⇒□; _»_; ∗-comm;
  ⊤∗-intro; ∗-elimʳ; -∗-const)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_)

-- Import and re-export
open import Syho.Logic.Judg public using ([]ᴵ-resp; []ᴵ-merge; []ᴵ-split; []ᴵ-✔;
  Inv-⇒□; Inv-resp-∗; OInv-mono; OInv-eatˡ; Inv-alloc-rec; Inv-open; OInv-close)

private variable
  ι :  Size
  P Q R :  Prop' ∞
  P˂ Q˂ :  Prop˂ ∞
  nm :  Name
  i :  ℕ

abstract

  -->  []ᴵ-resp :  Nm ≡˙ Nm' →  [ Nm ]ᴵ ⊢[ ι ] [ Nm' ]ᴵ

  -->  []ᴵ-merge :  [ Nm ]ᴵ  ∗  [ Nm' ]ᴵ  ⊢[ ι ]  [ Nm ⊎ᶻ Nm' ]ᴵ

  -->  []ᴵ-split :  [ Nm ⊎ᶻ Nm' ]ᴵ  ⊢[ ι ]  [ Nm ]ᴵ  ∗  [ Nm' ]ᴵ

  -->  []ᴵ-✔ :  [ Nm ]ᴵ  ⊢[ ι ]  ⌜ ✔ᶻ Nm ⌝

  -->  OInv-mono :  P˂ .!  ⊢[< ι ]  Q˂ .!  →   OInv nm P˂  ⊢[ ι ]  OInv nm Q˂

  -->  Inv-open :  Inv nm P˂  ∗  [ ^ᶻ nm ]ᴵ  ⊢[ ι ][ i ]⇛  P˂ .!  ∗  OInv nm P˂

  -->  OInv-close :  P˂ .!  ∗  OInv nm P˂  ⊢[ ι ][ i ]⇛  [ ^ᶻ nm ]ᴵ

  instance

    -- An invariant token is persistent

    -->  Inv-⇒□ :  Inv nm P˂  ⊢[ ι ]  □ Inv nm P˂

    Inv-Pers :  Pers $ Inv nm P˂
    Inv-Pers .Pers-⇒□ =  Inv-⇒□

  -- Change the proposition of an invariant token

  -->  Inv-resp-∗ :  {{Pers R}} →  {{Basic R}} →
  -->    R  ∗  P˂ .!  ⊢[< ι ]  Q˂ .!  →   R  ∗  Q˂ .!  ⊢[< ι ]  P˂ .!  →
  -->    R  ∗  Inv nm P˂  ⊢[ ι ]  Inv nm Q˂

  Inv-resp :  P˂ .!  ⊢[< ι ]  Q˂ .!  →   Q˂ .!  ⊢[< ι ]  P˂ .!  →
              Inv nm P˂  ⊢[ ι ]  Inv nm Q˂
  Inv-resp P⊢<Q Q⊢<P =  ⊤∗-intro »
    Inv-resp-∗ ((∗-elimʳ »_) $ᵀʰ P⊢<Q) ((∗-elimʳ »_) $ᵀʰ Q⊢<P)

  -- Let an open invariant token eat a basic proposition

  -->  OInv-eatˡ :  {{Basic Q}} →
  -->    Q  ∗  OInv nm P˂  ⊢[ ι ]  OInv nm (¡ (Q -∗ P˂ .!))

  OInv-eatʳ :  {{Basic Q}} →  OInv nm P˂  ∗  Q  ⊢[ ι ]  OInv nm (¡ (Q -∗ P˂ .!))
  OInv-eatʳ =   ∗-comm » OInv-eatˡ

  -- Allocate a proposition to get an invariant token

  -->  Inv-alloc-rec :  Inv nm P˂ -∗ P  ⊢[ ι ][ i ]⇛  Inv nm P˂

  Inv-alloc :  P  ⊢[ ι ][ i ]⇛  Inv nm P˂
  Inv-alloc =  -∗-const » Inv-alloc-rec
