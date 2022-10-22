--------------------------------------------------------------------------------
-- Proof rules on the name set token
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Names where

open import Base.Func using (_$_)
open import Base.Eq using (◠˙_)
open import Base.Size using (𝕊)
open import Base.Zoi using (Zoi; _⊆ᶻ_; _∖ᶻ_; ⊆ᶻ⇒∖-⊎ˡ)
open import Syho.Logic.Prop using (Name; _∗_; _-∗_; [_]ᴺ)
open import Syho.Logic.Core using (_⊢[_]_; _»_; ∗-monoʳ; -∗-introˡ)

-- Import and re-export
open import Syho.Logic.Judg public using ([]ᴺ-resp; []ᴺ-merge; []ᴺ-split; []ᴺ-✔)

private variable
  ι :  𝕊
  Nm Nm' :  Name → Zoi
  nm :  Name

abstract

  ------------------------------------------------------------------------------
  -- On the name set token

  -->  []ᴺ-resp :  Nm ≡˙ Nm' →  [ Nm ]ᴺ ⊢[ ι ] [ Nm' ]ᴺ

  -->  []ᴺ-merge :  [ Nm ]ᴺ  ∗  [ Nm' ]ᴺ  ⊢[ ι ]  [ Nm ⊎ᶻ Nm' ]ᴺ

  -->  []ᴺ-split :  [ Nm ⊎ᶻ Nm' ]ᴺ  ⊢[ ι ]  [ Nm ]ᴺ  ∗  [ Nm' ]ᴺ

  -->  []ᴺ-✔ :  [ Nm ]ᴺ  ⊢[ ι ]  ⌜ ✔ᶻ Nm ⌝

  -- Take out a name set token of a subset

  []ᴺ-⊆-split :  Nm' ⊆ᶻ Nm  →   [ Nm ]ᴺ  ⊢[ ι ]  [ Nm' ]ᴺ  ∗  [ Nm ∖ᶻ Nm' ]ᴺ
  []ᴺ-⊆-split Nm'⊆Nm =  []ᴺ-resp (◠˙ ⊆ᶻ⇒∖-⊎ˡ Nm'⊆Nm) » []ᴺ-split

  []ᴺ-⊆-merge :  Nm' ⊆ᶻ Nm  →   [ Nm' ]ᴺ  ∗  [ Nm ∖ᶻ Nm' ]ᴺ  ⊢[ ι ]  [ Nm ]ᴺ
  []ᴺ-⊆-merge Nm'⊆Nm =  []ᴺ-merge » []ᴺ-resp (⊆ᶻ⇒∖-⊎ˡ Nm'⊆Nm)

  []ᴺ-⊆--∗ :  Nm' ⊆ᶻ Nm  →   [ Nm ]ᴺ  ⊢[ ι ]  [ Nm' ]ᴺ  ∗  ([ Nm' ]ᴺ -∗ [ Nm ]ᴺ)
  []ᴺ-⊆--∗ Nm'⊆Nm =
    []ᴺ-⊆-split Nm'⊆Nm » ∗-monoʳ $ -∗-introˡ $ []ᴺ-⊆-merge Nm'⊆Nm
