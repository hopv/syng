--------------------------------------------------------------------------------
-- Level for universe levels
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Level where

open import Agda.Primitive public using (Level)
  renaming (lzero to ○; lsuc to infix 8 ^_; _⊔_ to _⌴_)

infix 8 ↑_
record  Up {ℓ : Level} (A : Set ℓ) {ℓ' : Level} :  Set (ℓ ⌴ ℓ')  where
  constructor ↑_
  infix 8 ↓_
  field  ↓_ :  A
open Up public
