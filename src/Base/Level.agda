--------------------------------------------------------------------------------
-- Level for universe levels
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Level where

open import Agda.Primitive public using (
  -- Level, in Set ○
  Level) renaming (
  -- Zero level, in Level
  lzero to ○;
  -- Successor level, in Level → Level
  lsuc to infix 8 ^_;
  -- Maximum level, in Level → Level → Level
  _⊔_ to _⌴_)

-- Up : Wrapper raising the level

infix 8 ↑_
record  Up {ℓ : Level} (A : Set ℓ) {ℓ' : Level} :  Set (ℓ ⌴ ℓ')  where
  -- ↑/↓ : Wrap into / unwrap from Up
  constructor ↑_
  infix 8 ↓_
  field  ↓_ :  A
open Up public
