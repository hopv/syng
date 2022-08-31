--------------------------------------------------------------------------------
-- Level for universe levels
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Level where

open import Agda.Primitive public using (
  -- Level, in Set₀
  Level) renaming (
  -- Zero level, in Level
  lzero to 0ᴸ;
  -- Successor level, in Level → Level
  lsuc to infix 10 ṡᴸ_;
  -- Maximum level, in Level → Level → Level
  _⊔_ to infixl 5 _⊔ᴸ_)

-- Shorthand for Level

1ᴸ 2ᴸ 3ᴸ :  Level
1ᴸ =  ṡᴸ 0ᴸ
2ᴸ =  ṡᴸ 1ᴸ
3ᴸ =  ṡᴸ 2ᴸ

-- Up : Wrapper raising the level

infix 8 ↑_
record  Up {ł : Level} (A : Set ł) {ł' : Level} :  Set (ł ⊔ᴸ ł')  where
  -- ↑/↓ : Wrap into / unwrap from Up
  constructor ↑_
  infix 8 ↓_
  field  ↓_ :  A
open Up public
