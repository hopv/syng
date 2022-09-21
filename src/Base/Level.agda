--------------------------------------------------------------------------------
-- Universe level
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Level where

-- Import and re-export
open import Agda.Primitive public using (
  -- Universe level
  -- Level :  Set₀
  Level) renaming (
  -- Zero level
  -- 0ᴸ :  Level
  lzero to 0ᴸ;
  -- Successor level
  -- ṡᴸ_ :  Level →  Level
  lsuc to infix 10 ṡᴸ_;
  -- Maximum level
  -- _⊔ᴸ_ :  Level →  Level →  Level
  _⊔_ to infixl 5 _⊔ᴸ_)

private variable
  ł :  Level

-- Shorthand for Level

1ᴸ 2ᴸ 3ᴸ :  Level
1ᴸ =  ṡᴸ 0ᴸ
2ᴸ =  ṡᴸ 1ᴸ
3ᴸ =  ṡᴸ 2ᴸ

--------------------------------------------------------------------------------
-- Up :  Wrapper raising the level

infix 8 ↑_
record  Up (A : Set ł) {ł' : Level} :  Set (ł ⊔ᴸ ł')  where

  -- ↑ :  Wrap into Up
  constructor ↑_

  -- ↓ :  Unwrap from Up
  field  ↓ :  A

open Up public
