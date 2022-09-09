--------------------------------------------------------------------------------
-- Size for sized types
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Base.Size where

open import Base.Level using (Level)

-- Import and re-export
open import Agda.Builtin.Size public using (
  -- Universe of Size
  SizeUniv;
  -- Size or ordinal
  -- Size :  SizeUniv
  Size;
  -- Inaccessible size/ordinal
  -- ∞ :  Size
  ∞) renaming (
  -- Subtype of Size, consisting of sizes smaller than the given size
  -- Size< :  Size →  SizeUniv
  Size<_ to Size<;
  -- Successor size
  -- ṡˢ :  Size →  Size
  ↑_ to infix 10 ṡˢ_;
  -- Maximum of Size
  -- _⊔ˢ_ :  Size →  Size →  Size
  _⊔ˢ_ to infixr 5 _⊔ˢ_)

--------------------------------------------------------------------------------
-- Thunk, for coinductive or coinductive-inductive data types

infix 8 ¡_
record  Thunk {ł : Level} (F : Size → Set ł) (ι : Size) :  Set ł  where
  coinductive
  constructor ¡_
  field  ! :  {ι' : Size< ι} →  F ι'
open Thunk public
