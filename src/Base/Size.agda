--------------------------------------------------------------------------------
-- Size, thunk and shrunk
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
  -- ṡˢ_ :  Size →  Size
  ↑_ to infix 10 ṡˢ_;
  -- Maximum of Size
  -- _⊔ˢ_ :  Size →  Size →  Size
  _⊔ˢ_ to infixr 5 _⊔ˢ_)

--------------------------------------------------------------------------------
-- Thunk, for coinductive or coinductive-inductive data types

infix 8 ¡_
record  Thunk {ł : Level} (F : Size → Set ł) (ι : Size) :  Set ł  where
  coinductive

  -- ¡ :  Construct a thunk
  constructor ¡_

  -- ! :  Force Thunk F ι into F ι' for any ι' < ι
  -- It can force Thunk F ∞ into F ∞ (when F satisfies some conditions)
  field  ! :  {ι' : Size< ι} →  F ι'

open Thunk public

--------------------------------------------------------------------------------
-- Shrunk, for inductive data types

infix 8 §_
data  Shrunk {ł : Level} (F : Size → Set ł) (ι : Size) :  Set ł  where
  -- Construct a shrunk
  §_ :  {ι' : Size< ι} →  F ι' →  Shrunk F ι
