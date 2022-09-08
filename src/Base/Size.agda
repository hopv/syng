--------------------------------------------------------------------------------
-- Size for sized types
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Base.Size where

open import Base.Level using (Level)

open import Agda.Builtin.Size public using (
  -- Universe of Size
  SizeUniv;
  -- Size/ordinal, in SizeUniv
  Size;
  -- Inaccessible size/ordinal, in Size
  ∞) renaming (
  -- Size< ι :  Size smaller than ι, in SizeUniv
  Size<_ to Size<;
  -- Successor size, in Size → Size
  ↑_ to infix 10 ṡˢ_;
  -- Maximum of Size, in Size → Size → Size
  _⊔ˢ_ to infixr 5 _⊔ˢ_)

--------------------------------------------------------------------------------
-- Thunk, for coinductive or coinductive-inductive data types

infix 8 ¡_
record  Thunk {ł : Level} (F : Size → Set ł) (ι : Size) :  Set ł  where
  coinductive
  constructor ¡_
  field  ! :  {ι' : Size< ι} →  F ι'
open Thunk public
