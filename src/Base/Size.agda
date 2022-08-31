--------------------------------------------------------------------------------
-- Size for sized types
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Base.Size where

open import Agda.Builtin.Size public using (
  -- Universe of Size
  SizeUniv;
  -- Size/ordinal, in SizeUniv
  Size;
  -- Inaccessible size/ordinal, in Size
  ∞) renaming (
  -- Maximum of Size, in Size → Size → Size
  _⊔ˢ_ to infixr 5 _⊔ˢ_;
  -- Size< ι :  Size smaller than ι, in SizeUniv
  Size<_ to Size<;
  -- Successor size, in Size → Size
  ↑_ to ṡˢ)
