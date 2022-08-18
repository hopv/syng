--------------------------------------------------------------------------------
-- Thunk for sized coinductive(-inductive) data types
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Base.Thunk where

open import Base.Level using (Level)
open import Base.Size using (Size; Size<)

--------------------------------------------------------------------------------
-- Thunk, for coinductive or coinductive-inductive data types

infix 8 ¡_
record  Thunk {ł : Level} (F : Size → Set ł) (ι : Size) :  Set ł  where
  coinductive
  constructor ¡_
  field  ! :  {ι' : Size< ι} →  F ι'
open Thunk public
