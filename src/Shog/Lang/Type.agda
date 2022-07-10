--------------------------------------------------------------------------------
-- Type
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Level using (Level)
module Shog.Lang.Type (ℓ : Level) where

open import Base.Level using (^_; Up)
open import Base.Func using (_$_)

--------------------------------------------------------------------------------
-- Type:  Simple type for expressions

infixr 4 _*→*_ _→*_

data  Type :  Set (^ ℓ)  where
  -- Embedding a pure type
  ⎡_⎤ :  Set ℓ →  Type
  -- Function
  _*→*_ :  Type →  Type →  Type

-- Function with a pure domain type
_→*_ :  Set ℓ →  Type →  Type
A →* T =  ⎡ A ⎤ *→* T

--------------------------------------------------------------------------------
-- VTF: Data defining a value-type function
record  VTF :  Set (^ ^ ℓ)  where
  field
    -- Defines the value-type for a non-pure type
    Vt* :  Type →  Set (^ ℓ)
open VTF public

-- Interpret (Φ : VTF) as a value-type function (Type → Set ℓ),
-- mapping ⎡ A ⎤ to A, with a level tweak
Vt :  VTF →  Type →  Set (^ ℓ)
Vt _ ⎡ A ⎤ =  Up A
Vt Φ (T *→* U) =  Φ .Vt* $ T *→* U
