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

infix 8 ◸_
infixr 4 _➔_

data  Type :  Set (^ ℓ)  where
  -- Embedding a pure type
  ◸_ :  Set ℓ →  Type
  -- Function
  _➔_ :  Type →  Type →  Type

--------------------------------------------------------------------------------
-- VtyGen: Data for generating a value-type function

record  VtyGen :  Set (^ ^ ℓ)  where
  field
    -- Defines the value-type for a non-pure type
    Vty* :  Type →  Set (^ ℓ)
open VtyGen public

-- Interpret (Φ : VtyFn) as a value-type function (Type → Set ℓ),
-- mapping ◸ A to A, with a level tweak
Vty :  VtyGen →  Type →  Set (^ ℓ)
Vty _ (◸ A) =  Up A
Vty Φ T =  Φ .Vty* T
