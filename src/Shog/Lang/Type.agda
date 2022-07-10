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
-- ValGen: Data for generating a value-type function

record  ValGen :  Set (^ ^ ℓ)  where
  field
    -- Defines the value-type for a non-pure type
    Val* :  Type →  Set (^ ℓ)
open ValGen public

-- Interpret (Φ : ValFn) as a value-type function (Type → Set ℓ),
-- mapping ◸ A to A, with a level tweak

Val :  ValGen →  Type →  Set (^ ℓ)
Val _ (◸ A) =  Up A
Val Φ T =  Φ .Val* T
