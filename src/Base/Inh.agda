--------------------------------------------------------------------------------
-- Inhabitance
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Inh where

open import Base.Level using (Level)
open import Base.Func using (_$_; it)
open import Base.Few using (⟨2⟩; 0₂; ⊤)
open import Base.Prod using (_×_; _,_)
open import Base.Sum using (_⨿_; ĩ₀_; ĩ₁_)
open import Base.Option using (¿_; ň)

private variable
  ł :  Level
  A B :  Set ł

--------------------------------------------------------------------------------
-- Inhabitance

-- Inh A :  A is inhabited

record  Inh (A : Set ł) :  Set ł  where
  -- inh :  Construct Inh
  constructor inh
  field
    -- any :  Arbitrarily taken inhabitant of A
    any :  A

open Inh {{…}} public

instance

  -- ⟨2⟩ and ⊤ are inhabited

  ⟨2⟩-Inh :  Inh $ ⟨2⟩ {ł}
  ⟨2⟩-Inh .any =  0₂

  ⊤-Inh :  Inh $ ⊤ {ł}
  ⊤-Inh .any =  _

  -- A × B is inhabited if both A and B are inhabited

  ×-Inh :  {{Inh A}} →  {{Inh B}} →  Inh $ A × B
  ×-Inh .any =  any , any

  -- ¿ A is inhabited

  ¿-Inh :  Inh $ ¿ A
  ¿-Inh .any =  ň

-- A ⨿ B is inhabited if either A or B is inhabited

⨿-Inh₀ :  {{Inh A}} →  Inh $ A ⨿ B
⨿-Inh₀ .any =  ĩ₀ any

⨿-Inh₁ :  {{Inh B}} →  Inh $ A ⨿ B
⨿-Inh₁ .any =  ĩ₁ any

-- A → B is inhabited if B is inhabited

→-Inh₁ :  {{Inh B}} →  Inh (A → B)
→-Inh₁ .any _ =  any
