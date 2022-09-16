--------------------------------------------------------------------------------
-- Option
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Option where

open import Base.Level using (Level)
open import Base.Eq using (_≡_; refl)

--------------------------------------------------------------------------------
-- ¿ :  Option type

-- Import and re-export
open import Agda.Builtin.Maybe public using () renaming (
  -- Option type
  -- ¿_ :  Set ł →  Set ł
  Maybe to infix 0 ¿_;
  -- Some
  -- š_ :  A →  ¿ A
  just to infix 8 š_;
  -- None
  -- ň :  ¿ A
  nothing to ň)

private variable
  ł :  Level
  A B :  Set ł
  a b :  A

¿-case :  (A → B) →  B →  ¿ A →  B
¿-case f _ (š a) =  f a
¿-case _ b ň =  b

infixr -1 _$¿_
_$¿_ :  (A → B) →  ¿ A →  ¿ B
f $¿ š a =  š f a
f $¿ ň =  ň

infixr -1 _»-¿_
_»-¿_ :  ¿ A →  (A → ¿ B) →  ¿ B
š a »-¿ f =  f a
ň »-¿ _ =  ň

abstract

  -- š is injective

  š-inj :  š a ≡ š b →  a ≡ b
  š-inj refl =  refl
