--------------------------------------------------------------------------------
-- Option
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Option where

open import Base.Level using (Level)

--------------------------------------------------------------------------------
-- ¿ :  Option type

open import Agda.Builtin.Maybe renaming (Maybe to infix 0 ¿_; just to some;
  nothing to none) public

private variable
  ł :  Level
  A B :  Set ł

¿-case :  (A → B) →  B →  ¿ A →  B
¿-case f _ (some a) =  f a
¿-case _ b none =  b

infixr -1 _$¿_
_$¿_ :  (A → B) →  ¿ A →  ¿ B
f $¿ some a =  some (f a)
f $¿ none =  none

infixr -1 _»-¿_
_»-¿_ :  ¿ A →  (A → ¿ B) →  ¿ B
some a »-¿ f =  f a
none »-¿ _ =  none
