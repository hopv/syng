--------------------------------------------------------------------------------
-- Option
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Option where

open import Base.Level using (Level)

--------------------------------------------------------------------------------
-- ¿ :  Option type

open import Agda.Builtin.Maybe renaming (Maybe to infix 0 ¿_;
  just to infix 8 š_; nothing to ň) public

private variable
  ł :  Level
  A B :  Set ł

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
