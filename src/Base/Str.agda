--------------------------------------------------------------------------------
-- Charactre and string
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Str where

open import Base.Eq using (_≡_; refl)
open import Base.Dec using (≡Dec; ≡Dec-inj)
open import Base.Nat using ()
open import Base.List using (List)

-- Import and re-export

open import Agda.Builtin.Char public using (
  -- Primitive character type
  -- Char :  Set₀
  Char) renaming (
  -- Inject Char into ℕ
  -- unchar :  Char →  ℕ
  primCharToNat to unchar)
open import Agda.Builtin.String public using () renaming (
  -- Str :  Set₀
  String to Str;
  -- Conversion between Str and List Char
  -- unstr :  Str →  List Char
  primStringToList to unstr;
  -- str :  Str →  List Char
  primStringFromList to str)

private variable
  c d :  Char
  cs ds :  List Char
  s t :  Str

open import Agda.Builtin.Char.Properties using (primCharToNatInjective)
open import Agda.Builtin.String.Properties using (primStringToListInjective;
  primStringFromListInjective)

abstract

  -- unchar is injective

  unchar-inj :  unchar c ≡ unchar d →  c ≡ d
  unchar-inj =  primCharToNatInjective _ _

  -- str and unstr are injective

  str-inj :  str cs ≡ str ds →  cs ≡ ds
  str-inj =  primStringFromListInjective _ _

  unstr-inj :  unstr s ≡ unstr t →  s ≡ t
  unstr-inj =  primStringToListInjective _ _

instance

  -- Equality decision on Char and Str

  Char-≡Dec :  ≡Dec Char
  Char-≡Dec =  ≡Dec-inj unchar unchar-inj

  Str-≡Dec :  ≡Dec Str
  Str-≡Dec =  ≡Dec-inj unstr unstr-inj
