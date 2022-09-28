--------------------------------------------------------------------------------
-- Option
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Option where

open import Base.Level using (Level)
open import Base.Func using (_$_)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using (Dec; yes; no; ≡Dec; _≟_)

--------------------------------------------------------------------------------
-- ¿ :  Option type

-- Import and re-export
open import Agda.Builtin.Maybe public using () renaming (
  -- Option type
  -- ¿_ :  Set ł →  Set ł
  Maybe to infix 8 ¿_;
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

-- ¿-case :  Case analysis of ¿

¿-case :  (A → B) →  B →  ¿ A →  B
¿-case f _ (š a) =  f a
¿-case _ b ň =  b

-- $¿ :  Map over an option

infixr -1 _$¿_
_$¿_ :  (A → B) →  ¿ A →  ¿ B
f $¿ š a =  š f a
f $¿ ň =  ň

-- »-¿ :  Bind over an option

infixr -1 _»-¿_
_»-¿_ :  ¿ A →  (A → ¿ B) →  ¿ B
š a »-¿ f =  f a
ň »-¿ _ =  ň

abstract

  -- š is injective

  š-inj :  š a ≡ š b →  a ≡ b
  š-inj refl =  refl

instance

  -- ¿ is inhabited

  ¿-Dec :  Dec $ ¿ A
  ¿-Dec =  yes ň

  -- Equality decision for ¿

  ¿-≡Dec :  {{≡Dec A}} →  ≡Dec $ ¿ A
  ¿-≡Dec ._≟_ ň ň =  yes refl
  ¿-≡Dec ._≟_ (š a) (š a')  with a ≟ a'
  … | yes refl =  yes refl
  … | no a≢a' =  no λ{ refl → a≢a' refl }
  ¿-≡Dec ._≟_ ň (š _) =  no λ ()
  ¿-≡Dec ._≟_ (š _) ň =  no λ ()
