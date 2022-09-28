--------------------------------------------------------------------------------
-- Booleans
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Bool where

open import Base.Eq using (refl)
open import Base.Dec using (Dec; yes; no; ≡Dec; _≟_)

--------------------------------------------------------------------------------
-- Bool :  Boolean

open import Agda.Builtin.Bool public using (Bool)
  renaming (true to tt; false to ff)

instance

  -- Bool is inhabited

  Bool-Dec :  Dec Bool
  Bool-Dec =  yes tt

  -- Equality decision for Bool

  Bool-≡Dec :  ≡Dec Bool
  Bool-≡Dec ._≟_ tt tt =  yes refl
  Bool-≡Dec ._≟_ ff ff =  yes refl
  Bool-≡Dec ._≟_ tt ff =  no λ ()
  Bool-≡Dec ._≟_ ff tt =  no λ ()
