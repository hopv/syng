--------------------------------------------------------------------------------
-- Booleans
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Bool where

open import Base.Eq using (refl)
open import Base.Dec using (Dec; yes; no; ≡Dec; _≟_)

--------------------------------------------------------------------------------
-- 𝔹 :  Boolean

open import Agda.Builtin.Bool public using () renaming (
  Bool to 𝔹; true to tt; false to ff)

instance

  -- 𝔹 is inhabited

  𝔹-Dec :  Dec 𝔹
  𝔹-Dec =  yes tt

  -- Equality decision for 𝔹

  𝔹-≡Dec :  ≡Dec 𝔹
  𝔹-≡Dec ._≟_ tt tt =  yes refl
  𝔹-≡Dec ._≟_ ff ff =  yes refl
  𝔹-≡Dec ._≟_ tt ff =  no λ ()
  𝔹-≡Dec ._≟_ ff tt =  no λ ()

-- And

infixr 7 _∧ᴮ_
_∧ᴮ_ :  𝔹 →  𝔹 →  𝔹
tt ∧ᴮ b =  b
ff ∧ᴮ _ =  ff

-- Or

infixr 6 _∨ᴮ_
_∨ᴮ_ :  𝔹 →  𝔹 →  𝔹
tt ∨ᴮ _ =  tt
ff ∨ᴮ b =  b
