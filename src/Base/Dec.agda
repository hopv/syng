--------------------------------------------------------------------------------
-- Decision
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Dec where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.Few using (¬_)

private variable
  ΛA ΛB ΛF :  Level

--------------------------------------------------------------------------------
-- Decision on A
data  Dec {ΛA : Level} (A : Set ΛA) :  Set ΛA  where
  yes :  A →  Dec A
  no :  ¬ A →  Dec A

--------------------------------------------------------------------------------
-- Decision on a predicate

Dec¹ :  ∀ {A : Set ΛA} →  (A → Set ΛF) →  Set (ΛA ⊔ᴸ ΛF)
Dec¹ F =  ∀ a →  Dec (F a)

Dec² :  ∀ {A : Set ΛA} {B : Set ΛB} →  (A → B → Set ΛF) →  Set (ΛA ⊔ᴸ ΛB ⊔ᴸ ΛF)
Dec² F =  ∀ a b →  Dec (F a b)
