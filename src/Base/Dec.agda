--------------------------------------------------------------------------------
-- Decision
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Dec where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.Few using (¬_)

private variable
  ł ł' ł'' :  Level
  A B : Set ł

--------------------------------------------------------------------------------
-- Decision on A
data  Dec (A : Set ł) :  Set ł  where
  yes :  A →  Dec A
  no :  ¬ A →  Dec A

--------------------------------------------------------------------------------
-- Decision on a predicate

Dec¹ :  ∀{A : Set ł} →  (A → Set ł') →  Set (ł ⊔ᴸ ł')
Dec¹ F =  ∀ a →  Dec (F a)

Dec² :  ∀{A : Set ł} {B : Set ł'} →  (A → B → Set ł'') →  Set (ł ⊔ᴸ ł' ⊔ᴸ ł'')
Dec² F =  ∀ a b →  Dec (F a b)
