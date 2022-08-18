--------------------------------------------------------------------------------
-- Decision
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Dec where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.Few using (¬_)

private variable
  Λ Λ' Λ'' :  Level
  A B : Set Λ

--------------------------------------------------------------------------------
-- Decision on A
data  Dec (A : Set Λ) :  Set Λ  where
  yes :  A →  Dec A
  no :  ¬ A →  Dec A

--------------------------------------------------------------------------------
-- Decision on a predicate

Dec¹ :  ∀{A : Set Λ} →  (A → Set Λ') →  Set (Λ ⊔ᴸ Λ')
Dec¹ F =  ∀ a →  Dec (F a)

Dec² :  ∀{A : Set Λ} {B : Set Λ'} →  (A → B → Set Λ'') →  Set (Λ ⊔ᴸ Λ' ⊔ᴸ Λ'')
Dec² F =  ∀ a b →  Dec (F a b)
