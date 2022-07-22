--------------------------------------------------------------------------------
-- Decision
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Dec where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.Few using (¬_)

private variable
  ℓA ℓB ℓF :  Level

--------------------------------------------------------------------------------
-- Decision on A
data  Dec {ℓA : Level} (A : Set ℓA) :  Set ℓA  where
  yes :  A →  Dec A
  no :  ¬ A →  Dec A

--------------------------------------------------------------------------------
-- Decision on a predicate

Dec¹ :  ∀ {A : Set ℓA} →  (A → Set ℓF) →  Set (ℓA ⊔ᴸ ℓF)
Dec¹ F =  ∀ a →  Dec (F a)

Dec² :  ∀ {A : Set ℓA} {B : Set ℓB} →  (A → B → Set ℓF) →  Set (ℓA ⊔ᴸ ℓB ⊔ᴸ ℓF)
Dec² F =  ∀ a b →  Dec (F a b)
