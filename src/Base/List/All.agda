--------------------------------------------------------------------------------
-- Conjunction over pairs of two lists
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.List.All where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.List using (List; _∷_; []; _++_)
open import Base.Func using (_$_)

private variable
  ℓA ℓB ℓF :  Level

--------------------------------------------------------------------------------
-- Conjunction over pairs of two lists

infixr 5 _∷ᴬ_
data  All {A : Set ℓA} (F : A → Set ℓF) :
  List A →  Set (ℓA ⊔ᴸ ℓF)  where
  []ᴬ :  All F []
  _∷ᴬ_ :  ∀ {a as} →  F a →  All F as →  All F (a ∷ as)
open All public
