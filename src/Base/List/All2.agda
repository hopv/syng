--------------------------------------------------------------------------------
-- Conjunction over pairs of two lists
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.List.All2 where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.List using (List; _∷_; []; _++_)
open import Base.Func using (_$_)

private variable
  Λ Λ' Λ'' :  Level

--------------------------------------------------------------------------------
-- Conjunction over pairs of two lists

infixr 5 _∷ᴬ²_
data  All² {A : Set Λ} {B : Set Λ'} (F : A → B → Set Λ'') :
  List A →  List B →  Set (Λ ⊔ᴸ Λ' ⊔ᴸ Λ'')  where
  []ᴬ² :  All² F [] []
  _∷ᴬ²_ :  ∀ {a b as bs} →  F a b →  All² F as bs →  All² F (a ∷ as) (b ∷ bs)
open All² public
