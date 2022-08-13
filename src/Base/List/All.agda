--------------------------------------------------------------------------------
-- Conjunction over pairs of two lists
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.List.All where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.List using (List; _∷_; []; _++_)
open import Base.Few using (⊤)
open import Base.Prod using (_×_)

private variable
  ℓA ℓF :  Level
  A :  Set ℓA
  F :  A → Set ℓF
  a :  A
  as :  List A

--------------------------------------------------------------------------------
-- Conjunction over a list

All :  (A → Set ℓF) →  List A →  Set ℓF
All F [] =  ⊤
All F (a ∷ as) =  F a × All F as
