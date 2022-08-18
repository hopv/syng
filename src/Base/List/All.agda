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
  ł :  Level
  A :  Set ł
  F :  A → Set ł
  a :  A
  as :  List A

--------------------------------------------------------------------------------
-- Conjunction over a list

All :  (A → Set ł) →  List A →  Set ł
All F [] =  ⊤
All F (a ∷ as) =  F a × All F as
