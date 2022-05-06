--------------------------------------------------------------------------------
-- Conjunction over pairs of two lists
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.List.All2 where

open import Base.Level using (Level; _⊔ˡ_)
open import Base.List using (List; _∷_; []; _++_)
open import Base.Func using (_$_)

private variable
  ℓA ℓB ℓF : Level

--------------------------------------------------------------------------------
-- Conjunction over pairs of two lists
infixr 5 _∷ᴬ²_
data All² {A : Set ℓA} {B : Set ℓB} (F : A → B → Set ℓF) :
  List A → List B → Set (ℓA ⊔ˡ ℓB ⊔ˡ ℓF) where
  []ᴬ² : All² F [] []
  _∷ᴬ²_ : ∀ {a b as bs} → F a b → All² F as bs → All² F (a ∷ as) (b ∷ bs)
open All² public
