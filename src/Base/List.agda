--------------------------------------------------------------------------------
-- Lists
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.List where

open import Base.Level using (Level)
open import Base.Eq using (_≡_; refl⁼)

private variable
  ℓA ℓB : Level
  A : Set ℓA
  B : Set ℓB

------------------------------------------------------------------------
-- List

open import Agda.Builtin.List public using (List; []; _∷_)

-- Singleton list

[_] : A → List A
[ a ] = a ∷ []

-- Map

map : (A → B) → List A → List B
map f [] = []
map f (a ∷ as) = f a ∷ map f as

-- Append

infixr 5 _++_
_++_ : List A → List A → List A
[] ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)

abstract

  -- ++ is associative

  ++-assoc : ∀ (as bs cs : List A) → (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
  ++-assoc [] _ _ = refl⁼
  ++-assoc (_ ∷ as) bs cs rewrite ++-assoc as bs cs = refl⁼
