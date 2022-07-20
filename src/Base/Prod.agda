--------------------------------------------------------------------------------
-- Sigma type / Product
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Prod where

open import Base.Level using (Level; _⌴_)

--------------------------------------------------------------------------------
-- Sigma type

open import Agda.Builtin.Sigma public
  renaming (Σ to ∑˙; _,_ to infixr -1 _,_; fst to proj₀; snd to proj₁)

private variable
  ℓA ℓB ℓC ℓF :  Level
  A :  Set ℓA
  B :  Set ℓB
  C :  Set ℓC

-- Syntax for ∑

infix 2 ∑∈-syntax ∑-syntax
∑∈-syntax :  ∀ (A : Set ℓA) →  (A → Set ℓF) →  Set (ℓA ⌴ ℓF)
∑∈-syntax =  ∑˙
∑-syntax :  ∀ {A : Set ℓA} →  (A → Set ℓF) →  Set (ℓA ⌴ ℓF)
∑-syntax =  ∑˙ _
syntax ∑∈-syntax A (λ a → b) =  ∑ a ∈ A , b
syntax ∑-syntax (λ a → B) =  ∑ a , B

--------------------------------------------------------------------------------
-- Product

infixr 2 _×_
_×_ :  Set ℓA →  Set ℓB →  Set (ℓA ⌴ ℓB)
A × B =  ∑ _ ∈ A , B

-- Curry and uncurry

curry :  (A × B → C) →  (A → B → C)
curry f a b =  f (a , b)

uncurry :  (A → B → C) →  (A × B → C)
uncurry f (a , b) =  f a b
