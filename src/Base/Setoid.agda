--------------------------------------------------------------------------------
-- Setoid
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Setoid where

open import Base.Level using (Level; _⊔ᴸ_; sucᴸ)
open import Base.Eq using (_≡_; refl; ◠_; _◇_)
open import Base.Few using (¬_)
open import Base.Func using (_∈_)
open import Base.Prod using (_×_; ∑-syntax; _,_)

record  Setoid ℓ ℓ≈ :  Set (sucᴸ (ℓ ⊔ᴸ ℓ≈))  where
  infix 4 _≈_
  infix 0 ◠˜_
  infixr -1 _◇˜_
  field
    -- Car :  Carrier set
    Car :  Set ℓ
    -- ≈ :  Binary relation over Car
    _≈_ :  Car → Car → Set ℓ≈
    -- ≈ is reflexive, symmetric and transitive
    refl˜ :  ∀ {a} →  a ≈ a
    ◠˜_ :  ∀ {a b} →  a ≈ b →  b ≈ a
    _◇˜_ :  ∀ {a b c} →  a ≈ b →  b ≈ c →  a ≈ c

  private variable
    a b :  Car

  ≡⇒≈ :  a ≡ b →  a ≈ b
  ≡⇒≈ refl =  refl˜

  ------------------------------------------------------------------------------
  -- ≉ :  Negation of ≈

  infix 4 _≉_
  _≉_ :  Car → Car → Set ℓ≈
  a ≉ b =  ¬  a ≈ b

open Setoid

private variable
  ℓA :  Level

≡-setoid :  Set ℓA →  Setoid ℓA ℓA
≡-setoid A .Car =  A
≡-setoid _ ._≈_ =  _≡_
≡-setoid _ .refl˜ =  refl
≡-setoid _ .◠˜_ =  ◠_
≡-setoid _ ._◇˜_ =  _◇_
