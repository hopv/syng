--------------------------------------------------------------------------------
-- Equality
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Eq where

open import Base.Level using (Level)
open import Base.Few using (¬_)

------------------------------------------------------------------------
-- ≡: Equality

open import Agda.Builtin.Equality public using (_≡_) renaming (refl to refl⁼)

private variable
  ℓA ℓB ℓC ℓF :  Level
  A :  Set ℓA
  B :  Set ℓB
  C :  Set ℓC
  a a' a'' :  A

-- Negation of _≡_
infix 4 _≢_
_≢_ :  ∀ {A : Set ℓA} →  A →  A →  Set ℓA
x ≢ y =  ¬  x ≡ y

abstract

  -- Congruence

  cong⁼ :  ∀ (f : A → B) {a a'} →  a ≡ a' →  f a ≡ f a'
  cong⁼ f refl⁼ =  refl⁼

  cong⁼₂ :  ∀ (f : A → B → C) {a a' b b'} →  a ≡ a' →  b ≡ b' →  f a b ≡ f a' b'
  cong⁼₂ f refl⁼ refl⁼ =  refl⁼

  -- ≡ is symmetric and transitive

  sym⁼ :  a ≡ a' →  a' ≡ a
  sym⁼ refl⁼ =  refl⁼

  infixr -1 _»⁼_
  _»⁼_ :  a ≡ a' →  a' ≡ a'' →  a ≡ a''
  refl⁼ »⁼ eq =  eq

  -- Substitution

  subst :  ∀ (F : A → Set ℓF) {a a'} →  a ≡ a' →  F a →  F a'
  subst _ refl⁼ Fa =  Fa

  subst₂ :  ∀ (F : A → B → Set ℓF) {a a' b b'} →
    a ≡ a' →  b ≡ b' →  F a b →  F a' b'
  subst₂ _ refl⁼ refl⁼ Fab =  Fab
