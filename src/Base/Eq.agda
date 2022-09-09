--------------------------------------------------------------------------------
-- Equality
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Eq where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.Few using (¬_)

--------------------------------------------------------------------------------
-- ≡ :  Equality

-- Import and re-export
open import Agda.Builtin.Equality public using (
  -- infix 4 _≡_
  -- _≡_ :  ∀{A : Set ł} →  A →  A →  Set ł
  _≡_;
  -- refl :  a ≡ a
  refl)

private variable
  ł ł' :  Level
  A B C :  Set ł
  B˙ :  A → Set ł
  a a' a'' :  A
  f g h :  ∀ a → B˙ a

-- Negation of _≡_
infix 4 _≢_
_≢_ :  ∀{A : Set ł} →  A →  A →  Set ł
x ≢ y =  ¬  x ≡ y

abstract

  -- Congruence

  cong :  ∀(f : A → B) {a a'} →  a ≡ a' →  f a ≡ f a'
  cong f refl =  refl

  cong₂ :  ∀(f : A → B → C) {a a' b b'} →  a ≡ a' →  b ≡ b' →  f a b ≡ f a' b'
  cong₂ f refl refl =  refl

  -- ≡ is symmetric and transitive

  infix 0 ◠_
  ◠_ :  a ≡ a' →  a' ≡ a
  ◠ refl =  refl

  infixr -1 _◇_
  _◇_ :  a ≡ a' →  a' ≡ a'' →  a ≡ a''
  refl ◇ eq =  eq

  -- Substitution

  subst :  ∀(F : A → Set ł) {a a'} →  a ≡ a' →  F a →  F a'
  subst _ refl Fa =  Fa

  subst₂ :  ∀(F : A → B → Set ł) {a a' b b'} →
    a ≡ a' →  b ≡ b' →  F a b →  F a' b'
  subst₂ _ refl refl Fab =  Fab

--------------------------------------------------------------------------------
-- ≡˙ :  Extentional equality of functions

infix 4 _≡˙_
_≡˙_ :  ∀{A : Set ł} {B˙ : A → Set ł'} →
  (∀ a → B˙ a) →  (∀ a → B˙ a) →  Set (ł ⊔ᴸ ł')
f ≡˙ g =  ∀ a →  f a ≡ g a

abstract

  -- ≡˙ is reflexive, symmetric and transitive

  refl˙ :  f ≡˙ f
  refl˙ _ =  refl

  ≡⇒≡˙ :  f ≡ g →  f ≡˙ g
  ≡⇒≡˙ refl =  refl˙

  infix 0 ◠˙_
  ◠˙_ :  f ≡˙ g →  g ≡˙ f
  (◠˙ f≡˙g) a  rewrite f≡˙g a =  refl

  infixr -1 _◇˙_
  _◇˙_ :  f ≡˙ g →  g ≡˙ h →  f ≡˙ h
  (f≡˙g ◇˙ g≡˙h) a  rewrite f≡˙g a | g≡˙h a =  refl
