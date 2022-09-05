--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Func where

open import Base.Level using (Level)

private variable
  ł :  Level
  A B C :  Set ł
  F :  A → Set ł

-- Identity

id :  A → A
id a =  a

-- Constant

const :  A → B → A
const a _ =  a

-- Composition

infixr 9 _∘_
_∘_ :  ∀{G : ∀ a → F a → Set ł} →
  (∀{a} b → G a b) →  (f : ∀ a → F a) →  (a : A) →  G a (f a)
(g ∘ f) a =  g (f a)

-- Flipped non-dependent composition

infixr -1 _›_
_›_ : (A → B) →  (B → C) →  A → C
(f › g) a =  g (f a)

-- Function application

infixr -1 _$_
_$_ :  (∀ a → F a) → ∀ a → F a
f $ a =  f a

-- Flipped non-dependent function application

infixl 0 _▷_
_▷_ :  A → (A → B) → B
a ▷ f =  f a

-- Flip the order of arguments

flip :  ∀{F : A → B → Set ł} → (∀ a b → F a b) → ∀ b a → F a b
flip f b a =  f a b

-- Instance search

it :  {{A}} → A
it {{a}} =  a
