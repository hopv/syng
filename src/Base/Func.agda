--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Func where

open import Base.Level using (Level)

private variable
  ł :  Level
  A B C :  Set ł
  B˙ :  A →  Set ł
  C˙˙ :  A →  B →  Set ł

-- Identity

id :  A →  A
id a =  a

-- Constant

const :  A →  B →  A
const a _ =  a

-- Composition

infixr 9 _∘_
_∘_ :  ∀{C˙˙ : ∀ a → B˙ a → Set ł} →
  (∀{a} b → C˙˙ a b) →  (f : ∀ a → B˙ a) →  (a : A) →  C˙˙ a (f a)
(g ∘ f) a =  g (f a)

-- Flipped non-dependent composition

infixr -1 _›_
_›_ : (A → B) →  (B → C) →  A → C
(f › g) a =  g (f a)

-- Function application

infixr -1 _$_
_$_ :  (∀ a → B˙ a) →  ∀ a →  B˙ a
f $ a =  f a

-- Flipped non-dependent function application

infixl 0 _▷_
_▷_ :  A →  (A → B) →  B
a ▷ f =  f a

-- Flip the order of arguments

flip :  (∀ a b → C˙˙ a b) →  ∀ b a →  C˙˙ a b
flip f b a =  f a b

-- Instance search

it :  {{A}} →  A
it {{a}} =  a
