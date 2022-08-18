--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Func where

open import Base.Level using (Level)

private variable
  Λ :  Level
  A B :  Set Λ
  F :  A → Set Λ

-- Identity

id :  A → A
id a =  a

-- Constant

const :  A → B → A
const a _ =  a

-- Composition

infixr 9 _∘_
_∘_ :  ∀ {G : ∀ a → F a → Set Λ} →
  (∀ {a} b → G a b) →  (f : ∀ a → F a) →  (a : A) →  G a (f a)
(g ∘ f) a =  g (f a)

-- Function application

infixr -1 _$_
_$_ :  (∀ a → F a) → ∀ a → F a
f $ a =  f a

-- Flipped function application

infixl 0 _▷_
_▷_ :  ∀ a → (∀ a → F a) → F a
a ▷ f =  f a

-- Function application read as Membership

infix 4 _∈_
_∈_ :  A → (A → Set Λ) → Set Λ
a ∈ B =  B a

-- Flip the order of arguments

flip :  ∀ {F : A → B → Set Λ} → (∀ a b → F a b) → ∀ b a → F a b
flip f b a =  f a b

-- Instance search

it :  {{A}} → A
it {{a}} =  a
