--------------------------------------------------------------------------------
-- Sigma type / Product
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Prod where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.Func using (it)

--------------------------------------------------------------------------------
-- Sigma type

open import Agda.Builtin.Sigma public using () renaming (Σ to ∑˙;
  _,_ to infixr -2 _,_; fst to proj₀; snd to proj₁)

private variable
  ł ł' :  Level
  A B C :  Set ł
  B˙ :  A →  Set ł

-- Syntax for ∑

infix -1 ∑∈-syntax ∑-syntax
∑∈-syntax ∑-syntax :  ∀{A : Set ł} →  (A → Set ł') →  Set (ł ⊔ᴸ ł')
∑∈-syntax =  ∑˙ _
∑-syntax =  ∑˙ _
syntax ∑∈-syntax {A = A} (λ a → b) =  ∑ a ∈ A , b
syntax ∑-syntax (λ a → B) =  ∑ a , B

infix -2 -,_
pattern -,_ b =  _ , b

abstract

  ∑-case :  (∀ a →  B˙ a → C) →  (∑˙ A B˙ → C)
  ∑-case Ba⇒C (a , b) =  Ba⇒C a b

--------------------------------------------------------------------------------
-- Product

infixr 1 _×_
_×_ :  Set ł →  Set ł' →  Set (ł ⊔ᴸ ł')
A × B =  ∑ _ ∈ A , B

-- Curry and uncurry

curry :  (A × B → C) →  (A → B → C)
curry f a b =  f (a , b)

uncurry :  (A → B → C) →  (A × B → C)
uncurry f (a , b) =  f a b

instance

  ,-it :  {{A}} →  {{B}} →  A × B
  ,-it =  it , it

--------------------------------------------------------------------------------
-- ∑ᴵ :  Dependent sum with an instance

infix -2 -ᴵ,_
data  ∑ᴵ˙ (A : Set ł) (B˙ : A → Set ł') :  Set (ł ⊔ᴸ ł')  where
  -ᴵ,_ :  ∀{{a : A}} →  B˙ a →  ∑ᴵ˙ A B˙

infixr -2 _ᴵ,_
pattern _ᴵ,_ a b =  -ᴵ,_ {{a}} b

∑ᴵ∈-syntax ∑ᴵ-syntax :  ∀{A : Set ł} →  (B : A → Set ł') →  Set (ł ⊔ᴸ ł')
∑ᴵ∈-syntax =  ∑ᴵ˙ _
∑ᴵ-syntax =  ∑ᴵ˙ _
infix -1 ∑ᴵ∈-syntax ∑ᴵ-syntax
syntax ∑ᴵ∈-syntax {A = A} (λ a → B) =  ∑ᴵ a ∈ A , B
syntax ∑ᴵ-syntax (λ a → B) =  ∑ᴵ a , B

abstract

  ∑ᴵ-case :  (∀{{a}} →  B˙ a → C) →  (∑ᴵ˙ A B˙ → C)
  ∑ᴵ-case Ba⇒C (-ᴵ, b) =  Ba⇒C b
