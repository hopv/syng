--------------------------------------------------------------------------------
-- Sigma and product type
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Prod where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.Func using (_$_; it)
open import Base.Eq using (_≡_; refl; subst; Uip; ≡refl)
open import Base.Dec using (Dec; yes; no; ≡Dec; _≟_)

--------------------------------------------------------------------------------
-- Sigma type

-- Import and re-export
open import Agda.Builtin.Sigma public using () renaming (
  -- Sigma type, or dependent pair type
  -- ∑˙ :  ∀(A : Set ł) →  (A → Set ł') →  Set (ł ⊔ ł')
  Σ to ∑˙;
  -- Pair constructor
  -- _,_ :  A →  B˙ A →  ∑˙ A B˙
  _,_ to infixr -3 _,_;
  -- The zeroth (left-hand) component of a pair
  -- π₀ :  ∑˙ A B˙ →  A
  fst to π₀;
  -- The first (right-hand) component of a pair
  -- π₁ :  ∀(p : ∑˙ A B˙) →  B˙ (p .π₀)
  snd to π₁)

private variable
  ł ł' :  Level
  A B C :  Set ł
  B˙ :  A →  Set ł
  a  a' b b' :  A

-- Syntax for ∑

infix -1 ∑∈-syntax ∑-syntax
∑∈-syntax ∑-syntax :  ∀{A : Set ł} →  (A → Set ł') →  Set (ł ⊔ᴸ ł')
∑∈-syntax =  ∑˙ _
∑-syntax =  ∑˙ _
syntax ∑∈-syntax {A = A} (λ a → b) =  ∑ a ∈ A , b
syntax ∑-syntax (λ a → B) =  ∑ a , B

infix -3 -,_ _,-
pattern -,_ b =  _ , b
pattern _,- a =  a , _

abstract

  -- Case analysis of ∑

  ∑-case :  (∀ a →  B˙ a → C) →  ∑˙ A B˙ →  C
  ∑-case Ba⇒C (a , b) =  Ba⇒C a b

  -- Destruct equality on a dependent pair

  ≡∑⇒π₀≡π₁≡ :  _≡_ {A = ∑˙ A B˙} (a , b) (a' , b') →
               ∑ eq ∈ a ≡ a' , subst B˙ eq b ≡ b'
  ≡∑⇒π₀≡π₁≡ refl =  refl , refl

  -- Destruct equality on a dependent pair of the same π₀,
  -- assuming that π₀'s type satisfies Uip

  ≡∑⇒π₁≡ :  {{Uip A}} →  _≡_ {A = ∑˙ A B˙} (a , b) (a , b') →  b ≡ b'
  ≡∑⇒π₁≡ {{UipA}} ab≡ab'  with ≡∑⇒π₀≡π₁≡ ab≡ab'
  … | a≡a , b≡b'  rewrite ≡refl {{UipA}} a≡a =  b≡b'

--------------------------------------------------------------------------------
-- Product type

infixr 1 _×_
_×_ :  Set ł →  Set ł' →  Set (ł ⊔ᴸ ł')
A × B =  ∑ _ ∈ A , B

-- curry/uncurry :  Curry and uncurry

curry :  (A × B → C) →  (A → B → C)
curry f a b =  f (a , b)

uncurry :  (A → B → C) →  (A × B → C)
uncurry f (a , b) =  f a b

instance

  -- Instance search for ×

  ,-it :  {{A}} →  {{B}} →  A × B
  ,-it =  it , it

  -- Derive Dec on ×

  ×-Dec :  {{Dec A}} →  {{Dec B}} →  Dec $ A × B
  ×-Dec {{yes a}} {{yes b}} =  yes (a , b)
  ×-Dec {{no ¬a}} =  no λ (a ,-) → ¬a a
  ×-Dec {{_}} {{no ¬b}} =  no λ (-, b) → ¬b b

  -- Equality decision for ×

  ×-≡Dec :  {{≡Dec A}} →  {{≡Dec B}} →  ≡Dec $ A × B
  ×-≡Dec ._≟_ (a , b) (a' , b')  with a ≟ a' | b ≟ b'
  … | yes refl | yes refl =  yes refl
  … | no a≢a' | _ =  no λ{ refl → a≢a' refl }
  … | _ | no b≢b' =  no λ{ refl → b≢b' refl }

--------------------------------------------------------------------------------
-- ∑ᴵ :  Sigma type with an instance

infix -3 -ᴵ,_
data  ∑ᴵ˙ (A : Set ł) (B˙ : A → Set ł') :  Set (ł ⊔ᴸ ł')  where
  -ᴵ,_ :  ∀{{a : A}} →  B˙ a →  ∑ᴵ˙ A B˙

infixr -3 _ᴵ,_
pattern _ᴵ,_ a b =  -ᴵ,_ {{a}} b

∑ᴵ∈-syntax ∑ᴵ-syntax :  ∀{A : Set ł} →  (B : A → Set ł') →  Set (ł ⊔ᴸ ł')
∑ᴵ∈-syntax =  ∑ᴵ˙ _
∑ᴵ-syntax =  ∑ᴵ˙ _
infix -1 ∑ᴵ∈-syntax ∑ᴵ-syntax
syntax ∑ᴵ∈-syntax {A = A} (λ a → B) =  ∑ᴵ a ∈ A , B
syntax ∑ᴵ-syntax (λ a → B) =  ∑ᴵ a , B

abstract

  -- Case analysis of ∑ᴵ

  ∑ᴵ-case :  (∀{{a}} →  B˙ a → C) →  ∑ᴵ˙ A B˙ →  C
  ∑ᴵ-case Ba⇒C (-ᴵ, b) =  Ba⇒C b
