----------------------------------------------------------------------
-- Derived notions and lemmas on a resource algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Shog.Model.RA.Base using (RA)

module Shog.Model.RA.Derived {ℓ ℓ≈ ℓ✓} (Ra : RA ℓ ℓ≈ ℓ✓) where
open RA Ra public using (
  Car; _≈_; ✓; _∙_; ε; ⌞_⌟; idᵉ; symm; _»ᵉ_; ✓-cong; ✓-rem;
  ∙-cong₀; ∙-ε₀; ∙-comm; ∙-assoc₀; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unit₀; ⌞⌟-idem)

open import Level using (Level; _⊔_)
open import Size using (Size; ∞)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function.Base using (_$_; case_of_)

private variable
  a a' b b' c d : Car
  ℓA ℓB ℓB' ℓC ℓD : Level
  A : Car → Set ℓA
  B : Car → Set ℓB
  B' : Car → Set ℓB'
  C : Car → Set ℓC
  D : Car → Set ℓD

----------------------------------------------------------------------
-- On ∙

∙-cong₁ : a ≈ b → c ∙ a ≈ c ∙ b
∙-cong₁ a≈b = ∙-comm »ᵉ ∙-cong₀ a≈b »ᵉ ∙-comm

∙-cong : a ≈ b → c ≈ d → a ∙ c ≈ b ∙ d
∙-cong a≈b c≈d = ∙-cong₀ a≈b »ᵉ ∙-cong₁ c≈d

∙-ε₁ : a ∙ ε ≈ a
∙-ε₁ = ∙-comm »ᵉ ∙-ε₀

∙-assoc₁ : a ∙ (b ∙ c) ≈ (a ∙ b) ∙ c
∙-assoc₁ = ∙-comm »ᵉ ∙-cong₀ ∙-comm »ᵉ ∙-assoc₀ »ᵉ ∙-comm »ᵉ ∙-cong₀ ∙-comm

----------------------------------------------------------------------
-- On ⌞⌟

⌞⌟-unit₁ : a ∙ ⌞ a ⌟ ≈ a
⌞⌟-unit₁ = ∙-comm »ᵉ ⌞⌟-unit₀

----------------------------------------------------------------------
-- ≤: Derived pre-order

infix 4 _≤_

_≤_ : Car → Car → Set (ℓ ⊔ ℓ≈)
a ≤ b = ∃[ c ] c ∙ a ≈ b

----------------------------------------------------------------------
-- On ≤

-- ≤ is reflexive

≈⇒≤ : a ≈ b → a ≤ b
≈⇒≤ a≈b = ε , (∙-ε₀ »ᵉ a≈b)

idᵒ : a ≤ a
idᵒ = ≈⇒≤ idᵉ

-- ≤ is transitive and preserves ≈

infixr -1 _»ᵒ_ _ᵉ»ᵒ_ _ᵒ»ᵉ_ -- the same fixity with _$_

_»ᵒ_ : a ≤ b → b ≤ c → a ≤ c
(d , d∙a≈b) »ᵒ (e , e∙b≈c) = (d ∙ e) ,
  (∙-cong₀ ∙-comm »ᵉ ∙-assoc₀ »ᵉ ∙-cong₁ d∙a≈b »ᵉ e∙b≈c)

_ᵉ»ᵒ_ : a ≈ b → b ≤ c → a ≤ c
a≈b ᵉ»ᵒ (d , d∙b≈c) = d , (∙-cong₁ a≈b »ᵉ d∙b≈c)

_ᵒ»ᵉ_ : a ≤ b → b ≈ c → a ≤ c
(d , d∙a≈b) ᵒ»ᵉ b≈c = d , (d∙a≈b »ᵉ b≈c)

-- ∙ is increasing

∙-incr : a ≤ b ∙ a
∙-incr {b = b} = b , idᵉ

-- Monotonicity of ✓, ∙ and ⌞⌟

✓-mono : a ≤ b → ✓ b → ✓ a
✓-mono (c , c∙a≈b) ✓b = ✓-rem $ ✓-cong (symm c∙a≈b) ✓b

∙-mono₀ : a ≤ b → a ∙ c ≤ b ∙ c
∙-mono₀ (d , d∙a≈b) = d , (∙-assoc₁ »ᵉ ∙-cong₀ d∙a≈b)

∙-mono₁ : a ≤ b → c ∙ a ≤ c ∙ b
∙-mono₁ a≤b = ∙-comm ᵉ»ᵒ ∙-mono₀ a≤b ᵒ»ᵉ ∙-comm

∙-mono : a ≤ b → c ≤ d → a ∙ c ≤ b ∙ d
∙-mono a≤b c≤d = ∙-mono₀ a≤b »ᵒ ∙-mono₁ c≤d

⌞⌟-mono : a ≤ b → ⌞ a ⌟ ≤ ⌞ b ⌟
⌞⌟-mono (c , c∙a≈b) with ⌞⌟-add
... | c' , c'∙⌞a⌟≈⌞c∙a⌟ = c' , (c'∙⌞a⌟≈⌞c∙a⌟ »ᵉ ⌞⌟-cong c∙a≈b)

----------------------------------------------------------------------
-- ~>/~>: : Resource update

infix 2 _~>_ _~>:_

-- a ~> b : a can be updated into b, regardless of the frame c
_~>_ : Car → Car → Set (ℓ ⊔ ℓ✓)
a ~> b = ∀ {c} → ✓ (c ∙ a) → ✓ (c ∙ b)

-- a ~>: B : a can be updated into b, regardless of the frame c
_~>:_ : Car → (Car → Set ℓB) → Set (ℓ ⊔ ℓ✓ ⊔ ℓB)
a ~>: B = ∀ {c} → ✓ (c ∙ a) → ∃[ b ] B b × ✓ (c ∙ b)

----------------------------------------------------------------------
-- ⊆≈ : Set inclusion relaxed with ≈

infix 4 _⊆≈_

_⊆≈_ : (Car → Set ℓA) → (Car → Set ℓB) → Set (ℓ ⊔ ℓ≈ ⊔ ℓA ⊔ ℓB)
A ⊆≈ B = ∀ {a} → A a → ∃[ b ] a ≈ b × B b

----------------------------------------------------------------------
-- On ⊆≈

-- ⊆≈ is reflexive

⊆≈-id : A ⊆≈ A
⊆≈-id {a = a} Aa = a , idᵉ , Aa

-- ⊆≈ is transitive

infixr -1 _[⊆≈]»_

_[⊆≈]»_ : A ⊆≈ B → B ⊆≈ C → A ⊆≈ C
(A⊆≈B [⊆≈]» B⊆≈C) Aa with A⊆≈B Aa
... | b , a≈b , Bb with B⊆≈C Bb
...   | c , b≈c , Cc = c , (a≈b »ᵉ b≈c) , Cc

----------------------------------------------------------------------
-- On ~>/~>:

-- ~> into ~>:
~>⇒~>: : a ~> b → a ~>: (b ≡_)
~>⇒~>: {b = b} a~>b ✓c∙a = b , refl , a~>b ✓c∙a

-- ~> respects ≈

~>-cong : a ≈ a' → b ≈ b' → a ~> b → a' ~> b'
~>-cong a≈a' b≈b' a~>b ✓c∙a' =
  ✓-cong (∙-cong₁ b≈b') $ a~>b $ ✓-cong (∙-cong₁ $ symm a≈a') ✓c∙a'

~>-cong₀ : a ≈ a' → a ~> b → a' ~> b
~>-cong₀ a≈a' = ~>-cong a≈a' idᵉ

~>-cong₁ : b ≈ b' → a ~> b → a ~> b'
~>-cong₁ = ~>-cong idᵉ

-- ~>: respects ≈

~>:-cong : a ≈ a' → B ⊆≈ B' → a ~>: B → a' ~>: B'
~>:-cong a≈a' B⊆≈B' a~>:B ✓c∙a'
  with a~>:B $ ✓-cong (∙-cong₁ $ symm a≈a') ✓c∙a'
... | b , Bb , ✓c∙b with B⊆≈B' Bb
...   | b' , b≈b' , B'b' = b' , B'b' , ✓-cong (∙-cong₁ b≈b') ✓c∙b

~>:-cong₀ : a ≈ a' → a ~>: B → a' ~>: B
~>:-cong₀ a≈a' = ~>:-cong a≈a' ⊆≈-id

~>:-cong₁ : B ⊆≈ B' → a ~>: B → a ~>: B'
~>:-cong₁ = ~>:-cong idᵉ

-- ~> is reflexive

~>-id : a ~> a
~>-id ✓c∙a = ✓c∙a

infixr -1 _[~>]»_ _[~>]»[~>:]_

-- ~> is transitive

_[~>]»_ : a ~> b → b ~> c → a ~> c
(a~>b [~>]» b~>c) ✓d∙a = b~>c $ a~>b ✓d∙a

-- ~>: respects ~>

_[~>]»[~>:]_ : a ~> b → b ~>: C → a ~>: C
(a~>b [~>]»[~>:] b~>C) ✓d∙a = b~>C $ a~>b ✓d∙a

-- ~>/~>: can be merged with respect to ∙

~>-∙ : a ~> b → c ~> d → a ∙ c ~> b ∙ d
~>-∙ {a = a} {d = d} a~>b c~>d ✓e∙a∙c = ✓-cong (∙-assoc₀ »ᵉ ∙-cong₁ ∙-comm) $
  a~>b $ ✓-cong (∙-assoc₀ »ᵉ ∙-cong₁ ∙-comm »ᵉ ∙-assoc₁) $
  c~>d $ ✓-cong ∙-assoc₁ ✓e∙a∙c

~>:-∙ : a ~>: B → c ~>: D →
  a ∙ c ~>: λ bd → ∃[ b ] B b × ∃[ d ] D d × bd ≡ b ∙ d
~>:-∙ {a = a} a~>:B c~>:D ✓e∙a∙c with
  c~>:D $ ✓-cong ∙-assoc₁ ✓e∙a∙c
... | d , Dd , ✓e∙a∙d with
  a~>:B $ ✓-cong (∙-assoc₀ »ᵉ ∙-cong₁ ∙-comm »ᵉ ∙-assoc₁) ✓e∙a∙d
...   | b , Bb , ✓e∙d∙b = b ∙ d , (b , Bb , d , Dd , refl) ,
  ✓-cong (∙-assoc₀ »ᵉ ∙-cong₁ ∙-comm) ✓e∙d∙b
