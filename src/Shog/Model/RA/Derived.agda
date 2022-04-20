----------------------------------------------------------------------
-- Derived notions and lemmas on a resource algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Shog.Model.RA.Base using (RA)

module Shog.Model.RA.Derived {ℓ ℓ≈ ℓ✓} (Ra : RA ℓ ℓ≈ ℓ✓) where
open RA Ra public using (
  Car; _≈_; ✓; _∙_; ⌞_⌟; idᵉ; symm; _»ᵉ_; ✓-cong; ✓-rem;
  ∙-cong₀; ∙-comm; ∙-assoc₀; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unit₀; ⌞⌟-idem)

open import Level using (Level; _⊔_)
open import Size using (Size; ∞)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe.Base using (Maybe; just; nothing)
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

∙-assoc₁ : a ∙ (b ∙ c) ≈ (a ∙ b) ∙ c
∙-assoc₁ = ∙-comm »ᵉ ∙-cong₀ ∙-comm »ᵉ ∙-assoc₀ »ᵉ ∙-comm »ᵉ ∙-cong₀ ∙-comm

----------------------------------------------------------------------
-- On ⌞⌟

⌞⌟-unit₁ : ⌞ a ⌟ ≡ just a' → a ∙ a' ≈ a
⌞⌟-unit₁ ⌞a⌟a' = ∙-comm »ᵉ ⌞⌟-unit₀ ⌞a⌟a'

----------------------------------------------------------------------
-- ᵐ∙: ∙ with Maybe

infixl 7 _ᵐ∙_

_ᵐ∙_ : Maybe Car → Car → Car
just a ᵐ∙ b = a ∙ b
nothing ᵐ∙ b = b

----------------------------------------------------------------------
-- ≤: Derived pre-order

infix 4 _≤_

_≤_ : Car → Car → Set (ℓ ⊔ ℓ≈)
a ≤ b = ∃[ cᵐ ] cᵐ ᵐ∙ a ≈ b

----------------------------------------------------------------------
-- On ≤

-- ≤ is reflexive

≈⇒≤ : a ≈ b → a ≤ b
≈⇒≤ a≈b = nothing , a≈b

idᵒ : a ≤ a
idᵒ = ≈⇒≤ idᵉ

-- ≤ is transitive and preserves ≈

infixr -1 _»ᵒ_ _ᵉ»ᵒ_ _ᵒ»ᵉ_ -- the same fixity with _$_

_»ᵒ_ : a ≤ b → b ≤ c → a ≤ c
(just d , d∙a≈b) »ᵒ (just e , e∙b≈c) = just (d ∙ e) ,
  (∙-cong₀ ∙-comm »ᵉ ∙-assoc₀ »ᵉ ∙-cong₁ d∙a≈b »ᵉ e∙b≈c)
(just d , d∙a≈b) »ᵒ (nothing , b≈c) = just d , (d∙a≈b »ᵉ b≈c)
(nothing , a≈b) »ᵒ (just e , e∙b≈c) = just e , (∙-cong₁ a≈b »ᵉ e∙b≈c)
(nothing , a≈b) »ᵒ (nothing , b≈c) = nothing , (a≈b »ᵉ b≈c)

_ᵉ»ᵒ_ : a ≈ b → b ≤ c → a ≤ c
a≈b ᵉ»ᵒ (just d , d∙b≈c) = just d , (∙-cong₁ a≈b »ᵉ d∙b≈c)
a≈b ᵉ»ᵒ (nothing , b≈c) = nothing , (a≈b »ᵉ b≈c)

_ᵒ»ᵉ_ : a ≤ b → b ≈ c → a ≤ c
(just d , d∙a≈b) ᵒ»ᵉ b≈c = just d , (d∙a≈b »ᵉ b≈c)
(nothing , a≈b) ᵒ»ᵉ b≈c = nothing , (a≈b »ᵉ b≈c)

-- ∙ is increasing

∙-incr : ∀ b → a ≤ b ∙ a
∙-incr b = just b , idᵉ

----------------------------------------------------------------------
-- Monotonicity of ✓, ∙ and ⌞⌟

✓-mono : a ≤ b → ✓ b → ✓ a
✓-mono (just c , c∙a≈b) ✓b = ✓-rem $ ✓-cong (symm c∙a≈b) ✓b
✓-mono (nothing , a≈b) ✓b = ✓-cong (symm a≈b) ✓b

∙-mono₀ : a ≤ b → a ∙ c ≤ b ∙ c
∙-mono₀ (just d , d∙a≈b) = just d , (∙-assoc₁ »ᵉ ∙-cong₀ d∙a≈b)
∙-mono₀ (nothing , a≈b) = nothing , ∙-cong₀ a≈b

∙-mono₁ : a ≤ b → c ∙ a ≤ c ∙ b
∙-mono₁ a≤b = ∙-comm ᵉ»ᵒ ∙-mono₀ a≤b ᵒ»ᵉ ∙-comm

∙-mono : a ≤ b → c ≤ d → a ∙ c ≤ b ∙ d
∙-mono a≤b c≤d = ∙-mono₀ a≤b »ᵒ ∙-mono₁ c≤d

⌞⌟-mono : a ≤ b → ⌞ a ⌟ ≡ just a' → ∃[ b' ] ⌞ b ⌟ ≡ just b' × a' ≤ b'
⌞⌟-mono (just c , c∙a≈b) ⌞a⌟a' with ⌞⌟-add {b = c} ⌞a⌟a'
... | d' , ⌞c∙a⌟d' , e' , e'∙a'≈d' with ⌞⌟-cong c∙a≈b ⌞c∙a⌟d'
...   | b' , ⌞b⌟b' , d'≈b' = b' , ⌞b⌟b' , (∙-incr e' ᵒ»ᵉ e'∙a'≈d' »ᵉ d'≈b')
⌞⌟-mono (nothing , a≈b) ⌞a⌟a' with ⌞⌟-cong a≈b ⌞a⌟a'
... | b' , ⌞b⌟b' , a'≈b' = b' , ⌞b⌟b' , ≈⇒≤ a'≈b'

----------------------------------------------------------------------
-- ~>/~>: : Resource update

infix 2 _~>_ _~>:_

-- a ~> b : a can be updated into b, regardless of the frame cᵐ
_~>_ : Car → Car → Set (ℓ ⊔ ℓ✓)
a ~> b = ∀ cᵐ → ✓ (cᵐ ᵐ∙ a) → ✓ (cᵐ ᵐ∙ b)

-- a ~>: B : a can be updated into b, regardless of the frame cᵐ
_~>:_ : Car → (Car → Set ℓB) → Set (ℓ ⊔ ℓ✓ ⊔ ℓB)
a ~>: B = ∀ cᵐ → ✓ (cᵐ ᵐ∙ a) → ∃[ b ] B b × ✓ (cᵐ ᵐ∙ b)

----------------------------------------------------------------------
-- ⊆≈ : Set inclusion relaxed with ≈

infix 4 _⊆≈_

_⊆≈_ : (Car → Set ℓA) → (Car → Set ℓB) → Set (ℓ ⊔ ℓ≈ ⊔ ℓA ⊔ ℓB)
A ⊆≈ B = ∀ a → A a → ∃[ b ] a ≈ b × B b

----------------------------------------------------------------------
-- On ⊆≈

-- ⊆≈ is reflexive

⊆≈-id : A ⊆≈ A
⊆≈-id a Aa = a , idᵉ , Aa

-- ⊆≈ is transitive

infixr -1 _[⊆≈]»_

_[⊆≈]»_ : A ⊆≈ B → B ⊆≈ C → A ⊆≈ C
(A⊆≈B [⊆≈]» B⊆≈C) a Aa with A⊆≈B a Aa
... | b , a≈b , Bb with B⊆≈C b Bb
...   | c , b≈c , Cc = c , (a≈b »ᵉ b≈c) , Cc

----------------------------------------------------------------------
-- On ~>/~>:

-- ~> into ~>:
~>⇒~>: : ∀ b → a ~> b → a ~>: (b ≡_)
~>⇒~>: b a~>b cᵐ ✓cᵐ∙a = b , refl , a~>b cᵐ ✓cᵐ∙a

-- ~> respects ≈

~>-cong : a ≈ a' → b ≈ b' → a ~> b → a' ~> b'
~>-cong a≈a' b≈b' a~>b (just c) ✓c∙a' =
  ✓-cong (∙-cong₁ b≈b') $ a~>b (just c) $ ✓-cong (∙-cong₁ $ symm a≈a') ✓c∙a'
~>-cong a≈a' b≈b' a~>b nothing ✓a' =
  ✓-cong b≈b' $ a~>b nothing $ ✓-cong (symm a≈a') ✓a'

~>-cong₀ : a ≈ a' → a ~> b → a' ~> b
~>-cong₀ a≈a' = ~>-cong a≈a' idᵉ

~>-cong₁ : b ≈ b' → a ~> b → a ~> b'
~>-cong₁ = ~>-cong idᵉ

-- ~>: respects ≈

~>:-cong : a ≈ a' → B ⊆≈ B' → a ~>: B → a' ~>: B'
~>:-cong a≈a' B⊆≈B' a~>:B (just c) ✓c∙a'
  with a~>:B (just c) $ ✓-cong (∙-cong₁ $ symm a≈a') ✓c∙a'
... | b , Bb , ✓c∙b with B⊆≈B' b Bb
...   | b' , b≈b' , B'b' = b' , B'b' , ✓-cong (∙-cong₁ b≈b') ✓c∙b
~>:-cong a≈a' B⊆≈B' a~>:B nothing ✓a'
  with a~>:B nothing $ ✓-cong (symm a≈a') ✓a'
... | b , Bb , ✓b with B⊆≈B' b Bb
...   | b' , b≈b' , B'b' = b' , B'b' , ✓-cong b≈b' ✓b

~>:-cong₀ : a ≈ a' → a ~>: B → a' ~>: B
~>:-cong₀ a≈a' = ~>:-cong a≈a' ⊆≈-id

~>:-cong₁ : B ⊆≈ B' → a ~>: B → a ~>: B'
~>:-cong₁ = ~>:-cong idᵉ

-- ~> is reflexive

~>-id : a ~> a
~>-id _ ✓cᵐ∙a = ✓cᵐ∙a

infixr -1 _[~>]»_ _[~>]»[~>:]_

-- ~> is transitive

_[~>]»_ : a ~> b → b ~> c → a ~> c
(a~>b [~>]» b~>c) dᵐ ✓dᵐ∙a = b~>c dᵐ $ a~>b dᵐ ✓dᵐ∙a

-- ~>: respects ~>

_[~>]»[~>:]_ : a ~> b → b ~>: C → a ~>: C
(a~>b [~>]»[~>:] b~>C) dᵐ ✓dᵐ∙a = b~>C dᵐ $ a~>b dᵐ ✓dᵐ∙a

-- ~>/~>: can be merged with respect to ∙

~>-∙ : ∀ a d → a ~> b → c ~> d → a ∙ c ~> b ∙ d
~>-∙ a d a~>b c~>d (just e) ✓e∙a∙c = ✓-cong (∙-assoc₀ »ᵉ ∙-cong₁ ∙-comm) $
  a~>b (just $ e ∙ d) $ ✓-cong (∙-assoc₀ »ᵉ ∙-cong₁ ∙-comm »ᵉ ∙-assoc₁) $
  c~>d (just $ e ∙ a) $ ✓-cong ∙-assoc₁ ✓e∙a∙c
~>-∙ a d a~>b c~>d nothing ✓a∙c = ✓-cong ∙-comm $
  a~>b (just d) $ ✓-cong ∙-comm $ c~>d (just a) ✓a∙c

~>:-∙ : ∀ a → a ~>: B → c ~>: D →
  a ∙ c ~>: λ bd → ∃[ b ] B b × ∃[ d ] D d × bd ≡ b ∙ d
~>:-∙ a a~>:B c~>:D (just e) ✓e∙a∙c with
  c~>:D (just $ e ∙ a) $ ✓-cong ∙-assoc₁ ✓e∙a∙c
... | d , Dd , ✓e∙a∙d with
  a~>:B (just $ e ∙ d) $ ✓-cong (∙-assoc₀ »ᵉ ∙-cong₁ ∙-comm »ᵉ ∙-assoc₁) ✓e∙a∙d
...   | b , Bb , ✓e∙d∙b = b ∙ d , (b , Bb , d , Dd , refl) ,
  ✓-cong (∙-assoc₀ »ᵉ ∙-cong₁ ∙-comm) ✓e∙d∙b
~>:-∙ a a~>:B c~>:D nothing ✓a∙c with c~>:D (just a) ✓a∙c
... | d , Dd , ✓a∙d with a~>:B (just d) $ ✓-cong ∙-comm ✓a∙d
...   | b , Bb , ✓d∙b = b ∙ d , (b , Bb , d , Dd , refl) , ✓-cong ∙-comm ✓d∙b
