----------------------------------------------------------------------
-- Resource Algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Shog.Model.RA where

open import Level using (Level; _⊔_; suc)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function.Base using (_$_)
open import Data.Product using (_×_; _,_; ∃-syntax)

----------------------------------------------------------------------
-- Resource algebra (Unital)
record RA ℓ ℓ≈ ℓ✓ : Set (suc (ℓ ⊔ ℓ≈ ⊔ ℓ✓)) where
  infix 4 _≈_
  infixl 7 _∙_
  infixr -1 _»ᵉ_ -- the same fixity with _$_
  field
    -- Carrier
    Car : Set ℓ
    ------------------------------------------------------------------
    -- Equivalence
    _≈_ : Car → Car → Set ℓ≈
    -- Validity
    ✓ : Car → Set ℓ✓
    -- Product
    _∙_ : Car → Car → Car
    -- Unit
    ε : Car
    -- Core
    ⌞_⌟ : Car → Car
    ------------------------------------------------------------------
    -- ≈ is reflexive, symmetric and transitive
    idᵉ : ∀ {a} → a ≈ a
    symᵉ : ∀ {a b} → a ≈ b → b ≈ a
    _»ᵉ_ : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
    ------------------------------------------------------------------
    -- ✓ respects ≈
    ✓-cong : ∀ {a b} → a ≈ b → ✓ a → ✓ b
    -- ✓ is kept after a resource is removed
    ✓-rem : ∀ {a b} → ✓ (b ∙ a) → ✓ a
    ------------------------------------------------------------------
    -- ∙ preserves ≈
    ∙-cong₀ : ∀ {a b c} → a ≈ b → a ∙ c ≈ b ∙ c
    -- ∙ is unital w.r.t. ε, commutative and associative
    ∙-ε₀ : ∀ {a} → ε ∙ a ≈ a
    ∙-comm : ∀ {a b} → a ∙ b ≈ b ∙ a
    ∙-assoc₀ : ∀ {a b c} → (a ∙ b) ∙ c ≈ a ∙ (b ∙ c)
    ------------------------------------------------------------------
    -- ⌞⌟ preserves ≈
    ⌞⌟-cong : ∀ {a b} → a ≈ b → ⌞ a ⌟ ≈ ⌞ b ⌟
    -- When ⌞⌟'s argument gets added, ⌞⌟'s result gets added
    ⌞⌟-add : ∀ {a b} → ∃[ b' ] b' ∙ ⌞ a ⌟ ≈ ⌞ b ∙ a ⌟
    -- ⌞ a ⌟ is absorbed by a
    ⌞⌟-unit₀ : ∀ {a} → ⌞ a ⌟ ∙ a ≈ a
    -- ⌞⌟ is idempotent
    ⌞⌟-idem : ∀ {a} → ⌞ ⌞ a ⌟ ⌟ ≈ ⌞ a ⌟

  private variable
    a a' b b' c d : Car
    ℓA ℓB ℓB' ℓC ℓD ℓE : Level
    A : Car → Set ℓA
    B : Car → Set ℓB
    B' : Car → Set ℓB'
    C : Car → Set ℓC
    D : Car → Set ℓD
    E : Car → Set ℓE

  --------------------------------------------------------------------
  -- ∙ preserves ≈

  ∙-cong₁ : a ≈ b → c ∙ a ≈ c ∙ b
  ∙-cong₁ a≈b = ∙-comm »ᵉ ∙-cong₀ a≈b »ᵉ ∙-comm

  ∙-cong : a ≈ b → c ≈ d → a ∙ c ≈ b ∙ d
  ∙-cong a≈b c≈d = ∙-cong₀ a≈b »ᵉ ∙-cong₁ c≈d

  -- ∙ is unital w.r.t. ε and associative

  ∙-ε₁ : a ∙ ε ≈ a
  ∙-ε₁ = ∙-comm »ᵉ ∙-ε₀

  ∙-assoc₁ : a ∙ (b ∙ c) ≈ (a ∙ b) ∙ c
  ∙-assoc₁ = ∙-comm »ᵉ ∙-cong₀ ∙-comm »ᵉ ∙-assoc₀ »ᵉ ∙-comm »ᵉ ∙-cong₀ ∙-comm

  ----------------------------------------------------------------------
  -- ⌞⌟ is unital

  ⌞⌟-unit₁ : a ∙ ⌞ a ⌟ ≈ a
  ⌞⌟-unit₁ = ∙-comm »ᵉ ⌞⌟-unit₀

  ----------------------------------------------------------------------
  -- ≤: Derived pre-order

  infix 4 _≤_

  _≤_ : Car → Car → Set (ℓ ⊔ ℓ≈)
  a ≤ b = ∃[ c ] c ∙ a ≈ b

  ----------------------------------------------------------------------
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
  ✓-mono (c , c∙a≈b) ✓b = ✓-rem $ ✓-cong (symᵉ c∙a≈b) ✓b

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
    ✓-cong (∙-cong₁ b≈b') $ a~>b $ ✓-cong (∙-cong₁ $ symᵉ a≈a') ✓c∙a'

  ~>-cong₀ : a ≈ a' → a ~> b → a' ~> b
  ~>-cong₀ a≈a' = ~>-cong a≈a' idᵉ

  ~>-cong₁ : b ≈ b' → a ~> b → a ~> b'
  ~>-cong₁ = ~>-cong idᵉ

  -- ~>: respects ≈

  ~>:-cong : a ≈ a' → B ⊆≈ B' → a ~>: B → a' ~>: B'
  ~>:-cong a≈a' B⊆≈B' a~>:B ✓c∙a'
    with a~>:B $ ✓-cong (∙-cong₁ $ symᵉ a≈a') ✓c∙a'
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
  ~>-∙ a~>b c~>d ✓e∙a∙c = ✓-cong (∙-assoc₀ »ᵉ ∙-cong₁ ∙-comm) $
    a~>b $ ✓-cong (∙-assoc₀ »ᵉ ∙-cong₁ ∙-comm »ᵉ ∙-assoc₁) $
    c~>d $ ✓-cong ∙-assoc₁ ✓e∙a∙c

  ~>:-∙ : a ~>: B → c ~>: D →
    (∀ {b d} → B b → D d → ∃[ e ] E e × e ≈ b ∙ d) → a ∙ c ~>: E
  ~>:-∙ a~>:B c~>:D BDE ✓f∙a∙c with
    c~>:D $ ✓-cong ∙-assoc₁ ✓f∙a∙c
  ... | d , Dd , ✓f∙a∙d with
    a~>:B $ ✓-cong (∙-assoc₀ »ᵉ ∙-cong₁ ∙-comm »ᵉ ∙-assoc₁) ✓f∙a∙d
  ...   | b , Bb , ✓f∙d∙b with BDE Bb Dd
  ...     | e , Ee , e≈b∙d = e , Ee ,
    ✓-cong (∙-assoc₀ »ᵉ ∙-cong₁ $ ∙-comm »ᵉ symᵉ e≈b∙d) ✓f∙d∙b
