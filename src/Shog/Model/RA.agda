--------------------------------------------------------------------------------
-- Resource Algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Shog.Model.RA where

open import Base.Level using (Level; _⊔ˡ_; sucˡ)
open import Base.Eq using (_≡_; refl⁼)
open import Base.Func using (_$_; id; _▷_; _∈_)
open import Base.Prod using (_×_; _,_; Σ-syntax)
open import Base.Setoid using (Setoid)

--------------------------------------------------------------------------------
-- Resource algebra (Unital)
record RA ℓ ℓ≈ ℓ✓ : Set (sucˡ (ℓ ⊔ˡ ℓ≈ ⊔ˡ ℓ✓)) where
  ------------------------------------------------------------------------------
  -- Fields
  infix 4 _≈_
  infixl 7 _∙_
  infixr -1 _»˜_ -- the same fixity with _$_
  field
    -- Carrier set
    Car : Set ℓ
    ----------------------------------------------------------------------------
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
    ----------------------------------------------------------------------------
    -- ≈ is reflexive, symmetric and transitive
    refl˜ :  ∀ {a} →  a ≈ a
    sym˜ :  ∀ {a b} →  a ≈ b → b ≈ a
    _»˜_ :  ∀ {a b c} →  a ≈ b → b ≈ c → a ≈ c
    ----------------------------------------------------------------------------
    -- ∙ is congruent, unital with ε, commutative, and associative
    ∙-congˡ :  ∀ {a b c} →  a ≈ b → a ∙ c ≈ b ∙ c
    ∙-unitˡ :  ∀ {a} →  ε ∙ a ≈ a
    ∙-comm :  ∀ {a b} →  a ∙ b ≈ b ∙ a
    ∙-assocˡ :  ∀ {a b c} →  (a ∙ b) ∙ c ≈ a ∙ (b ∙ c)
    ----------------------------------------------------------------------------
    -- ✓ respects ≈
    ✓-resp :  ∀ {a b} →  a ≈ b  →  ✓ a  →  ✓ b
    -- ✓ is kept after a resource is removed
    ✓-rem :  ∀ {a b} →  ✓ (b ∙ a)  →  ✓ a
    -- ε satisfies ✓
    ✓-ε : ✓ ε
    ----------------------------------------------------------------------------
    -- ⌞⌟ preserves ≈
    ⌞⌟-cong :  ∀ {a b} →  a ≈ b  →  ⌞ a ⌟ ≈ ⌞ b ⌟
    -- When ⌞⌟'s argument gets added, ⌞⌟'s result gets added
    ⌞⌟-add :  ∀ {a b} →  Σ b' ,  b' ∙ ⌞ a ⌟ ≈ ⌞ b ∙ a ⌟
    -- ⌞ a ⌟ is absorbed by a
    ⌞⌟-unitˡ :  ∀ {a} →  ⌞ a ⌟ ∙ a  ≈  a
    -- ⌞⌟ is idempotent
    ⌞⌟-idem :  ∀ {a} →  ⌞ ⌞ a ⌟ ⌟ ≈ ⌞ a ⌟

  -- Setoid structure
  setoid : Setoid ℓ ℓ≈
  setoid = record{ Car = Car; _≈_ = _≈_; refl˜ = refl˜; sym˜ = sym˜;
    _»˜_ = _»˜_ }
  open Setoid setoid public hiding (Car; _≈_; refl˜; sym˜; _»˜_)

  private variable
    a a' b b' c d : Car
    ℓA ℓB ℓB' ℓC ℓD ℓE : Level
    A : Car → Set ℓA
    B : Car → Set ℓB
    B' : Car → Set ℓB'
    C : Car → Set ℓC
    D : Car → Set ℓD
    E : Car → Set ℓE

  ------------------------------------------------------------------------------
  -- Utility lemmas
  abstract

    -- Congruence, unitality and associativity

    ∙-congʳ :  a ≈ b  →  c ∙ a ≈ c ∙ b
    ∙-congʳ a≈b = ∙-comm »˜ ∙-congˡ a≈b »˜ ∙-comm

    ∙-unitʳ : a ∙ ε ≈ a
    ∙-unitʳ = ∙-comm »˜ ∙-unitˡ

    ∙-assocʳ : a ∙ (b ∙ c) ≈ (a ∙ b) ∙ c
    ∙-assocʳ = sym˜ ∙-assocˡ

    -- Variant of ⌞⌟-unitˡ

    ⌞⌟-unitʳ : a ∙ ⌞ a ⌟ ≈ a
    ⌞⌟-unitʳ = ∙-comm »˜ ⌞⌟-unitˡ

    -- ⌞ ε ⌟ is ε

    ⌞⌟-ε : ⌞ ε ⌟ ≈ ε
    ⌞⌟-ε = sym˜ ∙-unitʳ »˜ ⌞⌟-unitˡ

  ------------------------------------------------------------------------------
  -- ≤: Derived pre-order

  infix 4 _≤_
  _≤_ : Car → Car → Set (ℓ ⊔ˡ ℓ≈)
  a ≤ b  =  Σ c ,  c ∙ a  ≈  b

  abstract

    -- ≤ is reflexive

    ≈⇒≤ : a ≈ b → a ≤ b
    ≈⇒≤ a≈b = ε , (∙-unitˡ »˜ a≈b)

    ≤-refl˜ : a ≤ a
    ≤-refl˜ = ≈⇒≤ refl˜

    -- ≤ is transitive

    ≤-trans :  a ≤ b  →  b ≤ c  →  a ≤ c
    ≤-trans (d , d∙a≈b) (e , e∙b≈c)  =  (d ∙ e) ,
      (∙-congˡ ∙-comm »˜ ∙-assocˡ »˜ ∙-congʳ d∙a≈b »˜ e∙b≈c)

    infixr -1 _ᵒ»ᵒ_ _˜»ᵒ_ _ᵒ»˜_ -- the same fixity with _$_

    _ᵒ»ᵒ_ :  a ≤ b  →  b ≤ c  →  a ≤ c
    _ᵒ»ᵒ_ = ≤-trans

    _˜»ᵒ_ :  a ≈ b  →  b ≤ c  →  a ≤ c
    a≈b ˜»ᵒ b≤c = ≈⇒≤ a≈b ᵒ»ᵒ b≤c

    _ᵒ»˜_ :  a ≤ b  →  b ≈ c  →  a ≤ c
    a≤b ᵒ»˜ b≈c = a≤b ᵒ»ᵒ ≈⇒≤ b≈c

    -- ε is the minimum

    ε-min : ε ≤ a
    ε-min = _ , ∙-unitʳ

    -- ∙ is increasing

    ∙-incr :  a  ≤  b ∙ a
    ∙-incr = _ , refl˜

    -- Monotonicity of ✓, ∙ and ⌞⌟

    ✓-mono :  a ≤ b  →  ✓ b  →  ✓ a
    ✓-mono (c , c∙a≈b) ✓b   = ✓b ▷ ✓-resp (sym˜ c∙a≈b) ▷ ✓-rem

    ∙-monoˡ :  a ≤ b  →  a ∙ c  ≤  b ∙ c
    ∙-monoˡ (d , d∙a≈b) = d , (∙-assocʳ »˜ ∙-congˡ d∙a≈b)

    ∙-monoʳ :  a ≤ b  →  c ∙ a  ≤  c ∙ b
    ∙-monoʳ a≤b = ∙-comm ˜»ᵒ ∙-monoˡ a≤b ᵒ»˜ ∙-comm

    ∙-mono :  a ≤ b  →  c ≤ d  →  a ∙ c  ≤  b ∙ d
    ∙-mono a≤b c≤d = ∙-monoˡ a≤b ᵒ»ᵒ ∙-monoʳ c≤d

    ⌞⌟-mono :  a ≤ b  →  ⌞ a ⌟ ≤ ⌞ b ⌟
    ⌞⌟-mono (c , c∙a≈b) with ⌞⌟-add {_} {c}
    ... | c' , c'∙⌞a⌟≈⌞c∙a⌟  =  c' , (c'∙⌞a⌟≈⌞c∙a⌟ »˜ ⌞⌟-cong c∙a≈b)

  ------------------------------------------------------------------------------
  -- ↝/↝ˢ : Resource update

  infix 2 _↝_ _↝ˢ_

  -- a ↝ b : a can be updated into b, regardless of the frame c
  _↝_ : Car → Car → Set (ℓ ⊔ˡ ℓ✓)
  a ↝ b  =  ∀ c →  ✓ (c ∙ a)  →  ✓ (c ∙ b)

  -- a ↝ˢ B : a can be updated into b, regardless of the frame c
  _↝ˢ_ : Car → (Car → Set ℓB) → Set (ℓ ⊔ˡ ℓ✓ ⊔ˡ ℓB)
  a ↝ˢ B  =  ∀ c →  ✓ (c ∙ a)  →  Σ b ,  b ∈ B  ×  ✓ (c ∙ b)

  abstract

    -- ↝ into ↝ˢ
    ↝⇒↝ˢ : a ↝ b  →  a ↝ˢ (b ≡_)
    ↝⇒↝ˢ {b = b} a↝b c ✓c∙a = b , refl⁼ , a↝b c ✓c∙a

    -- ↝ respects ≈

    ↝-resp :  a ≈ a'  →  b ≈ b'  →  a ↝ b  →  a' ↝ b'
    ↝-resp a≈a' b≈b' a↝b c ✓c∙a' = ✓c∙a' ▷
      ✓-resp (∙-congʳ $ sym˜ a≈a') ▷ a↝b c ▷ ✓-resp (∙-congʳ b≈b')

    ↝-respˡ :  a ≈ a'  →  a ↝ b  →  a' ↝ b
    ↝-respˡ a≈a' = ↝-resp a≈a' refl˜

    ↝-respʳ :  b ≈ b'  →  a ↝ b  →  a ↝ b'
    ↝-respʳ b≈b' = ↝-resp refl˜ b≈b'

    -- ↝ˢ respects ≈ and ⊆≈

    ↝ˢ-resp :  a ≈ a'  →  B ⊆≈ B'  →  a ↝ˢ B  →  a' ↝ˢ B'
    ↝ˢ-resp a≈a' B⊆≈B' a↝ˢB c ✓c∙a'
      with  ✓c∙a' ▷ ✓-resp (∙-congʳ $ sym˜ a≈a') ▷ a↝ˢB c
    ... | b , b∈B , ✓c∙b  with  B⊆≈B' b∈B
    ...   | b' , b≈b' , b'∈B'  =  b' , b'∈B' , ✓-resp (∙-congʳ b≈b') ✓c∙b

    ↝ˢ-respˡ :  a ≈ a'  →  a ↝ˢ B  →  a' ↝ˢ B
    ↝ˢ-respˡ a≈a'  =  ↝ˢ-resp a≈a' ⊆≈-refl

    ↝ˢ-respʳ : B ⊆≈ B'  →  a ↝ˢ B  →  a ↝ˢ B'
    ↝ˢ-respʳ  =  ↝ˢ-resp refl˜

    -- ↝ is reflexive and transitive

    ↝-refl : a ↝ a
    ↝-refl _  =  id

    ↝-trans :  a ↝ b  →  b ↝ c  →  a ↝ c
    ↝-trans a↝b b↝c d ✓d∙a  =  ✓d∙a ▷ a↝b d ▷ b↝c d

    -- ↝ and ↝ˢ can be composed

    ↝-↝ˢ :  a ↝ b  →  b ↝ˢ C  →  a ↝ˢ C
    ↝-↝ˢ a↝b b↝ˢC d ✓d∙a  =  ✓d∙a ▷ a↝b d ▷ b↝ˢC d

    -- ↝/↝ˢ can be merged with respect to ∙

    ∙-mono-↝ :  a ↝ b  →  c ↝ d  →  a ∙ c  ↝  b ∙ d
    ∙-mono-↝ a↝b c↝d e ✓e∙a∙c  =  ✓e∙a∙c ▷ ✓-resp ∙-assocʳ ▷
      c↝d _ ▷ ✓-resp (∙-assocˡ »˜ ∙-congʳ ∙-comm »˜ ∙-assocʳ) ▷
      a↝b _ ▷ ✓-resp (∙-assocˡ »˜ ∙-congʳ ∙-comm)

    ∙-mono-↝ˢ :  a ↝ˢ B  →  c ↝ˢ D  →
      (∀ {b d} →  b ∈ B  →  d ∈ D  →  Σ e ,  e ≈ b ∙ d  ×  e ∈ E)  →  a ∙ c ↝ˢ E
    ∙-mono-↝ˢ a↝ˢB c↝ˢD BDE f ✓f∙a∙c  with ✓f∙a∙c ▷ ✓-resp ∙-assocʳ ▷ c↝ˢD _
    ... | d , d∈D , ✓f∙a∙d  with  ✓f∙a∙d ▷
      ✓-resp (∙-assocˡ »˜ ∙-congʳ ∙-comm »˜ ∙-assocʳ) ▷ a↝ˢB _
    ...   | b , b∈B , ✓f∙d∙b  with  BDE b∈B d∈D
    ...     | e , e≈b∙d , e∈E  =  e , e∈E ,
      ✓-resp (∙-assocˡ »˜ ∙-congʳ $ ∙-comm »˜ sym˜ e≈b∙d) ✓f∙d∙b
