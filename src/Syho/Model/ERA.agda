--------------------------------------------------------------------------------
-- Environmental Resource Algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Syho.Model.ERA where

open import Base.Level using (Level; _⊔ᴸ_; sucᴸ)
open import Base.Eq using (_≡_; refl)
open import Base.Func using (_$_; id; _▷_; flip; _∈_)
open import Base.Prod using (_×_; _,_; ∑-syntax)
open import Base.Setoid using (Setoid)

--------------------------------------------------------------------------------
-- Environmental Resource algebra

record  ERA ℓ ℓᴱ ℓ≈ ℓ✓ : Set (sucᴸ (ℓ ⊔ᴸ ℓᴱ ⊔ᴸ ℓ≈ ⊔ᴸ ℓ✓))  where
  ------------------------------------------------------------------------------
  -- Fields
  infix 4 _≈_
  infix 3 _✓_
  infixr 7 _∙_
  infix 0 ◠˜_
  infixr -1 _◇˜_
  field
    -- Carrier set
    Car :  Set ℓ
    -- Environment
    Env :  Set ℓᴱ
    ----------------------------------------------------------------------------
    -- Equivalence
    _≈_ :  Car → Car → Set ℓ≈
    -- Validity
    _✓_ :  Env → Car → Set ℓ✓
    -- Product
    _∙_ :  Car → Car → Car
    -- Unit
    ε :  Car
    -- Core
    ⌞_⌟ :  Car → Car
    ----------------------------------------------------------------------------
    -- ≈ is reflexive, symmetric and transitive
    refl˜ :  ∀ {a} →  a ≈ a
    ◠˜_ :  ∀ {a b} →  a ≈ b →  b ≈ a
    _◇˜_ :  ∀ {a b c} →  a ≈ b →  b ≈ c →  a ≈ c
    ----------------------------------------------------------------------------
    -- ∙ is congruent, unital with ε, commutative, and associative
    ∙-congˡ :  ∀ {a b c} →  a ≈ b →  a ∙ c ≈ b ∙ c
    ∙-unitˡ :  ∀ {a} →  ε ∙ a ≈ a
    ∙-comm :  ∀ {a b} →  a ∙ b ≈ b ∙ a
    ∙-assocˡ :  ∀ {a b c} →  (a ∙ b) ∙ c ≈ a ∙ (b ∙ c)
    ----------------------------------------------------------------------------
    -- ✓ respects ≈
    ✓-resp :  ∀ {E a b} →  a ≈ b →  E ✓ a →  E ✓ b
    -- ✓ is kept after a resource is removed
    ✓-rem :  ∀ {E a b} →  E ✓ a ∙ b →  E ✓ b
    -- ε satisfies ✓
    ✓-ε :  ∀{E} →  E ✓ ε
    ----------------------------------------------------------------------------
    -- ⌞⌟ preserves ≈
    ⌞⌟-cong :  ∀ {a b} →  a ≈ b →  ⌞ a ⌟ ≈ ⌞ b ⌟
    -- When ⌞⌟'s argument gets added, ⌞⌟'s result gets added
    ⌞⌟-add :  ∀ {a b} →  ∑ b' ,  b' ∙ ⌞ a ⌟ ≈ ⌞ b ∙ a ⌟
    -- ⌞ a ⌟ is absorbed by a
    ⌞⌟-unitˡ :  ∀ {a} →  ⌞ a ⌟ ∙ a  ≈  a
    -- ⌞⌟ is idempotent
    ⌞⌟-idem :  ∀ {a} →  ⌞ ⌞ a ⌟ ⌟ ≈ ⌞ a ⌟

  -- Setoid structure
  setoid :  Setoid ℓ ℓ≈
  setoid =  record{ Car = Car; _≈_ = _≈_; refl˜ = refl˜; ◠˜_ = ◠˜_;
    _◇˜_ = _◇˜_ }
  open Setoid setoid public hiding (Car; _≈_; refl˜; ◠˜_; _◇˜_)

  private variable
    a a' b b' c d :  Car
    E :  Env
    ℓX ℓY :  Level
    X :  Set ℓX
    b˙ b'˙ :  X → Car

  ------------------------------------------------------------------------------
  -- Utility lemmas
  abstract

    -- Congruence, unitality and associativity

    ∙-congʳ :  a ≈ b →  c ∙ a ≈ c ∙ b
    ∙-congʳ a≈b =  ∙-comm ◇˜ ∙-congˡ a≈b ◇˜ ∙-comm

    ∙-cong :  a ≈ b →  c ≈ d →  a ∙ c ≈ b ∙ d
    ∙-cong a≈b c≈d =  ∙-congˡ a≈b ◇˜ ∙-congʳ c≈d

    ∙-unitʳ :  a ∙ ε ≈ a
    ∙-unitʳ =  ∙-comm ◇˜ ∙-unitˡ

    ∙-assocʳ :  a ∙ (b ∙ c) ≈ (a ∙ b) ∙ c
    ∙-assocʳ =  ◠˜ ∙-assocˡ

    -- Variant of ⌞⌟-unitˡ

    ⌞⌟-unitʳ :  a ∙ ⌞ a ⌟ ≈ a
    ⌞⌟-unitʳ =  ∙-comm ◇˜ ⌞⌟-unitˡ

    -- ⌞ ⌟ can be duplicated

    ⌞⌟-dup :  ⌞ a ⌟ ∙ ⌞ a ⌟ ≈ ⌞ a ⌟
    ⌞⌟-dup =  ∙-congˡ (◠˜ ⌞⌟-idem) ◇˜ ⌞⌟-unitˡ

    -- ⌞ ε ⌟ is ε

    ⌞⌟-ε :  ⌞ ε ⌟ ≈ ε
    ⌞⌟-ε =  ◠˜ ∙-unitʳ ◇˜ ⌞⌟-unitˡ

  ------------------------------------------------------------------------------
  -- ⊑ :  Derived pre-order

  infix 4 _⊑_
  _⊑_ :  Car → Car → Set (ℓ ⊔ᴸ ℓ≈)
  a ⊑ b =  ∑ c ,  c ∙ a  ≈  b

  abstract

    -- ⊑ is reflexive

    ≈⇒⊑ :  a ≈ b →  a ⊑ b
    ≈⇒⊑ a≈b =  ε , ∙-unitˡ ◇˜ a≈b

    ⊑-refl :  a ⊑ a
    ⊑-refl =  ≈⇒⊑ refl˜

    -- ⊑ is transitive

    ⊑-trans :  a ⊑ b →  b ⊑ c →  a ⊑ c
    ⊑-trans (d , d∙a≈b) (e , e∙b≈c) =  d ∙ e ,
      ∙-congˡ ∙-comm ◇˜ ∙-assocˡ ◇˜ ∙-congʳ d∙a≈b ◇˜ e∙b≈c

    -- ⊑ respects ≈

    ⊑-resp :  a ≈ b →  c ≈ d →  a ⊑ c →  b ⊑ d
    ⊑-resp a≈b c≈d (e , e∙a≈c) =  e , ∙-congʳ (◠˜ a≈b) ◇˜ e∙a≈c ◇˜ c≈d

    ⊑-respˡ :  a ≈ b →  a ⊑ c →  b ⊑ c
    ⊑-respˡ a≈b a⊑c =  ⊑-resp a≈b refl˜ a⊑c

    ⊑-respʳ :  ∀ {a b c} →  b ≈ c →  a ⊑ b →  a ⊑ c
    ⊑-respʳ b≈c a⊑b =  ⊑-resp refl˜ b≈c a⊑b

    -- ε is the minimum

    ε-min :  ε ⊑ a
    ε-min =  _ , ∙-unitʳ

    -- ∙ is increasing

    ∙-incrˡ :  a  ⊑  b ∙ a
    ∙-incrˡ =  _ , refl˜

    ∙-incrʳ :  a  ⊑  a ∙ b
    ∙-incrʳ =  ⊑-respʳ ∙-comm ∙-incrˡ

    -- Monotonicity of ✓, ∙ and ⌞⌟

    ✓-mono :  a ⊑ b →  E ✓ b →  E ✓ a
    ✓-mono (c , c∙a≈b) E✓b =  E✓b ▷ ✓-resp (◠˜ c∙a≈b) ▷ ✓-rem

    ∙-monoˡ :  a ⊑ b →  a ∙ c  ⊑  b ∙ c
    ∙-monoˡ (d , d∙a≈b) =  d , ∙-assocʳ ◇˜ ∙-congˡ d∙a≈b

    ∙-monoʳ :  a ⊑ b →  c ∙ a  ⊑  c ∙ b
    ∙-monoʳ a⊑b =  ⊑-resp ∙-comm ∙-comm $ ∙-monoˡ a⊑b

    ∙-mono :  a ⊑ b →  c ⊑ d →  a ∙ c  ⊑  b ∙ d
    ∙-mono a⊑b c⊑d =  ⊑-trans (∙-monoˡ a⊑b) (∙-monoʳ c⊑d)

    ⌞⌟-mono :  a ⊑ b →  ⌞ a ⌟ ⊑ ⌞ b ⌟
    ⌞⌟-mono (c , c∙a≈b)  with ⌞⌟-add {_} {c}
    ... | c' , c'∙⌞a⌟≈⌞c∙a⌟ =  c' , c'∙⌞a⌟≈⌞c∙a⌟ ◇˜ ⌞⌟-cong c∙a≈b

    -- ⌞ ⌟ is decreasing

    ⌞⌟-decr :  ⌞ a ⌟ ⊑ a
    ⌞⌟-decr =  ⊑-respʳ ⌞⌟-unitˡ ∙-incrʳ

    -- ⌞ ⌟ and ∙ commute weakly

    ⌞⌟-∙ :  ⌞ a ⌟ ∙ ⌞ b ⌟ ⊑ ⌞ a ∙ b ⌟
    ⌞⌟-∙ =  ⊑-respʳ ⌞⌟-dup $ ∙-mono (⌞⌟-mono ∙-incrʳ) (⌞⌟-mono ∙-incrˡ)

    -- E ✓ a implies E ✓ ⌞ a ⌟

    ✓-⌞⌟ :  E ✓ a →  E ✓ ⌞ a ⌟
    ✓-⌞⌟ ✓a =  ✓-mono ⌞⌟-decr ✓a

  ------------------------------------------------------------------------------
  -- ↝/↝˙ : Resource update

  infix 2 _↝_ _↝˙_

  -- a ↝ b : a can be updated into b,
  -- regardless of the environment E and the frame c
  _↝_ :  Car → Car → Set (ℓ ⊔ᴸ ℓᴱ ⊔ᴸ ℓ✓)
  a ↝ b =  ∀ E c →  E ✓ c ∙ a →  E ✓ c ∙ b

  -- a ↝˙ b˙ : a can be updated into b˙ x for some x,
  -- regardless of the environment E and the frame c
  _↝˙_ :  {X : Set ℓX} →  Car →  (X → Car) →  Set (ℓ ⊔ᴸ ℓᴱ ⊔ᴸ ℓ✓ ⊔ᴸ ℓX)
  a ↝˙ b˙ =  ∀ E c →  E ✓ c ∙ a →  ∑ x ,  E ✓ c ∙ b˙ x

  abstract

    -- ↝ respects ≈

    ↝-resp :  a ≈ a' →  b ≈ b' →  a ↝ b →  a' ↝ b'
    ↝-resp a≈a' b≈b' a↝b E c E✓c∙a' =  E✓c∙a' ▷
      ✓-resp (∙-congʳ $ ◠˜ a≈a') ▷ a↝b E c ▷ ✓-resp (∙-congʳ b≈b')

    ↝-respˡ :  a ≈ a' →  a ↝ b →  a' ↝ b
    ↝-respˡ a≈a' =  ↝-resp a≈a' refl˜

    ↝-respʳ :  b ≈ b' →  a ↝ b →  a ↝ b'
    ↝-respʳ b≈b' =  ↝-resp refl˜ b≈b'

    -- ↝˙ respects ≈

    ↝˙-resp :  a ≈ a' →  (∀ x → b˙ x ≈ b'˙ x) →  a ↝˙ b˙ →  a' ↝˙ b'˙
    ↝˙-resp a≈a' b˙≈b'˙ a↝b˙ E c E✓c∙a'
      with  E✓c∙a' ▷ ✓-resp (∙-congʳ $ ◠˜ a≈a') ▷ a↝b˙ E c
    ... | x , E✓c∙b˙x  =  x , ✓-resp (∙-congʳ $ b˙≈b'˙ x) E✓c∙b˙x

    ↝˙-respˡ :  a ≈ a' →  a ↝˙ b˙ →  a' ↝˙ b˙
    ↝˙-respˡ a≈a' =  ↝˙-resp a≈a' (λ _ → refl˜)

    ↝˙-respʳ :  (∀ x → b˙ x ≈ b'˙ x) →  a ↝˙ b˙ →  a ↝˙ b'˙
    ↝˙-respʳ =  ↝˙-resp refl˜

    -- Reflexivity

    ↝-refl :  a ↝ a
    ↝-refl _ _ =  id
