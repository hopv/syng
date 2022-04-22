----------------------------------------------------------------------
-- Resource Algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Shog.Model.RA where

open import Level using (Level; _⊔_; suc)

open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel; _⇒_; Reflexive; Transitive;
  _Respects_; _Respectsʳ_; _Respectsˡ_; _Respects₂_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to refl')
open import Algebra using (Op₁; Op₂; Congruent₁;
  IsCommutativeMonoid; CommutativeMonoid)

open import Function.Base using (_$_; id; _|>_)
open import Data.Product using (_×_; _,_; ∃-syntax)

----------------------------------------------------------------------
-- Resource algebra (Unital)
record RA ℓ ℓ≈ ℓ✓ : Set (suc (ℓ ⊔ ℓ≈ ⊔ ℓ✓)) where
  --------------------------------------------------------------------
  -- Fields
  infix 4 _≈_
  infixl 7 _∙_
  field
    -- Carrier
    Carrier : Set ℓ
    ------------------------------------------------------------------
    -- Equivalence
    _≈_ : Rel Carrier ℓ≈
    -- Validity
    ✓ : Pred Carrier ℓ✓
    -- Product
    _∙_ : Op₂ Carrier
    -- Unit
    ε : Carrier
    -- Core
    ⌞_⌟ : Op₁ Carrier
    ------------------------------------------------------------------
    -- ≈, ∙, ε forms a commutative monoid
    isCommutativeMonoid : IsCommutativeMonoid _≈_ _∙_ ε
    ------------------------------------------------------------------
    -- ✓ respects ≈
    ✓-resp : ✓ Respects _≈_
    -- ✓ is kept after a resource is removed
    ✓-rem : ∀ a b → ✓ (b ∙ a) → ✓ a
    ------------------------------------------------------------------
    -- ⌞⌟ preserves ≈
    ⌞⌟-cong : Congruent₁ _≈_ ⌞_⌟
    -- When ⌞⌟'s argument gets added, ⌞⌟'s result gets added
    ⌞⌟-add : ∀ a b → ∃[ b' ] b' ∙ ⌞ a ⌟ ≈ ⌞ b ∙ a ⌟
    -- ⌞ a ⌟ is absorbed by a
    ⌞⌟-unitˡ : ∀ a → ⌞ a ⌟ ∙ a ≈ a
    -- ⌞⌟ is idempotent
    ⌞⌟-idem : ∀ a → ⌞ ⌞ a ⌟ ⌟ ≈ ⌞ a ⌟

  --------------------------------------------------------------------
  -- Commutative monoid structure
  commutativeMonoid : CommutativeMonoid _ _
  commutativeMonoid = record { isCommutativeMonoid = isCommutativeMonoid }
  open CommutativeMonoid commutativeMonoid public
    hiding (Carrier; _≈_; _∙_; ε; isCommutativeMonoid)

  -- Infix notation for trans
  infixr -1 _»_ -- the same as _$_
  _»_ = trans

  --------------------------------------------------------------------
  -- Derived notions

  private variable
    a a' b b' c d : Carrier
    ℓA ℓB ℓB' ℓC ℓD ℓE : Level
    A : Carrier → Set ℓA
    B : Carrier → Set ℓB
    B' : Carrier → Set ℓB'
    C : Carrier → Set ℓC
    D : Carrier → Set ℓD
    E : Carrier → Set ℓE

  ----------------------------------------------------------------------
  -- Variant of ⌞⌟-unitˡ

  ⌞⌟-unitʳ : ∀ a → a ∙ ⌞ a ⌟ ≈ a
  ⌞⌟-unitʳ _ = comm _ _ » ⌞⌟-unitˡ _

  ----------------------------------------------------------------------
  -- ≤: Derived pre-order

  infix 4 _≤_
  _≤_ : Carrier → Carrier → Set (ℓ ⊔ ℓ≈)
  a ≤ b = ∃[ c ] c ∙ a ≈ b

  ----------------------------------------------------------------------
  -- ≤ is reflexive

  ≈⇒≤ : _≈_ ⇒ _≤_
  ≈⇒≤ a≈b = ε , (identityˡ _ » a≈b)

  ≤-refl : a ≤ a
  ≤-refl = ≈⇒≤ refl

  -- ≤ is transitive

  ≤-trans : Transitive _≤_
  ≤-trans (d , d∙a≈b) (e , e∙b≈c) = (d ∙ e) ,
    (∙-congʳ (comm _ _) » assoc _ _ _ » ∙-congˡ d∙a≈b » e∙b≈c)

  infixr -1 _ᵒ»ᵒ_ _»ᵒ_ _ᵒ»_ -- the same fixity with _$_

  _ᵒ»ᵒ_ : Transitive _≤_
  _ᵒ»ᵒ_ = ≤-trans

  _»ᵒ_ : a ≈ b → b ≤ c → a ≤ c
  a≈b »ᵒ b≤c = ≈⇒≤ a≈b ᵒ»ᵒ b≤c

  _ᵒ»_ : a ≤ b → b ≈ c → a ≤ c
  a≤b ᵒ» b≈c = a≤b ᵒ»ᵒ ≈⇒≤ b≈c

  ----------------------------------------------------------------------
  -- ∙ is increasing

  ∙-incr : ∀ a b → a ≤ b ∙ a
  ∙-incr _ b = b , refl

  ----------------------------------------------------------------------
  -- Monotonicity of ✓, ∙ and ⌞⌟

  ✓-mono : a ≤ b → ✓ b → ✓ a
  ✓-mono (c , c∙a≈b) ✓b = ✓-rem _ _ $ ✓-resp (sym c∙a≈b) ✓b

  ∙-monoˡ : ∀ c → a ≤ b → a ∙ c ≤ b ∙ c
  ∙-monoˡ _ (d , d∙a≈b) = d , (sym (assoc _ _ _) » ∙-congʳ d∙a≈b)

  ∙-monoʳ : ∀ c → a ≤ b → c ∙ a ≤ c ∙ b
  ∙-monoʳ _ a≤b = comm _ _ »ᵒ ∙-monoˡ _ a≤b ᵒ» comm _ _

  ∙-mono : a ≤ b → c ≤ d → a ∙ c ≤ b ∙ d
  ∙-mono a≤b c≤d = ∙-monoˡ _ a≤b ᵒ»ᵒ ∙-monoʳ _ c≤d

  ⌞⌟-mono : a ≤ b → ⌞ a ⌟ ≤ ⌞ b ⌟
  ⌞⌟-mono (c , c∙a≈b) with ⌞⌟-add _ c
  ... | c' , c'∙⌞a⌟≈⌞c∙a⌟ = c' , (c'∙⌞a⌟≈⌞c∙a⌟ » ⌞⌟-cong c∙a≈b)

  ----------------------------------------------------------------------
  -- ~>/~>ˢ : Resource update

  infix 2 _~>_ _~>ˢ_

  -- a ~> b : a can be updated into b, regardless of the frame c
  _~>_ : Carrier → Carrier → Set (ℓ ⊔ ℓ✓)
  a ~> b = ∀ c → ✓ (c ∙ a) → ✓ (c ∙ b)

  -- a ~>ˢ B : a can be updated into b, regardless of the frame c
  _~>ˢ_ : Carrier → (Carrier → Set ℓB) → Set (ℓ ⊔ ℓ✓ ⊔ ℓB)
  a ~>ˢ B = ∀ c → ✓ (c ∙ a) → ∃[ b ] B b × ✓ (c ∙ b)

  ----------------------------------------------------------------------
  -- ~> into ~>ˢ
  ~>⇒~>ˢ : a ~> b → a ~>ˢ (b ≡_)
  ~>⇒~>ˢ {b = b} a~>b c ✓c∙a = b , refl' , a~>b c ✓c∙a

  ----------------------------------------------------------------------
  -- ~> respects ≈

  ~>-respʳ : _~>_ Respectsʳ _≈_
  ~>-respʳ b≈b' a~>b c ✓c∙a = ✓c∙a |> a~>b c |> ✓-resp (∙-congˡ b≈b')

  ~>-respˡ : _~>_ Respectsˡ _≈_
  ~>-respˡ a≈a' a~>b c ✓c∙a' = ✓c∙a' |> ✓-resp (∙-congˡ $ sym a≈a') |> a~>b c

  ~>-resp : _~>_ Respects₂ _≈_
  ~>-resp = ~>-respʳ , ~>-respˡ

  -- ~>ˢ respects ≈ and ⊆≈
  -- We don't use Respects₂ to achieve better level polymorphism

  open import Shog.Base.Setoid setoid using (_⊆≈_; ⊆≈-refl)

  ~>ˢ-resp : a ≈ a' → B ⊆≈ B' → a ~>ˢ B → a' ~>ˢ B'
  ~>ˢ-resp a≈a' B⊆≈B' a~>ˢB c ✓c∙a'
    with ✓c∙a' |> ✓-resp (∙-congˡ $ sym a≈a') |> a~>ˢB c
  ... | b , b∈B , ✓c∙b with B⊆≈B' b∈B
  ...   | b' , b≈b' , b'∈B' = b' , b'∈B' , ✓-resp (∙-congˡ b≈b') ✓c∙b

  ~>ˢ-respˡ : (_~>ˢ B) Respects _≈_
  ~>ˢ-respˡ a≈a' = ~>ˢ-resp a≈a' ⊆≈-refl

  ~>ˢ-respʳ : B ⊆≈ B' → a ~>ˢ B → a ~>ˢ B'
  ~>ˢ-respʳ = ~>ˢ-resp refl

  ----------------------------------------------------------------------
  -- ~> is reflexive

  ~>-refl : Reflexive _~>_
  ~>-refl _ = id

  -- ~> is transitive

  ~>-trans : Transitive _~>_
  ~>-trans a~>b b~>c d ✓d∙a = ✓d∙a |> a~>b d |> b~>c d

  -- ~> and ~>ˢ can be composed

  ~>-~>ˢ : a ~> b → b ~>ˢ C → a ~>ˢ C
  ~>-~>ˢ a~>b b~>ˢC d ✓d∙a = ✓d∙a |> a~>b d |> b~>ˢC d

  ----------------------------------------------------------------------
  -- ~>/~>ˢ can be merged with respect to ∙

  ∙-mono-~> : _∙_ Preserves₂ _~>_ ⟶ _~>_ ⟶ _~>_
  ∙-mono-~> a~>b c~>d e ✓e∙a∙c = ✓e∙a∙c |> ✓-resp (sym (assoc _ _ _)) |>
    c~>d _ |> ✓-resp (assoc _ _ _ » ∙-congˡ (comm _ _) » sym (assoc _ _ _)) |>
    a~>b _ |> ✓-resp (assoc e _ _ » ∙-congˡ (comm _ _))

  ∙-mono-~>ˢ : a ~>ˢ B → c ~>ˢ D →
    (∀ {b d} → b ∈ B → d ∈ D → ∃[ e ] e ≈ b ∙ d × e ∈ E) → a ∙ c ~>ˢ E
  ∙-mono-~>ˢ a~>ˢB c~>ˢD BDE f ✓f∙a∙c with
    ✓f∙a∙c |> ✓-resp (sym (assoc _ _ _)) |> c~>ˢD _
  ... | d , d∈D , ✓f∙a∙d with ✓f∙a∙d |>
    ✓-resp (assoc _ _ _ » ∙-congˡ (comm _ _) » sym (assoc _ _ _)) |> a~>ˢB _
  ...   | b , b∈B , ✓f∙d∙b with BDE b∈B d∈D
  ...     | e , e≈b∙d , e∈E  =  e , e∈E ,
    ✓-resp (assoc _ _ _ » ∙-congˡ $ comm _ _ » sym e≈b∙d) ✓f∙d∙b
