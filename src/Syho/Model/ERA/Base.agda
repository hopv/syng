--------------------------------------------------------------------------------
-- Environmental resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Syho.Model.ERA.Base where

open import Base.Level using (Level; _⊔ᴸ_; ṡᴸ_)
open import Base.Func using (_$_; id; _▷_; flip; _∘_)
open import Base.Few using (⊤₀)
open import Base.Eq using (_≡_; refl)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_; curry)
open import Base.Nat using (ℕ)
open import Base.List using (List; []; _∷_; _$ᴸ_; _$ⁱᴸ_; _$ⁱᴸ⟨_⟩_)

--------------------------------------------------------------------------------
-- ERA :  Environmental resource algebra

-- The ERA is similar to the (unital) resource algebra (RA) used in Iris, but
-- the ERA has the notion of environment Env, and the ERA's validity predicate ✓
-- inputs not only the resource but also the environment.
-- You can view an environment of an ERA as analogous to an authoritative state
-- ● a of the Auth RA in Iris.
-- The environment simplifies the proof of various properties (especially
-- resource updates ↝), thanks to the fact that we always stably have a single
-- environment separately from resources.

record  ERA łᴿ ł≈ łᴱ ł✓ : Set (ṡᴸ (łᴿ ⊔ᴸ ł≈ ⊔ᴸ łᴱ ⊔ᴸ ł✓))  where
  ------------------------------------------------------------------------------
  -- Fields
  infix 4 _≈_
  infixr 7 _∙_
  infix 4 _✓_
  infix 0 ◠˜_
  infixr -1 _◇˜_
  field
    ----------------------------------------------------------------------------
    -- Main components

    -- Res :  Resource
    Res :  Set łᴿ

    -- ≈ :  Equivalence on resources
    _≈_ :  Res →  Res →  Set ł≈

    -- ∙ :  Product of resources, used for modeling the separating conjunction ∗
    _∙_ :  Res →  Res →  Res

    -- ε :  Unit resource
    ε :  Res

    -- ⌞ ⌟ :  Core of a resource, used for modeling the persistence modality □
    ⌞_⌟ :  Res →  Res

    -- Env :  Environment
    Env :  Set łᴱ

    -- ✓ :  Validity of a pair of an environment and a resource
    _✓_ :  Env →  Res →  Set ł✓

    ----------------------------------------------------------------------------
    -- On ≈

    -- ≈ is reflexive, symmetric and transitive

    refl˜ :  ∀{a} →  a ≈ a
    ◠˜_ :  ∀{a b} →  a ≈ b →  b ≈ a
    _◇˜_ :  ∀{a b c} →  a ≈ b →  b ≈ c →  a ≈ c

    ----------------------------------------------------------------------------
    -- On ∙

    -- ∙ preserves ≈, and is unital with the unit ε, commutative and associative
    -- w.r.t. ≈

    ∙-congˡ :  ∀{a b c} →  a ≈ b →  a ∙ c ≈ b ∙ c
    ∙-unitˡ :  ∀{a} →  ε ∙ a ≈ a
    ∙-comm :  ∀{a b} →  a ∙ b ≈ b ∙ a
    ∙-assocˡ :  ∀{a b c} →  (a ∙ b) ∙ c ≈ a ∙ (b ∙ c)

    ----------------------------------------------------------------------------
    -- On ⌞⌟

    -- ⌞⌟ preserves ≈

    ⌞⌟-cong :  ∀{a b} →  a ≈ b →  ⌞ a ⌟ ≈ ⌞ b ⌟

    -- When ⌞⌟'s argument gets added, ⌞⌟'s result gets added

    ⌞⌟-add :  ∀{a b} →  ∑ a' ,  ⌞ a ∙ b ⌟  ≈ a' ∙ ⌞ b ⌟

    -- ⌞ a ⌟ is absorbed by a

    ⌞⌟-unitˡ :  ∀{a} →  ⌞ a ⌟ ∙ a  ≈  a

    -- ⌞⌟ is idempotent

    ⌞⌟-idem :  ∀{a} →  ⌞ ⌞ a ⌟ ⌟ ≈ ⌞ a ⌟

    ----------------------------------------------------------------------------
    -- On ✓

    -- ✓ respects ≈

    ✓-resp :  ∀{E a b} →  a ≈ b →  E ✓ a →  E ✓ b

    -- ✓ is kept after a resource is removed

    ✓-rem :  ∀{E a b} →  E ✓ a ∙ b →  E ✓ b

  private variable
    a a' b b' c d :  Res
    E E' F F' :  Env
    Ea E'a' Fb F'b' Gc :  Env × Res
    ł :  Level
    X Y :  Set ł
    Fb˙ F'b'˙ :  X →  Env × Res
    f :  Y → X

  abstract
    ----------------------------------------------------------------------------
    -- On ≈

    -->  ◠˜_ :  a ≈ b →  b ≈ a
    -->  _◇˜_ :  a ≈ b →  b ≈ c →  a ≈ c

    -- ≈ is reflexive

    -->  refl˜ :  a ≈ a

    ≡⇒≈ :  a ≡ b →  a ≈ b
    ≡⇒≈ refl =  refl˜

    ----------------------------------------------------------------------------
    -- On ∙

    -->  ∙-comm :  a ∙ b ≈ b ∙ a

    -- ∙ preserves ≈

    -->  ∙-congˡ :  a ≈ b →  a ∙ c ≈ b ∙ c

    ∙-congʳ :  a ≈ b →  c ∙ a ≈ c ∙ b
    ∙-congʳ a≈b =  ∙-comm ◇˜ ∙-congˡ a≈b ◇˜ ∙-comm

    ∙-cong :  a ≈ b →  c ≈ d →  a ∙ c ≈ b ∙ d
    ∙-cong a≈b c≈d =  ∙-congˡ a≈b ◇˜ ∙-congʳ c≈d

    -- ∙ is unital

    -->  ∙-unitˡ :  ε ∙ a ≈ a

    ∙-unitʳ :  a ∙ ε ≈ a
    ∙-unitʳ =  ∙-comm ◇˜ ∙-unitˡ

    -- ∙ is associative

    -->  ∙-assocˡ :  (a ∙ b) ∙ c ≈ a ∙ (b ∙ c)

    ∙-assocʳ :  a ∙ (b ∙ c) ≈ (a ∙ b) ∙ c
    ∙-assocʳ =  ◠˜ ∙-assocˡ

    ----------------------------------------------------------------------------
    -- On ✓

    -->  ✓-rem :  E ✓ a ∙ b →  E ✓ b

    ----------------------------------------------------------------------------
    -- On ⌞⌟

    -->  ⌞⌟-cong :  a ≈ b →  ⌞ a ⌟ ≈ ⌞ b ⌟

    -->  ⌞⌟-add :  ∑ a' ,  ⌞ a ∙ b ⌟  ≈ a' ∙ ⌞ b ⌟

    -->  ⌞⌟-idem :  ⌞ ⌞ a ⌟ ⌟ ≈ ⌞ a ⌟

    -- ⌞ a ⌟ is absorbed by a

    -->  ⌞⌟-unitˡ :  ⌞ a ⌟ ∙ a  ≈  a

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

  abstract

    infix 4 _⊑_
    _⊑_ :  Res → Res → Set (łᴿ ⊔ᴸ ł≈)
    a ⊑ b =  ∑ c ,  c ∙ a  ≈  b

    -- Unfold ⊑

    ⊑≡ :  _⊑_  ≡  λ a b → ∑ c , c ∙ a ≈ b
    ⊑≡ =  refl

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

    ⊑-respʳ :  a ≈ b →  c ⊑ a →  c ⊑ b
    ⊑-respʳ b≈c a⊑b =  ⊑-resp refl˜ b≈c a⊑b

    -- ε is the minimum

    ε-min :  ε ⊑ a
    ε-min =  -, ∙-unitʳ

    -- ∙ is increasing

    ∙-incrˡ :  a  ⊑  b ∙ a
    ∙-incrˡ =  -, refl˜

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
    ⌞⌟-mono (c , c∙a≈b)  with ⌞⌟-add {c}
    … | c' , ⌞c∙a⌟≈'∙⌞a⌟ =  c' , ◠˜ ⌞c∙a⌟≈'∙⌞a⌟ ◇˜ ⌞⌟-cong c∙a≈b

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
  -- [∙] :  Iterated resource product

  [∙] :  List Res →  Res
  [∙] [] =  ε
  [∙] (a ∷ as) =  a ∙ [∙] as

  -- Syntax for [∙] $ᴸ / $ⁱᴸ

  infix 8 [∙∈]-syntax [∙∈ⁱ]-syntax [∙∈ⁱ⟨⟩]-syntax
  [∙∈] [∙∈]-syntax :  (X → Res) →  List X →  Res
  [∙∈] a˙ xs =  [∙] $ a˙ $ᴸ xs
  [∙∈]-syntax =  [∙∈]
  [∙∈ⁱ] [∙∈ⁱ]-syntax :  (ℕ × X → Res) →  List X →  Res
  [∙∈ⁱ] a˙ xs =  [∙] $ curry a˙ $ⁱᴸ xs
  [∙∈ⁱ]-syntax =  [∙∈ⁱ]
  [∙∈ⁱ⟨⟩] [∙∈ⁱ⟨⟩]-syntax :  (ℕ × X → Res) →  ℕ →  List X →  Res
  [∙∈ⁱ⟨⟩] a˙ k xs =  [∙] $ curry a˙ $ⁱᴸ⟨ k ⟩ xs
  [∙∈ⁱ⟨⟩]-syntax =  [∙∈ⁱ⟨⟩]
  syntax [∙∈]-syntax (λ x → a) xs =  [∙ x ∈ xs ] a
  syntax [∙∈ⁱ]-syntax (λ ix → a) xs =  [∙ ix ∈ⁱ xs ] a
  syntax [∙∈ⁱ⟨⟩]-syntax (λ ix → a) k xs =  [∙ ix ∈ⁱ⟨ k ⟩ xs ] a

  ------------------------------------------------------------------------------
  -- ↝ :  Environmental resource update

  infix 2 _↝_

  -- (E , a) ↝ Fb˙ :  The environment-resource pair (E , a) can be updated into
  --                  Fb˙ x for some x, regardless the frame resource c

  _↝_ :  ∀{X : Set ł} →  Env × Res →  (X →  Env × Res) →  Set (łᴿ ⊔ᴸ ł✓ ⊔ᴸ ł)
  (E , a) ↝ Fb˙ =  ∀ c →  E ✓ a ∙ c →  ∑ x ,  let (F , b) = Fb˙ x in  F ✓ b ∙ c
