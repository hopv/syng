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

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function.Base using (_$_)

private variable
  a a' b b' c d : Car

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
... | (d' , ⌞c∙a⌟d' , e' , e'∙a'≈d') with ⌞⌟-cong c∙a≈b ⌞c∙a⌟d'
...   | (b' , ⌞b⌟b' , d'≈b') = b' , ⌞b⌟b' , (∙-incr e' ᵒ»ᵉ e'∙a'≈d' »ᵉ d'≈b')
⌞⌟-mono (nothing , a≈b) ⌞a⌟a' with ⌞⌟-cong a≈b ⌞a⌟a'
... | (b' , ⌞b⌟b' , a'≈b') = b' , ⌞b⌟b' , ≈⇒≤ a'≈b'
