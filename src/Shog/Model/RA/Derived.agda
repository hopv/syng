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
open import Data.Maybe.Base using (just)
open import Data.Product using (_×_; _,_; ∃-syntax)
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
-- Derived pre-order ≤

infix 4 _≤_

_≤_ : Car → Car → Set (ℓ ⊔ ℓ≈)
a ≤ b = ∃[ c ] c ∙ a ≈ b

----------------------------------------------------------------------
-- On ≤

infixr -1 _»ᵒ_ _ᵉ»ᵒ_ _ᵒ»ᵉ_ -- the same fixity with _$_

-- ≤ is transitive
_»ᵒ_ : a ≤ b → b ≤ c → a ≤ c
(d , d∙a≈b) »ᵒ (e , e∙b≈c) = d ∙ e ,_ $
  ∙-cong₀ ∙-comm »ᵉ ∙-assoc₀ »ᵉ ∙-cong₁ d∙a≈b »ᵉ e∙b≈c

-- ≤ preserves ≈

_ᵉ»ᵒ_ : a ≈ b → b ≤ c → a ≤ c
a≈b ᵉ»ᵒ (d , d∙b≈c) = d ,_ $ ∙-cong₁ a≈b »ᵉ d∙b≈c

_ᵒ»ᵉ_ : a ≤ b → b ≈ c → a ≤ c
(d , d∙a≈b) ᵒ»ᵉ b≈c = d ,_ $ d∙a≈b »ᵉ b≈c

----------------------------------------------------------------------
-- Monotonicity of ✓, ∙ and ⌞⌟

✓-mono : a ≤ b → ✓ b → ✓ a
✓-mono (c , c∙a≈b) ✓b = ✓-rem $ ✓-cong (symm c∙a≈b) ✓b

∙-mono₀ : a ≤ b → a ∙ c ≤ b ∙ c
∙-mono₀ (d , d∙a≈b) = d ,_ $ ∙-assoc₁ »ᵉ ∙-cong₀ d∙a≈b

∙-mono₁ : a ≤ b → c ∙ a ≤ c ∙ b
∙-mono₁ a≤b = ∙-comm ᵉ»ᵒ ∙-mono₀ a≤b ᵒ»ᵉ ∙-comm

∙-mono : a ≤ b → c ≤ d → a ∙ c ≤ b ∙ d
∙-mono a≤b c≤d = ∙-mono₀ a≤b »ᵒ ∙-mono₁ c≤d

⌞⌟-mono : a ≤ b → ⌞ a ⌟ ≡ just a' → ∃[ b' ] ⌞ b ⌟ ≡ just b' × a' ≤ b'
⌞⌟-mono (c , c∙a≈b) ⌞a⌟a' with ⌞⌟-add {b = c} ⌞a⌟a'
... | (d' , ⌞c∙a⌟d' , a'≤d') with ⌞⌟-cong c∙a≈b ⌞c∙a⌟d'
... | (b' , ⌞b⌟b' , d'≈b') = b' , ⌞b⌟b' , (a'≤d' ᵒ»ᵉ d'≈b')
