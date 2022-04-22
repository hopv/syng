------------------------------------------------------------------------
-- ℚ⁺: Positive rationals
------------------------------------------------------------------------
-- We use unnormalized rationals instead of normalized
-- for much better compile-time performance

{-# OPTIONS --without-K --safe #-}

module Shog.Base.RatPos where

open import Level using (Level)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Rational.Unnormalised.Base using (
  ℚᵘ; 1ℚᵘ; _≃_; _+_; Positive; positive)
open import Data.Rational.Unnormalised.Properties using (
  ≃-refl; ≃-sym; ≃-trans; positive⁻¹; +-mono-<; +-cong; +-comm; +-assoc)
open import Data.Product using (Σ-syntax; _,_)
open import Function.Base using (id; _$_)

------------------------------------------------------------------------
-- ℚ⁺ : Non-negative rationals

ℚ⁺ : Set
ℚ⁺ = Σ[ q ∈ ℚᵘ ] (Positive q)

1ℚ⁺ : ℚ⁺
1ℚ⁺ = (1ℚᵘ , _)

private variable
 p q r s : ℚᵘ
 p⁺ q⁺ r⁺ s⁺ : ℚ⁺

------------------------------------------------------------------------
-- ≃⁺ : Equivalence over ℚ⁺

infix 4 _≃⁺_

_≃⁺_ : ℚ⁺ → ℚ⁺ → Set
(p , _) ≃⁺ (q , _) = p ≃ q

------------------------------------------------------------------------
-- ≃⁺ is reflexive, symmetric and transitive

≃⁺-id : p⁺ ≃⁺ p⁺
≃⁺-id = ≃-refl

≃⁺-sym : p⁺ ≃⁺ q⁺ → q⁺ ≃⁺ p⁺
≃⁺-sym {_ , _} {_ , _} = ≃-sym

infixr -1 _[≃⁺]»_

_[≃⁺]»_ : p⁺ ≃⁺ q⁺ → q⁺ ≃⁺ r⁺ → p⁺ ≃⁺ r⁺
_[≃⁺]»_ {_ , _} {_ , _} {_ , _} = ≃-trans

------------------------------------------------------------------------
-- +⁺ : Addition over ℚ⁺

infixl 6 _+⁺_

+-pos : Positive p → Positive q → Positive (p + q)
+-pos pos-p pos-q = positive $ +-mono-< (positive⁻¹ pos-p) (positive⁻¹ pos-q)

_+⁺_ : ℚ⁺ → ℚ⁺ → ℚ⁺
(p , pos-p) +⁺ (q , pos-q) = p + q , +-pos pos-p pos-q

------------------------------------------------------------------------
-- +⁺ preseves ≃⁺

+⁺-cong : p⁺ ≃⁺ q⁺ → r⁺ ≃⁺ s⁺ → p⁺ +⁺ r⁺ ≃⁺ q⁺ +⁺ s⁺
+⁺-cong {_ , _} {_ , _} {_ , _} {_ , _} = +-cong

-- +⁺ is commutative, and associative

+⁺-comm : p⁺ +⁺ q⁺ ≃⁺ q⁺ +⁺ p⁺
+⁺-comm {p , _} {q , _} = +-comm p q

+⁺-assoc₀ : (p⁺ +⁺ q⁺) +⁺ r⁺ ≃⁺ p⁺ +⁺ (q⁺ +⁺ r⁺)
+⁺-assoc₀ {p , _} {q , _} {r , _} = +-assoc p q r
