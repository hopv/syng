----------------------------------------------------------------------
-- Fractional resource algebra
----------------------------------------------------------------------
-- We use unnormalized rationals instead of normalized
-- for much better compile-time performance

{-# OPTIONS --without-K --safe #-}

module Shog.Model.RA.Frac where

open import Level using (Level)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Rational.Unnormalised.Base using (
  ℚᵘ; 0ℚᵘ; 1ℚᵘ; _≃_; _+_; NonNegative; nonNegative)
open import Data.Rational.Unnormalised.Properties using (
 +-identityˡ; +-comm; +-assoc; nonNegative⁻¹; ≤-steps)
open import Data.Product using (Σ-syntax; _,_)
open import Function.Base using (id; _$_)

open import Shog.Model.RA using (RA)
open RA

------------------------------------------------------------------------
-- ℚ₊ : Non-negative rational numbers

ℚ₊ : Set
ℚ₊ = Σ[ q ∈ ℚᵘ ] (NonNegative q)

0ℚ₊ : ℚ₊
0ℚ₊ = (0ℚᵘ , _)

1ℚ₊ : ℚ₊
1ℚ₊ = (1ℚᵘ , _)

private variable
 p q r : ℚᵘ
 p₊ q₊ r₊ : ℚ₊

------------------------------------------------------------------------
-- ≃₊ : Equivalence over ℚ₊

infix 4 _≃₊_

_≃₊_ : ℚ₊ → ℚ₊ → Set
(p , _) ≃₊ (q , _) = p ≃ q

------------------------------------------------------------------------
-- +₊ : Addition over ℚ₊

infixl 6 _+₊_

+-nonNeg : NonNegative p → NonNegative q → NonNegative (p + q)
+-nonNeg 0≤p 0≤q = nonNegative $ ≤-steps 0≤p $ nonNegative⁻¹ 0≤q

_+₊_ : ℚ₊ → ℚ₊ → ℚ₊
(p , 0≤p) +₊ (q , 0≤q) = p + q , +-nonNeg 0≤p 0≤q

------------------------------------------------------------------------
-- +₊ is unital w.r.t. 0ℚ₊, commutative, and associative

+₊-unit₀ : 0ℚ₊ +₊ p₊ ≃₊ p₊
+₊-unit₀ {p₊ = (p , _)} = +-identityˡ p

+₊-comm : p₊ +₊ q₊ ≃₊ q₊ +₊ p₊
+₊-comm {p₊ = (p , _)} {q₊ = (q , _)} = +-comm p q

+₊-assoc₀ : (p₊ +₊ q₊) +₊ r₊ ≃₊ p₊ +₊ (q₊ +₊ r₊)
+₊-assoc₀ {p₊ = (p , _)} {q₊ = (q , _)} {r₊ = (r , _)} = +-assoc p q r
