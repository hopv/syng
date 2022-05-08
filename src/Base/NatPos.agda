--------------------------------------------------------------------------------
-- Positive natural number
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.NatPos where

open import Base.Nat using (ℕ; suc; _+_; _*_; +-comm; +-assocˡ; +-injˡ; *-comm;
  *-assocˡ; *-injˡ; *-+-distrˡ)
open import Base.Eq using (_≡_; refl⁼; sym⁼; _»⁼_; cong⁼; cong⁼₂)
open import Base.Func using (_$_)

--------------------------------------------------------------------------------
-- ℕ⁺: Positive natural number

record ℕ⁺ : Set where
  constructor 1+
  field un1+ : ℕ

private variable
  l⁺ m⁺ n⁺ : ℕ⁺

--------------------------------------------------------------------------------
-- Operations on ℕ⁺

-- Back to ℕ

ℕ⁺⇒ℕ : ℕ⁺ → ℕ
ℕ⁺⇒ℕ (1+ n) = suc n

-- Addition

infixl 6 _+⁺_
_+⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
1+ m +⁺ 1+ n = 1+ $ m + (suc n)
-- Defined so because "suc m + suc n" reduces to "suc (m + (suc n))"

-- Multiplication

infixl 7 _*⁺_
_*⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
1+ m *⁺ 1+ n = 1+ $ n + m * (suc n)
-- Defined so because "suc m * suc n" reduces to "suc (n + m * (suc n))"

abstract

  -- ℕ⁺⇒ℕ is injective

  ℕ⁺⇒ℕ-inj : ℕ⁺⇒ℕ m⁺ ≡ ℕ⁺⇒ℕ n⁺ → m⁺ ≡ n⁺
  ℕ⁺⇒ℕ-inj refl⁼ = refl⁼

  -- +⁺ is commutative

  +⁺-comm : m⁺ +⁺ n⁺ ≡ n⁺ +⁺ m⁺
  +⁺-comm {1+ m} = ℕ⁺⇒ℕ-inj $ +-comm {suc m}

  -- +⁺ is associative

  +⁺-assocˡ : (l⁺ +⁺ m⁺) +⁺ n⁺ ≡ l⁺ +⁺ (m⁺ +⁺ n⁺)
  +⁺-assocˡ {1+ l} = ℕ⁺⇒ℕ-inj $ +-assocˡ {suc l}

  +⁺-assocʳ : l⁺ +⁺ (m⁺ +⁺ n⁺) ≡ (l⁺ +⁺ m⁺) +⁺ n⁺
  +⁺-assocʳ = sym⁼ +⁺-assocˡ

  -- +⁺ is injective

  +⁺-injˡ : ∀ {l⁺ m⁺ n⁺} → m⁺ +⁺ l⁺ ≡ n⁺ +⁺ l⁺ → m⁺ ≡ n⁺
  +⁺-injˡ {1+ l} m⁺+l⁺≡n⁺+l⁺ = ℕ⁺⇒ℕ-inj $ +-injˡ $ cong⁼ ℕ⁺⇒ℕ m⁺+l⁺≡n⁺+l⁺

  +⁺-injʳ : l⁺ +⁺ m⁺ ≡ l⁺ +⁺ n⁺ → m⁺ ≡ n⁺
  +⁺-injʳ {l⁺} {m⁺} {n⁺} rewrite +⁺-comm {l⁺} {m⁺} | +⁺-comm {l⁺} {n⁺} = +⁺-injˡ

  -- *⁺ is commutative

  *⁺-comm : m⁺ *⁺ n⁺ ≡ n⁺ *⁺ m⁺
  *⁺-comm {1+ m} = ℕ⁺⇒ℕ-inj $ *-comm {suc m}

  -- *⁺ is associative

  *⁺-assocˡ : (l⁺ *⁺ m⁺) *⁺ n⁺ ≡ l⁺ *⁺ (m⁺ *⁺ n⁺)
  *⁺-assocˡ {1+ l} {1+ m} = ℕ⁺⇒ℕ-inj $ *-assocˡ {suc l} {suc m}

  *⁺-assocʳ : l⁺ *⁺ (m⁺ *⁺ n⁺) ≡ (l⁺ *⁺ m⁺) *⁺ n⁺
  *⁺-assocʳ {l⁺} {m⁺} = sym⁼ $ *⁺-assocˡ {l⁺} {m⁺}

  -- *⁺ is injective

  *⁺-injˡ : ∀ {l⁺ m⁺ n⁺} → m⁺ *⁺ l⁺ ≡ n⁺ *⁺ l⁺ → m⁺ ≡ n⁺
  *⁺-injˡ {1+ l} m⁺*l⁺≡n⁺*l⁺ = ℕ⁺⇒ℕ-inj $ *-injˡ $ cong⁼ ℕ⁺⇒ℕ m⁺*l⁺≡n⁺*l⁺

  *⁺-injʳ : l⁺ *⁺ m⁺ ≡ l⁺ *⁺ n⁺ → m⁺ ≡ n⁺
  *⁺-injʳ {l⁺} {m⁺} {n⁺} rewrite *⁺-comm {l⁺} {m⁺} | *⁺-comm {l⁺} {n⁺} = *⁺-injˡ

  -- *⁺ is distributive over +⁺

  *⁺-+⁺-distrˡ : (l⁺ +⁺ m⁺) *⁺ n⁺ ≡ l⁺ *⁺ n⁺ +⁺ m⁺ *⁺ n⁺
  *⁺-+⁺-distrˡ {1+ l} = ℕ⁺⇒ℕ-inj $ *-+-distrˡ {suc l}

  *⁺-+⁺-distrʳ : l⁺ *⁺ (m⁺ +⁺ n⁺) ≡ l⁺ *⁺ m⁺ +⁺ l⁺ *⁺ n⁺
  *⁺-+⁺-distrʳ {l⁺} {m⁺} {n⁺} = *⁺-comm {l⁺} »⁼ *⁺-+⁺-distrˡ {m⁺} »⁼
    cong⁼₂ _+⁺_ (*⁺-comm {m⁺}) (*⁺-comm {n⁺})
