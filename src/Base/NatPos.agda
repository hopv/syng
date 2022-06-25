--------------------------------------------------------------------------------
-- Positive natural number
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.NatPos where

open import Base.Nat using (ℕ; suc; _≤_; _<_; _≡ᵇ_; _≤ᵇ_; _<ᵇ_; cmp; _+_; _*_;
  suc≤suc; suc<suc; ≤-refl; ≤-trans; ≤-antisym; <-irrefl; <-trans; <-asym; <⇒≤;
  ≤-<-trans; <-≤-trans; ≤⇒¬>; suc≤suc⁻¹; suc<suc⁻¹; suc-sincr; ᵇ⇒≡; ≡⇒ᵇ; ᵇ⇒≤;
  ≤⇒ᵇ; ᵇ⇒<; <⇒ᵇ; +-comm; +-assocˡ; +-injˡ; +-0; +-incrˡ; +-smonoʳ; *-comm;
  *-assocˡ; *-injˡ; *-+-distrˡ; *-monoˡ; *-smonoˡ)
open import Base.Eq using (_≡_; refl⁼; sym⁼; _»⁼_; cong; cong₂; subst; subst₂)
open import Base.Func using (_$_)
open import Base.Bool using (Bool; Tt)
open import Base.Few using (¬_)
open import Base.Sum using (_⊎_; inj₀; inj₁₀; inj₁₁)

--------------------------------------------------------------------------------
-- ℕ⁺: Positive natural number

record  ℕ⁺ :  Set  where
  constructor 1+
  field  un1+ :  ℕ

private variable
  k l m n :  ℕ⁺

--------------------------------------------------------------------------------
-- 1⁺, 2⁺, 3⁺, 4⁺, 5⁺: Numbers in ℕ⁺

1⁺ 2⁺ 3⁺ 4⁺ 5⁺ :  ℕ⁺
1⁺ =  1+ 0
2⁺ =  1+ 1
3⁺ =  1+ 2
4⁺ =  1+ 3
5⁺ =  1+ 4

--------------------------------------------------------------------------------
-- ℕ⁺⇒ℕ: Back to ℕ

ℕ⁺⇒ℕ :  ℕ⁺ →  ℕ
ℕ⁺⇒ℕ (1+ n⁰) =  suc n⁰

abstract

  -- ℕ⁺⇒ℕ is injective

  ℕ⁺⇒ℕ-inj :  ℕ⁺⇒ℕ m ≡ ℕ⁺⇒ℕ n →  m ≡ n
  ℕ⁺⇒ℕ-inj refl⁼ =  refl⁼

--------------------------------------------------------------------------------
-- ≤⁺, <⁺, ≥⁺, >⁺: Order

infix 4 _≤⁺_ _<⁺_ _≥⁺_ _>⁺_
_≤⁺_ _<⁺_ _≥⁺_ _>⁺_ :  ℕ⁺ → ℕ⁺ → Set
1+ m⁰ ≤⁺ 1+ n⁰ =  m⁰ ≤ n⁰
1+ m⁰ <⁺ 1+ n⁰ =  m⁰ < n⁰
p ≥⁺ q =  q ≤⁺ p
p >⁺ q =  q <⁺ p

abstract

  -- ≤⁺ is reflexive, transitive and antisymmetric

  ≤⁺-refl :  n ≤⁺ n
  ≤⁺-refl =  ≤-refl

  ≤⁺-trans :  l ≤⁺ m →  m ≤⁺ n →  l ≤⁺ n
  ≤⁺-trans =  ≤-trans

  ≤⁺-antisym :  m ≤⁺ n →  n ≤⁺ m →  m ≡ n
  ≤⁺-antisym mᵒ≤nᵒ nᵒ≤mᵒ =  cong 1+ $ ≤-antisym mᵒ≤nᵒ nᵒ≤mᵒ

  -- <⁺ is irreflexive, transitive and asymmetric

  <⁺-irrefl :  ¬ n <⁺ n
  <⁺-irrefl =  <-irrefl

  ≡⇒¬<⁺ :  m ≡ n →  ¬ m <⁺ n
  ≡⇒¬<⁺ refl⁼ =  <⁺-irrefl

  <⁺-trans :  l <⁺ m →  m <⁺ n →  l <⁺ n
  <⁺-trans =  <-trans

  <⁺-asym :  m <⁺ n →  ¬ m >⁺ n
  <⁺-asym =  <-asym

  -- <⁺ into ≤⁺

  <⁺⇒≤⁺ :  m <⁺ n →  m ≤⁺ n
  <⁺⇒≤⁺ =  <⇒≤

  -- Composing ≤⁺ and <⁺

  ≤⁺-<⁺-trans :  l ≤⁺ m →  m <⁺ n →  l <⁺ n
  ≤⁺-<⁺-trans =   ≤-<-trans

  <⁺-≤⁺-trans :  l <⁺ m →  m ≤⁺ n →  l <⁺ n
  <⁺-≤⁺-trans =  <-≤-trans

  -- ≤⁺ and >⁺ do not hold at the same time

  ≤⁺⇒¬>⁺ :  m ≤⁺ n →  ¬ m >⁺ n
  ≤⁺⇒¬>⁺ =  ≤⇒¬>

  -- Get <⁺, ≡ or >⁺

  cmp⁺ :  ∀ m n →  m <⁺ n  ⊎  m ≡ n  ⊎  m >⁺ n
  cmp⁺ (1+ m⁰) (1+ n⁰)  with cmp m⁰ n⁰
  ... | inj₀ m⁰<n⁰ =  inj₀ m⁰<n⁰
  ... | inj₁₀ refl⁼ =  inj₁₀ refl⁼
  ... | inj₁₁ m⁰>n⁰ =  inj₁₁ m⁰>n⁰

--------------------------------------------------------------------------------
-- ≡⁺ᵇ, ≤⁺ᵇ, <⁺ᵇ, ≥⁺ᵇ, >⁺ᵇ: Boolean order

infix 4 _≡⁺ᵇ_ _≤⁺ᵇ_ _<⁺ᵇ_ _≥⁺ᵇ_ _>⁺ᵇ_
_≡⁺ᵇ_ _≤⁺ᵇ_ _<⁺ᵇ_ _≥⁺ᵇ_ _>⁺ᵇ_ :  ℕ⁺ → ℕ⁺ → Bool
1+ m⁰ ≡⁺ᵇ 1+ n⁰ =  m⁰ ≡ᵇ n⁰
1+ m⁰ ≤⁺ᵇ 1+ n⁰ =  m⁰ ≤ᵇ n⁰
1+ m⁰ <⁺ᵇ 1+ n⁰ =  m⁰ <ᵇ n⁰
p ≥⁺ᵇ q =  q ≤⁺ᵇ p
p >⁺ᵇ q =  q <⁺ᵇ p

abstract

  -- Conversion between ≡ᵇ and ≡

  ⁺ᵇ⇒≡ :  Tt (m ≡⁺ᵇ n) →  m ≡ n
  ⁺ᵇ⇒≡ m⁰≡ᵇn⁰ =  cong 1+ (ᵇ⇒≡ m⁰≡ᵇn⁰)

  ≡⇒⁺ᵇ :  m ≡ n →  Tt (m ≡⁺ᵇ n)
  ≡⇒⁺ᵇ {1+ m⁰} {1+ n⁰} refl⁼ =  ≡⇒ᵇ {m⁰} {n⁰} refl⁼

  -- Conversion between ≤ᵇ and ≤

  ᵇ⇒≤⁺ :  Tt (m ≤⁺ᵇ n) →  m ≤⁺ n
  ᵇ⇒≤⁺ =  ᵇ⇒≤

  ≤⁺⇒ᵇ :  m ≤⁺ n →  Tt (m ≤⁺ᵇ n)
  ≤⁺⇒ᵇ =  ≤⇒ᵇ

  -- Conversion between <ᵇ and <

  ᵇ⇒<⁺ :  Tt (m <⁺ᵇ n) →  m <⁺ n
  ᵇ⇒<⁺ =  ᵇ⇒<

  <⁺⇒ᵇ :  m <⁺ n →  Tt (m <⁺ᵇ n)
  <⁺⇒ᵇ =  <⇒ᵇ

--------------------------------------------------------------------------------
-- +⁺: Addition

infixl 6 _+⁺_
_+⁺_ :  ℕ⁺ → ℕ⁺ → ℕ⁺
1+ m⁰ +⁺ 1+ n⁰ =  1+ $ m⁰ + (suc n⁰)
-- Defined so because "suc m⁰ + suc n⁰" reduces to "suc (m⁰ + (suc n⁰))"

abstract

  -- +⁺ is commutative

  +⁺-comm :  m +⁺ n ≡ n +⁺ m
  +⁺-comm {1+ m⁰} =  ℕ⁺⇒ℕ-inj $ +-comm {suc m⁰}

  -- +⁺ is associative

  +⁺-assocˡ :  (l +⁺ m) +⁺ n ≡ l +⁺ (m +⁺ n)
  +⁺-assocˡ {1+ l⁰} =  ℕ⁺⇒ℕ-inj $ +-assocˡ {suc l⁰}

  +⁺-assocʳ :  l +⁺ (m +⁺ n) ≡ (l +⁺ m) +⁺ n
  +⁺-assocʳ =  sym⁼ +⁺-assocˡ

  -- +⁺ is injective

  +⁺-injˡ :  ∀ {l m n} →  m +⁺ l ≡ n +⁺ l →  m ≡ n
  +⁺-injˡ {1+ l⁰} m+l≡n+l =  ℕ⁺⇒ℕ-inj $ +-injˡ $ cong ℕ⁺⇒ℕ m+l≡n+l

  +⁺-injʳ :  l +⁺ m ≡ l +⁺ n →  m ≡ n
  +⁺-injʳ {l} {m} {n} rewrite +⁺-comm {l} {m} | +⁺-comm {l} {n} =  +⁺-injˡ

  -- +⁺ strictly increases

  +⁺-sincrˡ :  ∀ {m n} →  n <⁺ m +⁺ n
  +⁺-sincrˡ =  ≤-<-trans +-incrˡ (+-smonoʳ suc-sincr)

  +⁺-sincrʳ :  m <⁺ m +⁺ n
  +⁺-sincrʳ {m} =  subst (m <⁺_) +⁺-comm +⁺-sincrˡ

--------------------------------------------------------------------------------
-- *⁺: Multiplication

infixl 7 _*⁺_
_*⁺_ :  ℕ⁺ → ℕ⁺ → ℕ⁺
1+ m⁰ *⁺ 1+ n⁰ =  1+ $ n⁰ + m⁰ * (suc n⁰)
-- Defined so because "suc m⁰ * suc n⁰" reduces to "suc (n⁰ + m⁰ * (suc n⁰))"

abstract

  -- *⁺ is commutative

  *⁺-comm :  m *⁺ n ≡ n *⁺ m
  *⁺-comm {1+ m⁰} =  ℕ⁺⇒ℕ-inj $ *-comm {suc m⁰}

  -- *⁺ is associative

  *⁺-assocˡ :  (l *⁺ m) *⁺ n ≡ l *⁺ (m *⁺ n)
  *⁺-assocˡ {1+ l⁰} {1+ m⁰} =  ℕ⁺⇒ℕ-inj $ *-assocˡ {suc l⁰} {suc m⁰}

  *⁺-assocʳ :  l *⁺ (m *⁺ n) ≡ (l *⁺ m) *⁺ n
  *⁺-assocʳ {l} {m} =  sym⁼ $ *⁺-assocˡ {l} {m}

  -- Commutativity over left/right actions

  *⁺-actˡ-comm :  l *⁺ (m *⁺ n) ≡ m *⁺ (l *⁺ n)
  *⁺-actˡ-comm {l} {m} {n} =  *⁺-assocʳ {l} {m} {n} »⁼
      cong (_*⁺ n) (*⁺-comm {l} {m}) »⁼ *⁺-assocˡ {m} {l} {n}

  *⁺-actʳ-comm :  (l *⁺ m) *⁺ n ≡ (l *⁺ n) *⁺ m
  *⁺-actʳ-comm {l} {m} {n} =  *⁺-assocˡ {l} {m} {n} »⁼
      cong (l *⁺_) (*⁺-comm {m} {n}) »⁼ *⁺-assocʳ {l} {n} {m}

  -- *⁺ is injective

  *⁺-injˡ :  ∀ {l m n} →  m *⁺ l ≡ n *⁺ l →  m ≡ n
  *⁺-injˡ {1+ l⁰} m*l≡n*l =  ℕ⁺⇒ℕ-inj $ *-injˡ $ cong ℕ⁺⇒ℕ m*l≡n*l

  *⁺-injʳ :  l *⁺ m ≡ l *⁺ n →  m ≡ n
  *⁺-injʳ {l} {m} {n} rewrite *⁺-comm {l} {m} | *⁺-comm {l} {n} =  *⁺-injˡ

  -- *⁺ is distributive over +⁺

  *⁺-+⁺-distrˡ :  (l +⁺ m) *⁺ n ≡ l *⁺ n +⁺ m *⁺ n
  *⁺-+⁺-distrˡ {1+ l⁰} =  ℕ⁺⇒ℕ-inj $ *-+-distrˡ {suc l⁰}

  *⁺-+⁺-distrʳ :  l *⁺ (m +⁺ n) ≡ l *⁺ m +⁺ l *⁺ n
  *⁺-+⁺-distrʳ {l} {m} {n} =  *⁺-comm {l} »⁼ *⁺-+⁺-distrˡ {m} »⁼
    cong₂ _+⁺_ (*⁺-comm {m}) (*⁺-comm {n})

  -- *⁺ is unital with 1⁺

  *⁺-1ˡ :  1⁺ *⁺ n ≡ n
  *⁺-1ˡ =  cong 1+ +-0

  *⁺-1ʳ :  n *⁺ 1⁺ ≡ n
  *⁺-1ʳ {n} rewrite *⁺-comm {n} {1⁺} =  *⁺-1ˡ {n}

  -- *⁺ is monotone

  *⁺-monoˡ :  l ≤⁺ m →  l *⁺ n ≤⁺ m *⁺ n
  *⁺-monoˡ {1+ l⁰} {1+ m⁰} {1+ n⁰} l⁰≤m⁰ =
    suc≤suc⁻¹ $ *-monoˡ {suc l⁰} {suc m⁰} {suc n⁰} $ suc≤suc l⁰≤m⁰

  *⁺-monoʳ :  ∀ {l m n} →  m ≤⁺ n →  l *⁺ m ≤⁺ l *⁺ n
  *⁺-monoʳ {l} {m} {n} m≤n =  subst₂ _≤⁺_ (*⁺-comm {m} {l}) (*⁺-comm {n} {l})
    (*⁺-monoˡ m≤n)

  *⁺-mono :  k ≤⁺ l →  m ≤⁺ n →  k *⁺ m ≤⁺ l *⁺ n
  *⁺-mono {l = l} k≤l m≤n =  ≤⁺-trans (*⁺-monoˡ k≤l) (*⁺-monoʳ {l} m≤n)

  -- *⁺ is strictly monotone

  *⁺-smonoˡ :  l <⁺ m →  l *⁺ n <⁺ m *⁺ n
  *⁺-smonoˡ {1+ l⁰} {1+ m⁰} {1+ n⁰} l⁰<m⁰ =
    suc<suc⁻¹ $ *-smonoˡ {suc l⁰} {suc m⁰} {n⁰} $ suc<suc l⁰<m⁰

  *⁺-smonoʳ :  ∀ {l m n} →  m <⁺ n →  l *⁺ m <⁺ l *⁺ n
  *⁺-smonoʳ {l} {m} {n} m<n =  subst₂ _<⁺_ (*⁺-comm {m} {l}) (*⁺-comm {n} {l})
    (*⁺-smonoˡ m<n)

  *⁺-smono :  k <⁺ l →  m <⁺ n →  k *⁺ m <⁺ l *⁺ n
  *⁺-smono {l = l} k<l m<n =  <⁺-trans (*⁺-smonoˡ k<l) (*⁺-smonoʳ {l} m<n)
