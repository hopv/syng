--------------------------------------------------------------------------------
-- Natural number
--------------------------------------------------------------------------------

module Base.Nat where

open import Base.Level using (0ˡ)
open import Base.Eq using (_≡_; refl⁼; sym⁼; _»⁼_; cong⁼; cong⁼₂)
open import Base.Func using (_$_)
open import Base.NElem using (¬)

--------------------------------------------------------------------------------
-- ℕ: Natural number
open import Agda.Builtin.Nat public
  using (zero; suc) renaming (Nat to ℕ)

private variable
  l m n : ℕ

--------------------------------------------------------------------------------
-- +, ∸, * : Addition, truncated subtraction, multiplication

open import Agda.Builtin.Nat public
  using (_+_; _*_) renaming (_-_ to _∸_)

abstract

  -- Clearing the right-hand side of +

  +-0 : n + 0 ≡ n
  +-0 {0} = refl⁼
  +-0 {suc n'} = cong⁼ suc $ +-0 {n'}

  +-suc : m + suc n ≡ suc (m + n)
  +-suc {0} = refl⁼
  +-suc {suc m'} = cong⁼ suc $ +-suc {m'}

  -- + is commutative

  +-comm : m + n ≡ n + m
  +-comm {_} {0} = +-0
  +-comm {_} {suc n'} = +-suc »⁼ cong⁼ suc (+-comm {_} {n'})

  -- + is associative

  +-assocˡ : (l + m) + n ≡ l + (m + n)
  +-assocˡ {0} = refl⁼
  +-assocˡ {suc l'} = cong⁼ suc $ +-assocˡ {l'}

  +-assocʳ : l + (m + n) ≡ (l + m) + n
  +-assocʳ {l} = sym⁼ $ +-assocˡ {l}

  -- Clearing the right-hand side of *

  *-0 : n * 0 ≡ 0
  *-0 {0} = refl⁼
  *-0 {suc n'} = *-0 {n'}

  *-suc : m * suc n ≡ m + m * n
  *-suc {0} = refl⁼
  *-suc {suc m'} {n} = cong⁼ (suc n +_) (*-suc {m'}) »⁼ cong⁼ suc $
    +-assocʳ {n} »⁼ cong⁼ (_+ m' * n) (+-comm {n}) »⁼ +-assocˡ {m'}

  -- * is commutative

  *-comm : m * n ≡ n * m
  *-comm {m} {0} = *-0 {m}
  *-comm {m} {suc n'} = *-suc {m} »⁼ cong⁼ (m +_) (*-comm {_} {n'})

  -- * is distributive over +

  *-+-distrˡ : (l + m) * n ≡ l * n + m * n
  *-+-distrˡ {0} = refl⁼
  *-+-distrˡ {suc l'} {_} {n} = cong⁼ (n +_) (*-+-distrˡ {l'}) »⁼ +-assocʳ {n}

  *-+-distrʳ : l * (m + n) ≡ l * m + l * n
  *-+-distrʳ {l} {m} {n} = *-comm {l} »⁼ *-+-distrˡ {m} »⁼
    cong⁼₂ _+_ (*-comm {m}) (*-comm {n})

  -- * is associative

  *-assocˡ : (l * m) * n ≡ l * (m * n)
  *-assocˡ {0} = refl⁼
  *-assocˡ {suc l'} {m} {n} = *-+-distrˡ {m} »⁼ cong⁼ (m * n +_) $ *-assocˡ {l'}

  *-assocʳ : l * (m * n) ≡ (l * m) * n
  *-assocʳ {l} = sym⁼ $ *-assocˡ {l}

--------------------------------------------------------------------------------
-- ≤, <: Order

infix 4 _≤_ _<_

data _≤_ : ℕ → ℕ → Set 0ˡ where
  0≤ : ∀ {n} → 0 ≤ n
  suc≤suc : ∀ {m n} → m ≤ n → suc m ≤ suc n

_<_ : ℕ → ℕ → Set 0ˡ
m < n = suc m ≤ n

abstract

  -- ≤ is reflexive

  ≤-refl : n ≤ n
  ≤-refl {0} = 0≤
  ≤-refl {suc _} = suc≤suc ≤-refl

  -- ≤ is transitive

  ≤-trans : l ≤ m → m ≤ n → l ≤ n
  ≤-trans 0≤ _ = 0≤
  ≤-trans (suc≤suc l≤m) (suc≤suc m≤n) = suc≤suc $ ≤-trans l≤m m≤n

  -- Composing ≤ and <

  ≤-<-trans : l ≤ m → m < n → l < n
  ≤-<-trans l≤m sm≤n = ≤-trans (suc≤suc l≤m) sm≤n

  <-≤-trans : l < m → m ≤ n → l < n
  <-≤-trans sl≤m m≤n = ≤-trans sl≤m m≤n

  -- suc is increasing

  suc-incr : n ≤ suc n
  suc-incr {0} = 0≤
  suc-incr {suc _} = suc≤suc suc-incr

  -- < into ≤

  <⇒≤ : m < n → m ≤ n
  <⇒≤ sm≤n = ≤-trans suc-incr sm≤n

  -- < is transitive

  <-trans : l < m → m < n → l < n
  <-trans l<m m<n = <-≤-trans l<m (<⇒≤ m<n)

  -- ≤ is antisymmetric

  ≤-antisym : m ≤ n → n ≤ m → m ≡ n
  ≤-antisym 0≤ 0≤ = refl⁼
  ≤-antisym (suc≤suc m'≤n') (suc≤suc n'≤m') = cong⁼ suc $ ≤-antisym m'≤n' n'≤m'

  -- < is asymmetric

  <-antisym : m < n → ¬ (n < m)
  <-antisym (suc≤suc m'<n') (suc≤suc n'<m') = <-antisym m'<n' n'<m'

--------------------------------------------------------------------------------
-- ⊔: Maximum

_⊔_ : ℕ → ℕ → ℕ
0 ⊔ n = n
m ⊔ 0 = m
suc m ⊔ suc n = suc (m ⊔ n)

abstract

  -- Clearing ⊔ 0

  ⊔-0 : n ⊔ 0 ≡ n
  ⊔-0 {0} = refl⁼
  ⊔-0 {suc _} = refl⁼

  -- ⊔ is the lub of m and n

  ⊔-introˡ : m ≤ m ⊔ n
  ⊔-introˡ {0} = 0≤
  ⊔-introˡ {suc _} {0} = ≤-refl
  ⊔-introˡ {suc _} {suc _} = suc≤suc ⊔-introˡ

  ⊔-introʳ : m ≤ n ⊔ m
  ⊔-introʳ {_} {0} = ≤-refl
  ⊔-introʳ {0} {suc _} = 0≤
  ⊔-introʳ {suc m'} {suc n'} = suc≤suc $ ⊔-introʳ {m'} {n'}

  ⊔-elim : ∀{l m n} → l ≤ n → m ≤ n → l ⊔ m ≤ n
  ⊔-elim {0} _ m≤n = m≤n
  ⊔-elim {suc _} {0} l≤n _ = l≤n
  ⊔-elim (suc≤suc l'≤n') (suc≤suc m'≤n') = suc≤suc $ ⊔-elim l'≤n' m'≤n'

  -- ⊔ is commutative and associative

  ⊔-comm : m ⊔ n ≡ n ⊔ m
  ⊔-comm {0} {_} = sym⁼ ⊔-0
  ⊔-comm {_} {0} = ⊔-0
  ⊔-comm {suc m'} {suc _} = cong⁼ suc (⊔-comm {m'})

  ⊔-assocˡ : (l ⊔ m) ⊔ n ≡ l ⊔ (m ⊔ n)
  ⊔-assocˡ {0} = refl⁼
  ⊔-assocˡ {suc _} {0} = refl⁼
  ⊔-assocˡ {suc _} {suc _} {0} = refl⁼
  ⊔-assocˡ {suc l'} {suc _} {suc _} = cong⁼ suc (⊔-assocˡ {l'})

  ⊔-assocʳ : l ⊔ (m ⊔ n) ≡ (l ⊔ m) ⊔ n
  ⊔-assocʳ {l} = sym⁼ $ ⊔-assocˡ {l}
