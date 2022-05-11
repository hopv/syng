--------------------------------------------------------------------------------
-- Natural number
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Nat where

open import Base.Eq using (_≡_; refl⁼; sym⁼; _»⁼_; cong⁼; cong⁼₂)
open import Base.Func using (_$_)
open import Base.Few using (¬_; absurd)
open import Base.Sum using (_⊎_; inj₀; inj₁₀; inj₁₁)
open import Base.Bool using (Bool; tt; Tt)
open import Base.Dec using (Dec²)

--------------------------------------------------------------------------------
-- ℕ: Natural number

open import Agda.Builtin.Nat public
  using (zero; suc) renaming (Nat to ℕ)

private variable
  k l m n : ℕ

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

data _≤_ : ℕ → ℕ → Set where
  0≤ : ∀ {n} → 0 ≤ n
  suc≤suc : ∀ {m n} → m ≤ n → suc m ≤ suc n

_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n

pattern 0<suc = suc≤suc 0≤
pattern suc<suc m<n = suc≤suc m<n
pattern ?<? = suc≤suc _

abstract

  -- ≤ is reflexive

  ≤-refl : n ≤ n
  ≤-refl {0} = 0≤
  ≤-refl {suc _} = suc≤suc ≤-refl

  -- < is irreflexive

  <-irrefl : ¬ n < n
  <-irrefl (suc≤suc n'<n') = <-irrefl n'<n'

  <-irrefl' : m ≡ n → ¬ m < n
  <-irrefl' refl⁼ = <-irrefl

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

  <-asym : m < n → ¬ n < m
  <-asym (suc<suc m'<n') (suc<suc n'<m') = <-asym m'<n' n'<m'

  -- Get <, ≡ or >

  cmp : ∀ m n → m < n ⊎ m ≡ n ⊎ n < m
  cmp 0 (suc _) = inj₀ 0<suc
  cmp 0 0 = inj₁₀ refl⁼
  cmp (suc _) 0 = inj₁₁ 0<suc
  cmp (suc m') (suc n') with cmp m' n'
  ... | inj₀ m'<n' =  inj₀ $ suc<suc m'<n'
  ... | inj₁₀ m'≡n' =  inj₁₀ $ cong⁼ suc m'≡n'
  ... | inj₁₁ m'>n' =  inj₁₁ (suc<suc m'>n')

  -- + is increasing

  +-incr : ∀ {m n} → n ≤ m + n
  +-incr {0} = ≤-refl
  +-incr {suc m'} = ≤-trans (+-incr {m'}) suc-incr

  -- + is monotone

  +-monoˡ : l ≤ m → l + n ≤ m + n
  +-monoˡ 0≤ = +-incr
  +-monoˡ (suc≤suc l'≤m') = suc≤suc $ +-monoˡ l'≤m'

  +-monoʳ : ∀{l m n} → m ≤ n → l + m ≤ l + n
  +-monoʳ {l} {m} {n} rewrite +-comm {l} {m} | +-comm {l} {n} = +-monoˡ

  +-mono : k ≤ l → m ≤ n → k + m ≤ l + n
  +-mono k≤l m≤n = ≤-trans (+-monoˡ k≤l) (+-monoʳ m≤n)

  -- + is strictly monotone

  +-smonoˡ : l < m → l + n < m + n
  +-smonoˡ = +-monoˡ

  +-smonoʳ : ∀{l m n} → m < n → l + m < l + n
  +-smonoʳ {l} {m} {n} rewrite +-comm {l} {m} | +-comm {l} {n} = +-smonoˡ

  +-smono : k < l → m < n → k + m < l + n
  +-smono k<l m<n = <-trans (+-smonoˡ k<l) (+-smonoʳ m<n)

  -- + is injective

  +-injˡ : ∀ {l m n} → m + l ≡ n + l → m ≡ n
  +-injˡ {_} {m} {n} m+l≡n+l with cmp m n
  ... | inj₀ m<n =  absurd $ <-irrefl' m+l≡n+l (+-smonoˡ m<n)
  ... | inj₁₀ m≡n =  m≡n
  ... | inj₁₁ m>n =  absurd $ <-irrefl' (sym⁼ m+l≡n+l) (+-smonoˡ m>n)

  +-injʳ : l + m ≡ l + n → m ≡ n
  +-injʳ {l} {m} {n} rewrite +-comm {l} {m} | +-comm {l} {n} = +-injˡ

  -- * is monotone

  *-monoˡ : l ≤ m → l * n ≤ m * n
  *-monoˡ 0≤ = 0≤
  *-monoˡ (suc≤suc l'≤m') = +-monoʳ $ *-monoˡ l'≤m'

  *-monoʳ : ∀{l m n} → m ≤ n → l * m ≤ l * n
  *-monoʳ {l} {m} {n} rewrite *-comm {l} {m} | *-comm {l} {n} = *-monoˡ

  *-mono : k ≤ l → m ≤ n → k * m ≤ l * n
  *-mono {l = l} k≤l m≤n = ≤-trans (*-monoˡ k≤l) (*-monoʳ {l} m≤n)

  -- * is strictly monotone when one argument is positive

  *-smonoˡ : l < m → l * suc n < m * suc n
  *-smonoˡ sl≤m = ≤-trans (suc≤suc +-incr) (*-monoˡ sl≤m)

  *-smonoʳ : ∀{l m n} → m < n → suc l * m < suc l * n
  *-smonoʳ {l} {m} {n} rewrite *-comm {suc l} {m} | *-comm {suc l} {n}
    = *-smonoˡ

  -- * with a positive argument is injective

  *-injˡ : ∀ {l m n} → m * suc l ≡ n * suc l → m ≡ n
  *-injˡ {_} {m} {n} m*sl≡n*sl with cmp m n
  ... | inj₀ m<n =  absurd $ <-irrefl' m*sl≡n*sl (*-smonoˡ m<n)
  ... | inj₁₀ m≡n =  m≡n
  ... | inj₁₁ m>n =  absurd $ <-irrefl' (sym⁼ m*sl≡n*sl) (*-smonoˡ m>n)

  *-injʳ : suc l * m ≡ suc l * n → m ≡ n
  *-injʳ {l} {m} {n} rewrite *-comm {suc l} {m} | *-comm {suc l} {n} = *-injˡ

--------------------------------------------------------------------------------
-- ≡ᵇ, ≤ᵇ, <ᵇ : Boolean order

open import Agda.Builtin.Nat public using () renaming (_==_ to _≡ᵇ_;
  _<_ to _<ᵇ_)

infix 4 _≤ᵇ_
_≤ᵇ_ : ℕ → ℕ → Bool
0 ≤ᵇ n = tt
suc m ≤ᵇ n = m <ᵇ n

abstract

  -- Convertion between ≡ᵇ and ≡

  ≡ᵇ⇒≡ : Tt (m ≡ᵇ n) → m ≡ n
  ≡ᵇ⇒≡ {0} {0} _ = refl⁼
  ≡ᵇ⇒≡ {suc m'} {suc n'} m'≡ᵇn' = cong⁼ suc $ ≡ᵇ⇒≡ m'≡ᵇn'

  ≡⇒≡ᵇ : m ≡ n → Tt (m ≡ᵇ n)
  ≡⇒≡ᵇ {0} {0} _ = _
  ≡⇒≡ᵇ {suc m'} {suc n'} refl⁼ = ≡⇒≡ᵇ {m'} {n'} refl⁼

  -- Convertion between <ᵇ and <

  <ᵇ⇒< : Tt (m <ᵇ n) → m < n
  <ᵇ⇒< {0} {suc _} _ = 0<suc
  <ᵇ⇒< {suc m'} {suc n'} m'<ᵇn' = suc<suc $ <ᵇ⇒< m'<ᵇn'

  <⇒<ᵇ : m < n → Tt (m <ᵇ n)
  <⇒<ᵇ 0<suc = _
  <⇒<ᵇ (suc<suc m'<n'@?<?) = <⇒<ᵇ m'<n'

  -- Convertion between ≤ᵇ and ≤

  ≤ᵇ⇒≤ : Tt (m ≤ᵇ n) → m ≤ n
  ≤ᵇ⇒≤ {0} _ = 0≤
  ≤ᵇ⇒≤ {suc m} m≤n = <ᵇ⇒< m≤n

  ≤⇒≤ᵇ : m ≤ n → Tt (m ≤ᵇ n)
  ≤⇒≤ᵇ 0≤ = _
  ≤⇒≤ᵇ m'<n@?<? = <⇒<ᵇ m'<n

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
