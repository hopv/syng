--------------------------------------------------------------------------------
-- Natural number
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Nat where

open import Base.Func using (_$_; _∘_)
open import Base.Few using (¬_; absurd)
open import Base.Eq using (_≡_; _≢_; refl; ◠_; _◇_; cong; cong₂)
open import Base.Sum using (_⊎_; inj₀; inj₁; inj₁₀; inj₁₁)
open import Base.Bool using (Bool; tt; ff; Tt; Tt⇒≡tt; ¬Tt⇒≡ff)
open import Base.Dec using (Dec²; yes; no)
open import Base.Dec.Construct using (dec-Tt)

--------------------------------------------------------------------------------
-- ℕ :  Natural number

open import Agda.Builtin.Nat public
  using (zero; suc) renaming (Nat to ℕ)

private variable
  k l m n :  ℕ

--------------------------------------------------------------------------------
-- ≤, <, ≤ᵈ, <ᵈ :  Order

infix 4 _≤_ _<_ _≥_ _>_ _≤ᵈ_ _<ᵈ_ _≥ᵈ_ _>ᵈ_

-- ≤ :  Order, with induction on the left-hand side

data  _≤_ :  ℕ → ℕ → Set₀  where
  0≤ :  0 ≤ n
  suc≤suc :  m ≤ n →  suc m ≤ suc n

-- ≤ᵈ :  Order, with induction on difference

data  _≤ᵈ_ :  ℕ → ℕ → Set₀  where
  ≤ᵈ-refl :  n ≤ᵈ n
  ≤ᵈsuc :  m ≤ᵈ n →  m ≤ᵈ suc n

_<_ _≥_ _>_ _<ᵈ_ _≥ᵈ_ _>ᵈ_ :  ℕ → ℕ → Set₀
m < n =  suc m ≤ n
m ≥ n =  n ≤ m
m > n =  n < m
m <ᵈ n =  suc m ≤ᵈ n
m ≥ᵈ n =  n ≤ᵈ m
m >ᵈ n =  n <ᵈ m

pattern 0<suc =  suc≤suc 0≤
pattern suc<suc m<n =  suc≤suc m<n
pattern ?<? =  suc≤suc _

abstract

  -- ≤ is reflexive

  ≤-refl :  n ≤ n
  ≤-refl {0} =  0≤
  ≤-refl {suc _} =  suc≤suc ≤-refl

  -- < is irreflexive

  <-irrefl :  ¬ n < n
  <-irrefl (suc≤suc n'<n') =  <-irrefl n'<n'

  ≡⇒¬< :  m ≡ n →  ¬ m < n
  ≡⇒¬< refl =  <-irrefl

  -- ≤ is transitive

  ≤-trans :  l ≤ m →  m ≤ n →  l ≤ n
  ≤-trans 0≤ _ =  0≤
  ≤-trans (suc≤suc l≤m) (suc≤suc m≤n) =  suc≤suc $ ≤-trans l≤m m≤n

  -- Composing ≤ and <

  ≤-<-trans :  l ≤ m →  m < n →  l < n
  ≤-<-trans l≤m sm≤n =  ≤-trans (suc≤suc l≤m) sm≤n

  <-≤-trans :  l < m →  m ≤ n →  l < n
  <-≤-trans sl≤m m≤n =  ≤-trans sl≤m m≤n

  -- suc is increasing

  suc-sincr :  n < suc n
  suc-sincr =  ≤-refl

  suc-incr :  n ≤ suc n
  suc-incr {0} =  0≤
  suc-incr {suc _} =  suc≤suc suc-incr

  -- < into ≤

  <⇒≤ :  m < n →  m ≤ n
  <⇒≤ sm≤n =  ≤-trans suc-incr sm≤n

  -- < is transitive

  <-trans :  l < m →  m < n →  l < n
  <-trans l<m m<n =  <-≤-trans l<m (<⇒≤ m<n)

  -- ≤ is antisymmetric

  ≤-antisym :  m ≤ n →  n ≤ m →  m ≡ n
  ≤-antisym 0≤ 0≤ =  refl
  ≤-antisym (suc≤suc m'≤n') (suc≤suc n'≤m') =  cong suc $ ≤-antisym m'≤n' n'≤m'

  -- ≤ and > do not hold at the same time

  ≤⇒¬> :  m ≤ n →  ¬ m > n
  ≤⇒¬> (suc≤suc m'≤n') (suc<suc m'>n') =  ≤⇒¬> m'≤n' m'>n'

  -- < is asymmetric

  <-asym :  m < n →  ¬ m > n
  <-asym m<n =  ≤⇒¬> $ <⇒≤ m<n

  -- Invert suc≤/<suc

  suc≤suc⁻¹ :  suc m ≤ suc n →  m ≤ n
  suc≤suc⁻¹ (suc≤suc m≤n) =   m≤n

  suc<suc⁻¹ :  suc m < suc n →  m < n
  suc<suc⁻¹ (suc<suc m<n) =   m<n

  infix 4 _<≡>_ _≤>_ _<≥_

  -- Get <, ≡ or >

  _<≡>_ :  ∀ m n →  m < n  ⊎  m ≡ n  ⊎  m > n
  0 <≡> (suc _) =  inj₀ 0<suc
  0 <≡> 0 =  inj₁₀ refl
  suc _ <≡> 0 =  inj₁₁ 0<suc
  suc m' <≡> suc n'  with m' <≡> n'
  ... | inj₀ m'<n' =  inj₀ $ suc<suc m'<n'
  ... | inj₁₀ refl =  inj₁₀ refl
  ... | inj₁₁ m'>n' =  inj₁₁ (suc<suc m'>n')

  -- Get ≤ or >

  _≤>_ :  ∀ m n →  m ≤ n  ⊎  m > n
  m ≤> n  with m <≡> n
  ... | inj₀ m<n =  inj₀ $ <⇒≤ m<n
  ... | inj₁₀ refl =  inj₀ ≤-refl
  ... | inj₁₁ m>n =  inj₁ m>n

  -- Get < or ≥

  _<≥_ :  ∀ m n →  m < n  ⊎  m ≥ n
  m <≥ n  with n ≤> m
  ... | inj₀ n≤m =  inj₁ n≤m
  ... | inj₁ n>m =  inj₀ n>m

  -- Conversion between ≤ and ≤ᵈ

  0≤ᵈ :  0 ≤ᵈ n
  0≤ᵈ {n = 0} =  ≤ᵈ-refl
  0≤ᵈ {n = suc n'} =  ≤ᵈsuc $ 0≤ᵈ {n = n'}

  suc≤ᵈsuc :  m ≤ᵈ n →  suc m ≤ᵈ suc n
  suc≤ᵈsuc ≤ᵈ-refl =  ≤ᵈ-refl
  suc≤ᵈsuc (≤ᵈsuc m≤ᵈn') =  ≤ᵈsuc $ suc≤ᵈsuc m≤ᵈn'

  ≤⇒≤ᵈ :  m ≤ n →  m ≤ᵈ n
  ≤⇒≤ᵈ 0≤ =  0≤ᵈ
  ≤⇒≤ᵈ (suc≤suc m≤n) =  suc≤ᵈsuc $ ≤⇒≤ᵈ m≤n

  ≤ᵈ⇒≤ :  m ≤ᵈ n →  m ≤ n
  ≤ᵈ⇒≤ ≤ᵈ-refl =  ≤-refl
  ≤ᵈ⇒≤ (≤ᵈsuc m≤ᵈn') =  ≤-trans (≤ᵈ⇒≤ m≤ᵈn') suc-incr

--------------------------------------------------------------------------------
-- ≡ᵇ, ≤ᵇ, <ᵇ : Boolean order

open import Agda.Builtin.Nat public using () renaming (_==_ to _≡ᵇ_;
  _<_ to _<ᵇ_)

infix 4 _≤ᵇ_ _≥ᵇ_ _>ᵇ_
_≤ᵇ_ _≥ᵇ_ _>ᵇ_ :  ℕ → ℕ → Bool
0 ≤ᵇ n =  tt
suc m ≤ᵇ n =  m <ᵇ n
m ≥ᵇ n =  n ≤ᵇ m
m >ᵇ n =  n <ᵇ m

abstract

  -- Conversion between ≡ᵇ and ≡

  ᵇ⇒≡ :  Tt (m ≡ᵇ n) →  m ≡ n
  ᵇ⇒≡ {0} {0} _ =  refl
  ᵇ⇒≡ {suc m'} {suc n'} m'≡ᵇn' =  cong suc $ ᵇ⇒≡ m'≡ᵇn'

  ≡⇒ᵇ :  m ≡ n →  Tt (m ≡ᵇ n)
  ≡⇒ᵇ {0} {0} _ =  _
  ≡⇒ᵇ {suc m'} {suc n'} refl =  ≡⇒ᵇ {m'} {n'} refl

  -- Reflexivity of ≡ᵇ

  ≡ᵇ-refl :  (n ≡ᵇ n) ≡ tt
  ≡ᵇ-refl {n} =  Tt⇒≡tt $ ≡⇒ᵇ {n} refl

  -- Use ≢ to reduce ≡ᵇ

  ≢-≡ᵇ-ff :  m ≢ n →  (m ≡ᵇ n) ≡ ff
  ≢-≡ᵇ-ff m≢n =  ¬Tt⇒≡ff $ m≢n ∘ ᵇ⇒≡

  -- Conversion between <ᵇ and <

  ᵇ⇒< :  Tt (m <ᵇ n) →  m < n
  ᵇ⇒< {0} {suc _} _ =  0<suc
  ᵇ⇒< {suc m'} {suc n'} m'<ᵇn' =  suc<suc $ ᵇ⇒< m'<ᵇn'

  <⇒ᵇ :  m < n →  Tt (m <ᵇ n)
  <⇒ᵇ 0<suc =  _
  <⇒ᵇ (suc<suc m'<n'@?<?) =  <⇒ᵇ m'<n'

  -- Irreflexivity of <ᵇ

  <ᵇ-irrefl :  (n <ᵇ n) ≡ ff
  <ᵇ-irrefl {n} =  ¬Tt⇒≡ff (<-irrefl ∘ ᵇ⇒< {n})

  -- Conversion between ≤ᵇ and ≤

  ᵇ⇒≤ :  Tt (m ≤ᵇ n) →  m ≤ n
  ᵇ⇒≤ {0} _ =  0≤
  ᵇ⇒≤ {suc m} m≤n =  ᵇ⇒< m≤n

  ≤⇒ᵇ :  m ≤ n →  Tt (m ≤ᵇ n)
  ≤⇒ᵇ 0≤ =  _
  ≤⇒ᵇ m'<n@?<? =  <⇒ᵇ m'<n

  -- Reflexivity of ≤ᵇ

  ≤ᵇ-refl :  (n ≤ᵇ n) ≡ tt
  ≤ᵇ-refl {n} =  Tt⇒≡tt $ ≤⇒ᵇ {n} ≤-refl

--------------------------------------------------------------------------------
-- ≡?, ≤?, <? : Order decision

infix 4 _≡?_ _≤?_ _<?_

-- Defined directly without abstract for better normalization
_≡?_ :  Dec² {A = ℕ} _≡_
0 ≡? 0 =  yes refl
0 ≡? suc _ =  no $ λ ()
suc _ ≡? 0 =  no $ λ ()
suc m ≡? suc n  with m ≡? n
... | yes refl =  yes refl
... | no m≢n =  no λ{ refl → m≢n refl }

abstract

  -- Reflexivity of ≡?

  ≡?-refl :  (n ≡? n) ≡ yes refl
  ≡?-refl {n = 0} =  refl
  ≡?-refl {n = suc n}  rewrite ≡?-refl {n = n} =  refl

_≤?_ :  Dec² _≤_
_≤?_ _ _ =  dec-Tt ᵇ⇒≤ ≤⇒ᵇ

_<?_ :  Dec² _<_
_<?_ _ _ =  dec-Tt ᵇ⇒< <⇒ᵇ

--------------------------------------------------------------------------------
-- + :  Addition

open import Agda.Builtin.Nat public using (_+_)

abstract

  -- Clearing the right-hand side of +

  +-0 :  n + 0 ≡ n
  +-0 {0} =  refl
  +-0 {suc n'} =  cong suc $ +-0 {n'}

  +-suc :  m + suc n ≡ suc (m + n)
  +-suc {0} =  refl
  +-suc {suc m'} =  cong suc $ +-suc {m'}

  -- + is commutative

  +-comm :  m + n ≡ n + m
  +-comm {_} {0} =  +-0
  +-comm {_} {suc n'} =  +-suc ◇ cong suc (+-comm {_} {n'})

  -- + is associative

  +-assocˡ :  (l + m) + n ≡ l + (m + n)
  +-assocˡ {0} =  refl
  +-assocˡ {suc l'} =  cong suc $ +-assocˡ {l'}

  +-assocʳ :  l + (m + n) ≡ (l + m) + n
  +-assocʳ {l} =  ◠ +-assocˡ {l}

  -- + is increasing

  +-incrˡ :  ∀{m n} →  n ≤ m + n
  +-incrˡ {0} =  ≤-refl
  +-incrˡ {suc m'} =  ≤-trans (+-incrˡ {m'}) suc-incr

  -- + is monotone

  +-monoˡ :  l ≤ m →  l + n ≤ m + n
  +-monoˡ 0≤ =  +-incrˡ
  +-monoˡ (suc≤suc l'≤m') =  suc≤suc $ +-monoˡ l'≤m'

  +-monoʳ :  ∀{l m n} →  m ≤ n →  l + m ≤ l + n
  +-monoʳ {l} {m} {n}  rewrite +-comm {l} {m} | +-comm {l} {n} =  +-monoˡ

  +-mono :  k ≤ l →  m ≤ n →  k + m ≤ l + n
  +-mono k≤l m≤n =  ≤-trans (+-monoˡ k≤l) (+-monoʳ m≤n)

  -- + is strictly monotone

  +-smonoˡ :  l < m →  l + n < m + n
  +-smonoˡ =  +-monoˡ

  +-smonoʳ :  ∀{l m n} →  m < n →  l + m < l + n
  +-smonoʳ {l} {m} {n}  rewrite +-comm {l} {m} | +-comm {l} {n} =  +-smonoˡ

  +-smono :  k < l →  m < n →  k + m < l + n
  +-smono k<l m<n =  <-trans (+-smonoˡ k<l) (+-smonoʳ m<n)

  -- + is injective

  +-injˡ :  ∀{l m n} →  m + l ≡ n + l →  m ≡ n
  +-injˡ {_} {m} {n} m+l≡n+l  with m <≡> n
  ... | inj₀ m<n =  absurd $ ≡⇒¬< m+l≡n+l (+-smonoˡ m<n)
  ... | inj₁₀ m≡n =  m≡n
  ... | inj₁₁ m>n =  absurd $ ≡⇒¬< (◠ m+l≡n+l) (+-smonoˡ m>n)

  +-injʳ :  l + m ≡ l + n →  m ≡ n
  +-injʳ {l} {m} {n}  rewrite +-comm {l} {m} | +-comm {l} {n} =  +-injˡ

--------------------------------------------------------------------------------
-- * :  Multiplication

open import Agda.Builtin.Nat public using (_*_)

abstract

  -- Clearing the right-hand side of *

  *-0 :  n * 0 ≡ 0
  *-0 {0} =  refl
  *-0 {suc n'} =  *-0 {n'}

  *-suc :  m * suc n ≡ m + m * n
  *-suc {0} =  refl
  *-suc {suc m'} {n} =  cong (suc n +_) (*-suc {m'}) ◇ cong suc $
    +-assocʳ {n} ◇ cong (_+ m' * n) (+-comm {n}) ◇ +-assocˡ {m'}

  -- * is commutative

  *-comm :  m * n ≡ n * m
  *-comm {m} {0} =  *-0 {m}
  *-comm {m} {suc n'} =  *-suc {m} ◇ cong (m +_) (*-comm {_} {n'})

  -- * is distributive over +

  *-+-distrˡ :  (l + m) * n ≡ l * n + m * n
  *-+-distrˡ {0} =  refl
  *-+-distrˡ {suc l'} {_} {n} =  cong (n +_) (*-+-distrˡ {l'}) ◇ +-assocʳ {n}

  *-+-distrʳ :  l * (m + n) ≡ l * m + l * n
  *-+-distrʳ {l} {m} {n} =  *-comm {l} ◇ *-+-distrˡ {m} ◇
    cong₂ _+_ (*-comm {m}) (*-comm {n})

  -- * is associative

  *-assocˡ :  (l * m) * n ≡ l * (m * n)
  *-assocˡ {0} =  refl
  *-assocˡ {suc l'} {m} {n} =  *-+-distrˡ {m} ◇ cong (m * n +_) $ *-assocˡ {l'}

  *-assocʳ :  l * (m * n) ≡ (l * m) * n
  *-assocʳ {l} =  ◠ *-assocˡ {l}

  -- * is unital with 1

  *-1ˡ :  1 * n ≡ n
  *-1ˡ =  +-0

  *-1ʳ :  n * 1 ≡ n
  *-1ʳ {n} =  *-comm {n} ◇ *-1ˡ

  -- * is monotone

  *-monoˡ :  l ≤ m →  l * n ≤ m * n
  *-monoˡ 0≤ =  0≤
  *-monoˡ (suc≤suc l'≤m') =  +-monoʳ $ *-monoˡ l'≤m'

  *-monoʳ :  ∀{l m n} →  m ≤ n →  l * m ≤ l * n
  *-monoʳ {l} {m} {n}  rewrite *-comm {l} {m} | *-comm {l} {n} =  *-monoˡ

  *-mono :  k ≤ l →  m ≤ n →  k * m ≤ l * n
  *-mono {l = l} k≤l m≤n =  ≤-trans (*-monoˡ k≤l) (*-monoʳ {l} m≤n)

  -- * is strictly monotone when one argument is positive

  *-smonoˡ :  l < m →  l * suc n < m * suc n
  *-smonoˡ sl≤m =  ≤-trans (suc≤suc +-incrˡ) (*-monoˡ sl≤m)

  *-smonoʳ :  ∀{l m n} →  m < n →  suc l * m < suc l * n
  *-smonoʳ {l} {m} {n}  rewrite *-comm {suc l} {m} | *-comm {suc l} {n}
    =  *-smonoˡ

  -- * with a positive argument is injective

  *-injˡ :  ∀{l m n} →  m * suc l ≡ n * suc l →  m ≡ n
  *-injˡ {_} {m} {n} m*sl≡n*sl  with m <≡> n
  ... | inj₀ m<n =  absurd $ ≡⇒¬< m*sl≡n*sl (*-smonoˡ m<n)
  ... | inj₁₀ m≡n =  m≡n
  ... | inj₁₁ m>n =  absurd $ ≡⇒¬< (◠ m*sl≡n*sl) (*-smonoˡ m>n)

  *-injʳ :  suc l * m ≡ suc l * n →  m ≡ n
  *-injʳ {l} {m} {n}  rewrite *-comm {suc l} {m} | *-comm {suc l} {n} =  *-injˡ

--------------------------------------------------------------------------------
-- ∸ :  Truncated subtraction

open import Agda.Builtin.Nat public using () renaming (_-_ to _∸_)

--------------------------------------------------------------------------------
-- ⊔ :  Maximum

_⊔_ :  ℕ → ℕ →  ℕ
0 ⊔ n =  n
m ⊔ 0 =  m
suc m ⊔ suc n =  suc (m ⊔ n)

abstract

  -- Clearing ⊔ 0

  ⊔-0 :  n ⊔ 0 ≡ n
  ⊔-0 {0} =  refl
  ⊔-0 {suc _} =  refl

  -- ⊔ is the lub of m and n

  ⊔-introˡ :  m ≤ m ⊔ n
  ⊔-introˡ {0} =  0≤
  ⊔-introˡ {suc _} {0} =  ≤-refl
  ⊔-introˡ {suc _} {suc _} =  suc≤suc ⊔-introˡ

  ⊔-introʳ :  m ≤ n ⊔ m
  ⊔-introʳ {_} {0} =  ≤-refl
  ⊔-introʳ {0} {suc _} =  0≤
  ⊔-introʳ {suc m'} {suc n'} =  suc≤suc $ ⊔-introʳ {m'} {n'}

  ⊔-elim :  ∀{l m n} →  l ≤ n →  m ≤ n →  l ⊔ m ≤ n
  ⊔-elim {0} _ m≤n =  m≤n
  ⊔-elim {suc _} {0} l≤n _ =  l≤n
  ⊔-elim (suc≤suc l'≤n') (suc≤suc m'≤n') =  suc≤suc $ ⊔-elim l'≤n' m'≤n'

  -- ⊔ is commutative and associative

  ⊔-comm :  m ⊔ n ≡ n ⊔ m
  ⊔-comm {0} {_} =  ◠ ⊔-0
  ⊔-comm {_} {0} =  ⊔-0
  ⊔-comm {suc m'} {suc _} =  cong suc (⊔-comm {m'})

  ⊔-assocˡ :  (l ⊔ m) ⊔ n ≡ l ⊔ (m ⊔ n)
  ⊔-assocˡ {0} =  refl
  ⊔-assocˡ {suc _} {0} =  refl
  ⊔-assocˡ {suc _} {suc _} {0} =  refl
  ⊔-assocˡ {suc l'} {suc _} {suc _} =  cong suc (⊔-assocˡ {l'})

  ⊔-assocʳ :  l ⊔ (m ⊔ n) ≡ (l ⊔ m) ⊔ n
  ⊔-assocʳ {l} =  ◠ ⊔-assocˡ {l}

  -- Utility

  ⊔≤-introˡ :  l ⊔ m ≤ n →  l ≤ n
  ⊔≤-introˡ l⊔m≤n =  ≤-trans ⊔-introˡ l⊔m≤n

  ⊔≤-introʳ :  l ⊔ m ≤ n →  m ≤ n
  ⊔≤-introʳ {l} l⊔m≤n =  ≤-trans (⊔-introʳ {_} {l}) l⊔m≤n

  -- Reduce ⊔

  ⊔-≤ :  m ≤ n →  m ⊔ n ≡ n
  ⊔-≤ 0≤ =  refl
  ⊔-≤ (suc≤suc m'≤n') =  cong suc $ ⊔-≤ m'≤n'

  ⊔-≥ :  m ≥ n →  m ⊔ n ≡ m
  ⊔-≥ {m} m≥n =  ⊔-comm {m} ◇ ⊔-≤ m≥n

  ⊔-same :  n ⊔ n ≡ n
  ⊔-same =  ⊔-≥ ≤-refl

  -- Reduce suc _ ⊔ _

  suc⊔-< :  m < n →  suc m ⊔ n ≡ n
  suc⊔-< =  ⊔-≤

  suc⊔-≥ :  m ≥ n →  suc m ⊔ n ≡ suc m
  suc⊔-≥ m≥n =  ⊔-≥ $ ≤-trans m≥n suc-incr

  suc⊔-same :  suc n ⊔ n ≡ suc n
  suc⊔-same =  suc⊔-≥ ≤-refl
