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
open import Base.Dec using (Dec²; yes; no; dec-Tt)

--------------------------------------------------------------------------------
-- ℕ :  Natural number

open import Agda.Builtin.Nat public
  using () renaming (suc to infix 10 ṡ_; Nat to ℕ)

private variable
  k l m n :  ℕ

--------------------------------------------------------------------------------
-- ≤, <, ≤ᵈ, <ᵈ :  Order

infix 4 _≤_ _<_ _≥_ _>_ _≤ᵈ_ _<ᵈ_ _≥ᵈ_ _>ᵈ_

-- ≤ :  Order, with induction on the left-hand side

data  _≤_ :  ℕ → ℕ → Set₀  where
  0≤ :  0 ≤ n
  ṡ≤ṡ :  m ≤ n →  ṡ m ≤ ṡ n

-- ≤ᵈ :  Order, with induction on difference

data  _≤ᵈ_ :  ℕ → ℕ → Set₀  where
  ≤ᵈ-refl :  n ≤ᵈ n
  ≤ᵈṡ :  m ≤ᵈ n →  m ≤ᵈ ṡ n

_<_ _≥_ _>_ _<ᵈ_ _≥ᵈ_ _>ᵈ_ :  ℕ → ℕ → Set₀
m < n =  ṡ m ≤ n
m ≥ n =  n ≤ m
m > n =  n < m
m <ᵈ n =  ṡ m ≤ᵈ n
m ≥ᵈ n =  n ≤ᵈ m
m >ᵈ n =  n <ᵈ m

pattern 0<ṡ =  ṡ≤ṡ 0≤
pattern ṡ<ṡ m<n =  ṡ≤ṡ m<n
pattern ?<? =  ṡ≤ṡ _

abstract

  -- ≤ is reflexive

  ≤-refl :  n ≤ n
  ≤-refl {0} =  0≤
  ≤-refl {ṡ _} =  ṡ≤ṡ ≤-refl

  -- < is irreflexive

  <-irrefl :  ¬ n < n
  <-irrefl (ṡ≤ṡ n'<n') =  <-irrefl n'<n'

  ≡⇒¬< :  m ≡ n →  ¬ m < n
  ≡⇒¬< refl =  <-irrefl

  -- ≤ is transitive

  ≤-trans :  l ≤ m →  m ≤ n →  l ≤ n
  ≤-trans 0≤ _ =  0≤
  ≤-trans (ṡ≤ṡ l≤m) (ṡ≤ṡ m≤n) =  ṡ≤ṡ $ ≤-trans l≤m m≤n

  -- Composing ≤ and <

  ≤-<-trans :  l ≤ m →  m < n →  l < n
  ≤-<-trans l≤m ṡm≤n =  ≤-trans (ṡ≤ṡ l≤m) ṡm≤n

  <-≤-trans :  l < m →  m ≤ n →  l < n
  <-≤-trans ṡl≤m m≤n =  ≤-trans ṡl≤m m≤n

  -- ṡ is increasing

  ṡ-sincr :  n < ṡ n
  ṡ-sincr =  ≤-refl

  ṡ-incr :  n ≤ ṡ n
  ṡ-incr {0} =  0≤
  ṡ-incr {ṡ _} =  ṡ≤ṡ ṡ-incr

  -- < into ≤

  <⇒≤ :  m < n →  m ≤ n
  <⇒≤ ṡm≤n =  ≤-trans ṡ-incr ṡm≤n

  -- < is transitive

  <-trans :  l < m →  m < n →  l < n
  <-trans l<m m<n =  <-≤-trans l<m (<⇒≤ m<n)

  -- ≤ is antisymmetric

  ≤-antisym :  m ≤ n →  n ≤ m →  m ≡ n
  ≤-antisym 0≤ 0≤ =  refl
  ≤-antisym (ṡ≤ṡ m'≤n') (ṡ≤ṡ n'≤m') =  cong ṡ_ $ ≤-antisym m'≤n' n'≤m'

  -- ≤ and > do not hold at the same time

  ≤⇒¬> :  m ≤ n →  ¬ m > n
  ≤⇒¬> (ṡ≤ṡ m'≤n') (ṡ<ṡ m'>n') =  ≤⇒¬> m'≤n' m'>n'

  -- < is asymmetric

  <-asym :  m < n →  ¬ m > n
  <-asym m<n =  ≤⇒¬> $ <⇒≤ m<n

  -- Invert ṡ≤/<ṡ

  ṡ≤ṡ⁻¹ :  ṡ m ≤ ṡ n →  m ≤ n
  ṡ≤ṡ⁻¹ (ṡ≤ṡ m≤n) =   m≤n

  ṡ<ṡ⁻¹ :  ṡ m < ṡ n →  m < n
  ṡ<ṡ⁻¹ (ṡ<ṡ m<n) =   m<n

  infix 4 _<≡>_ _≤>_ _<≥_

  -- Get <, ≡ or >

  _<≡>_ :  ∀ m n →  m < n  ⊎  m ≡ n  ⊎  m > n
  0 <≡> (ṡ _) =  inj₀ 0<ṡ
  0 <≡> 0 =  inj₁₀ refl
  ṡ _ <≡> 0 =  inj₁₁ 0<ṡ
  ṡ m' <≡> ṡ n'  with m' <≡> n'
  … | inj₀ m'<n' =  inj₀ $ ṡ<ṡ m'<n'
  … | inj₁₀ refl =  inj₁₀ refl
  … | inj₁₁ m'>n' =  inj₁₁ (ṡ<ṡ m'>n')

  -- Get ≤ or >

  _≤>_ :  ∀ m n →  m ≤ n  ⊎  m > n
  m ≤> n  with m <≡> n
  … | inj₀ m<n =  inj₀ $ <⇒≤ m<n
  … | inj₁₀ refl =  inj₀ ≤-refl
  … | inj₁₁ m>n =  inj₁ m>n

  -- Get < or ≥

  _<≥_ :  ∀ m n →  m < n  ⊎  m ≥ n
  m <≥ n  with n ≤> m
  … | inj₀ n≤m =  inj₁ n≤m
  … | inj₁ n>m =  inj₀ n>m

  -- Conversion between ≤ and ≤ᵈ

  0≤ᵈ :  0 ≤ᵈ n
  0≤ᵈ {n = 0} =  ≤ᵈ-refl
  0≤ᵈ {n = ṡ n'} =  ≤ᵈṡ $ 0≤ᵈ {n = n'}

  ṡ≤ᵈṡ :  m ≤ᵈ n →  ṡ m ≤ᵈ ṡ n
  ṡ≤ᵈṡ ≤ᵈ-refl =  ≤ᵈ-refl
  ṡ≤ᵈṡ (≤ᵈṡ m≤ᵈn') =  ≤ᵈṡ $ ṡ≤ᵈṡ m≤ᵈn'

  ≤⇒≤ᵈ :  m ≤ n →  m ≤ᵈ n
  ≤⇒≤ᵈ 0≤ =  0≤ᵈ
  ≤⇒≤ᵈ (ṡ≤ṡ m≤n) =  ṡ≤ᵈṡ $ ≤⇒≤ᵈ m≤n

  ≤ᵈ⇒≤ :  m ≤ᵈ n →  m ≤ n
  ≤ᵈ⇒≤ ≤ᵈ-refl =  ≤-refl
  ≤ᵈ⇒≤ (≤ᵈṡ m≤ᵈn') =  ≤-trans (≤ᵈ⇒≤ m≤ᵈn') ṡ-incr

--------------------------------------------------------------------------------
-- ≡ᵇ, ≤ᵇ, <ᵇ : Boolean order

open import Agda.Builtin.Nat public using () renaming (_==_ to _≡ᵇ_;
  _<_ to _<ᵇ_)

infix 4 _≤ᵇ_ _≥ᵇ_ _>ᵇ_
_≤ᵇ_ _≥ᵇ_ _>ᵇ_ :  ℕ → ℕ → Bool
0 ≤ᵇ n =  tt
ṡ m ≤ᵇ n =  m <ᵇ n
m ≥ᵇ n =  n ≤ᵇ m
m >ᵇ n =  n <ᵇ m

abstract

  -- Conversion between ≡ᵇ and ≡

  ᵇ⇒≡ :  Tt (m ≡ᵇ n) →  m ≡ n
  ᵇ⇒≡ {0} {0} _ =  refl
  ᵇ⇒≡ {ṡ m'} {ṡ n'} m'≡ᵇn' =  cong ṡ_ $ ᵇ⇒≡ m'≡ᵇn'

  ≡⇒ᵇ :  m ≡ n →  Tt (m ≡ᵇ n)
  ≡⇒ᵇ {0} {0} _ =  _
  ≡⇒ᵇ {ṡ m'} {ṡ n'} refl =  ≡⇒ᵇ {m'} {n'} refl

  -- Reflexivity of ≡ᵇ

  ≡ᵇ-refl :  (n ≡ᵇ n) ≡ tt
  ≡ᵇ-refl {n} =  Tt⇒≡tt $ ≡⇒ᵇ {n} refl

  -- Use ≢ to reduce ≡ᵇ

  ≢-≡ᵇ-ff :  m ≢ n →  (m ≡ᵇ n) ≡ ff
  ≢-≡ᵇ-ff m≢n =  ¬Tt⇒≡ff $ m≢n ∘ ᵇ⇒≡

  -- Conversion between <ᵇ and <

  ᵇ⇒< :  Tt (m <ᵇ n) →  m < n
  ᵇ⇒< {0} {ṡ _} _ =  0<ṡ
  ᵇ⇒< {ṡ m'} {ṡ n'} m'<ᵇn' =  ṡ<ṡ $ ᵇ⇒< m'<ᵇn'

  <⇒ᵇ :  m < n →  Tt (m <ᵇ n)
  <⇒ᵇ 0<ṡ =  _
  <⇒ᵇ (ṡ<ṡ m'<n'@?<?) =  <⇒ᵇ m'<n'

  -- Irreflexivity of <ᵇ

  <ᵇ-irrefl :  (n <ᵇ n) ≡ ff
  <ᵇ-irrefl {n} =  ¬Tt⇒≡ff (<-irrefl ∘ ᵇ⇒< {n})

  -- Conversion between ≤ᵇ and ≤

  ᵇ⇒≤ :  Tt (m ≤ᵇ n) →  m ≤ n
  ᵇ⇒≤ {0} _ =  0≤
  ᵇ⇒≤ {ṡ m} m≤n =  ᵇ⇒< m≤n

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
0 ≡? ṡ _ =  no λ ()
ṡ _ ≡? 0 =  no λ ()
ṡ m ≡? ṡ n  with m ≡? n
… | yes refl =  yes refl
… | no m≢n =  no λ{ refl → m≢n refl }

abstract

  -- Reflexivity of ≡?

  ≡?-refl :  (n ≡? n) ≡ yes refl
  ≡?-refl {n = 0} =  refl
  ≡?-refl {n = ṡ n}  rewrite ≡?-refl {n = n} =  refl

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
  +-0 {ṡ n'} =  cong ṡ_ $ +-0 {n'}

  +-ṡ :  m + ṡ n ≡ ṡ (m + n)
  +-ṡ {0} =  refl
  +-ṡ {ṡ m'} =  cong ṡ_ $ +-ṡ {m'}

  -- + is commutative

  +-comm :  m + n ≡ n + m
  +-comm {_} {0} =  +-0
  +-comm {_} {ṡ n'} =  +-ṡ ◇ cong ṡ_ (+-comm {_} {n'})

  -- + is associative

  +-assocˡ :  (l + m) + n ≡ l + (m + n)
  +-assocˡ {0} =  refl
  +-assocˡ {ṡ l'} =  cong ṡ_ $ +-assocˡ {l'}

  +-assocʳ :  l + (m + n) ≡ (l + m) + n
  +-assocʳ {l} =  ◠ +-assocˡ {l}

  -- + is increasing

  +-incrˡ :  ∀{m n} →  n ≤ m + n
  +-incrˡ {0} =  ≤-refl
  +-incrˡ {ṡ m'} =  ≤-trans (+-incrˡ {m'}) ṡ-incr

  -- + is monotone

  +-monoˡ :  l ≤ m →  l + n ≤ m + n
  +-monoˡ 0≤ =  +-incrˡ
  +-monoˡ (ṡ≤ṡ l'≤m') =  ṡ≤ṡ $ +-monoˡ l'≤m'

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
  … | inj₀ m<n =  absurd $ ≡⇒¬< m+l≡n+l (+-smonoˡ m<n)
  … | inj₁₀ m≡n =  m≡n
  … | inj₁₁ m>n =  absurd $ ≡⇒¬< (◠ m+l≡n+l) (+-smonoˡ m>n)

  +-injʳ :  l + m ≡ l + n →  m ≡ n
  +-injʳ {l} {m} {n}  rewrite +-comm {l} {m} | +-comm {l} {n} =  +-injˡ

--------------------------------------------------------------------------------
-- * :  Multiplication

open import Agda.Builtin.Nat public using (_*_)

abstract

  -- Clearing the right-hand side of *

  *-0 :  n * 0 ≡ 0
  *-0 {0} =  refl
  *-0 {ṡ n'} =  *-0 {n'}

  *-ṡ :  m * ṡ n ≡ m + m * n
  *-ṡ {0} =  refl
  *-ṡ {ṡ m'} {n} =  cong (ṡ n +_) (*-ṡ {m'}) ◇ cong ṡ_ $
    +-assocʳ {n} ◇ cong (_+ m' * n) (+-comm {n}) ◇ +-assocˡ {m'}

  -- * is commutative

  *-comm :  m * n ≡ n * m
  *-comm {m} {0} =  *-0 {m}
  *-comm {m} {ṡ n'} =  *-ṡ {m} ◇ cong (m +_) (*-comm {_} {n'})

  -- * is distributive over +

  *-+-distrˡ :  (l + m) * n ≡ l * n + m * n
  *-+-distrˡ {0} =  refl
  *-+-distrˡ {ṡ l'} {_} {n} =  cong (n +_) (*-+-distrˡ {l'}) ◇ +-assocʳ {n}

  *-+-distrʳ :  l * (m + n) ≡ l * m + l * n
  *-+-distrʳ {l} {m} {n} =  *-comm {l} ◇ *-+-distrˡ {m} ◇
    cong₂ _+_ (*-comm {m}) (*-comm {n})

  -- * is associative

  *-assocˡ :  (l * m) * n ≡ l * (m * n)
  *-assocˡ {0} =  refl
  *-assocˡ {ṡ l'} {m} {n} =  *-+-distrˡ {m} ◇ cong (m * n +_) $ *-assocˡ {l'}

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
  *-monoˡ (ṡ≤ṡ l'≤m') =  +-monoʳ $ *-monoˡ l'≤m'

  *-monoʳ :  ∀{l m n} →  m ≤ n →  l * m ≤ l * n
  *-monoʳ {l} {m} {n}  rewrite *-comm {l} {m} | *-comm {l} {n} =  *-monoˡ

  *-mono :  k ≤ l →  m ≤ n →  k * m ≤ l * n
  *-mono {l = l} k≤l m≤n =  ≤-trans (*-monoˡ k≤l) (*-monoʳ {l} m≤n)

  -- * is strictly monotone when one argument is positive

  *-smonoˡ :  l < m →  l * ṡ n < m * ṡ n
  *-smonoˡ ṡl≤m =  ≤-trans (ṡ≤ṡ +-incrˡ) (*-monoˡ ṡl≤m)

  *-smonoʳ :  ∀{l m n} →  m < n →  ṡ l * m < ṡ l * n
  *-smonoʳ {l} {m} {n}  rewrite *-comm {ṡ l} {m} | *-comm {ṡ l} {n} =  *-smonoˡ

  -- * with a positive argument is injective

  *-injˡ :  ∀{l m n} →  m * ṡ l ≡ n * ṡ l →  m ≡ n
  *-injˡ {_} {m} {n} m*ṡl≡n*ṡl  with m <≡> n
  … | inj₀ m<n =  absurd $ ≡⇒¬< m*ṡl≡n*ṡl (*-smonoˡ m<n)
  … | inj₁₀ m≡n =  m≡n
  … | inj₁₁ m>n =  absurd $ ≡⇒¬< (◠ m*ṡl≡n*ṡl) (*-smonoˡ m>n)

  *-injʳ :  ṡ l * m ≡ ṡ l * n →  m ≡ n
  *-injʳ {l} {m} {n}  rewrite *-comm {ṡ l} {m} | *-comm {ṡ l} {n} =  *-injˡ

--------------------------------------------------------------------------------
-- ∸ :  Truncated subtraction

open import Agda.Builtin.Nat public using () renaming (_-_ to _∸_)

--------------------------------------------------------------------------------
-- ⊔ :  Maximum

infixr 5 _⊔_
_⊔_ :  ℕ → ℕ →  ℕ
0 ⊔ n =  n
m ⊔ 0 =  m
ṡ m ⊔ ṡ n =  ṡ (m ⊔ n)

abstract

  -- Clearing ⊔ 0

  ⊔-0 :  n ⊔ 0 ≡ n
  ⊔-0 {0} =  refl
  ⊔-0 {ṡ _} =  refl

  -- ⊔ is the lub of m and n

  ⊔-introˡ :  m ≤ m ⊔ n
  ⊔-introˡ {0} =  0≤
  ⊔-introˡ {ṡ _} {0} =  ≤-refl
  ⊔-introˡ {ṡ _} {ṡ _} =  ṡ≤ṡ ⊔-introˡ

  ⊔-introʳ :  m ≤ n ⊔ m
  ⊔-introʳ {_} {0} =  ≤-refl
  ⊔-introʳ {0} {ṡ _} =  0≤
  ⊔-introʳ {ṡ m'} {ṡ n'} =  ṡ≤ṡ $ ⊔-introʳ {m'} {n'}

  ⊔-elim :  ∀{l m n} →  l ≤ n →  m ≤ n →  l ⊔ m ≤ n
  ⊔-elim {0} _ m≤n =  m≤n
  ⊔-elim {ṡ _} {0} l≤n _ =  l≤n
  ⊔-elim (ṡ≤ṡ l'≤n') (ṡ≤ṡ m'≤n') =  ṡ≤ṡ $ ⊔-elim l'≤n' m'≤n'

  -- ⊔ is commutative and associative

  ⊔-comm :  m ⊔ n ≡ n ⊔ m
  ⊔-comm {0} {_} =  ◠ ⊔-0
  ⊔-comm {_} {0} =  ⊔-0
  ⊔-comm {ṡ m'} {ṡ _} =  cong ṡ_ (⊔-comm {m'})

  ⊔-assocˡ :  (l ⊔ m) ⊔ n ≡ l ⊔ (m ⊔ n)
  ⊔-assocˡ {0} =  refl
  ⊔-assocˡ {ṡ _} {0} =  refl
  ⊔-assocˡ {ṡ _} {ṡ _} {0} =  refl
  ⊔-assocˡ {ṡ l'} {ṡ _} {ṡ _} =  cong ṡ_ (⊔-assocˡ {l'})

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
  ⊔-≤ (ṡ≤ṡ m'≤n') =  cong ṡ_ $ ⊔-≤ m'≤n'

  ⊔-≥ :  m ≥ n →  m ⊔ n ≡ m
  ⊔-≥ {m} m≥n =  ⊔-comm {m} ◇ ⊔-≤ m≥n

  ⊔-same :  n ⊔ n ≡ n
  ⊔-same =  ⊔-≥ ≤-refl

  -- Reduce ṡ _ ⊔ _

  ṡ⊔-< :  m < n →  ṡ m ⊔ n ≡ n
  ṡ⊔-< =  ⊔-≤

  ṡ⊔-≥ :  m ≥ n →  ṡ m ⊔ n ≡ ṡ m
  ṡ⊔-≥ m≥n =  ⊔-≥ $ ≤-trans m≥n ṡ-incr

  ṡ⊔-same :  ṡ n ⊔ n ≡ ṡ n
  ṡ⊔-same =  ṡ⊔-≥ ≤-refl
