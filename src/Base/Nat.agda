--------------------------------------------------------------------------------
-- Natural number
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Nat where

open import Base.Level using (Level)
open import Base.Func using (_$_; _∘_)
open import Base.Few using (⊤; ⊥; ¬_; absurd)
open import Base.Eq using (_≡_; _≢_; refl; ◠_; _◇_; cong; cong₂; _≡˙_)
open import Base.Dec using (Dec; yes; no; ≡Dec; _≟_; upd˙)
open import Base.Acc using (Acc; acc; acc-sub)
open import Base.Prod using (∑-syntax; _,_; -,_; _,-; π₀; π₁)
open import Base.Sum using (_⨿_; ĩ₀_; ĩ₁_)

--------------------------------------------------------------------------------
-- ℕ :  Natural number

-- Import and re-export
open import Agda.Builtin.Nat public using () renaming (
  -- Natural number
  -- ℕ :  Set₀
  Nat to ℕ;
  -- Successor
  -- š_ :  ℕ →  ℕ
  suc to infix 10 ṡ_)

private variable
  k l m n :  ℕ
  ł :  Level
  A :  Set ł
  A˙ :  ℕ → Set ł
  F :  ∀ i →  A˙ i →  Set ł
  f g :  ∀ i →  A˙ i
  i :  ℕ
  a :  A

abstract

  -- ṡ is injective

  ṡ-inj :  ṡ m ≡ ṡ n →  m ≡ n
  ṡ-inj refl =  refl

instance

  -- ℕ is inhabited

  ℕ-Dec :  Dec ℕ
  ℕ-Dec =  yes 0

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

-- 0<ṡ :  0 < ṡ n
pattern 0<ṡ =  ṡ≤ṡ 0≤
-- ṡ<ṡ :  m < n →  ṡ m < ṡ n
pattern ṡ<ṡ m<n =  ṡ≤ṡ m<n
-- ?<? :  m < ṡ n
pattern ?<? =  ṡ≤ṡ _
-- <ᵈ-ṡrefl :  m <ᵈ ṡ m
pattern <ᵈ-ṡrefl =  ≤ᵈ-refl
-- <ᵈṡ :  m <ᵈ n →  m <ᵈ ṡ n
pattern <ᵈṡ m<n =  ≤ᵈṡ m<n

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

  <⇒¬≥ :  m < n →  ¬ m ≥ n
  <⇒¬≥ m<n m≥n =  ≤⇒¬> m≥n m<n

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

  _<≡>_ :  ∀ m n →  m < n  ⨿  m ≡ n  ⨿  m > n
  0 <≡> (ṡ _) =  ĩ₀ 0<ṡ
  0 <≡> 0 =  ĩ₁ ĩ₀ refl
  ṡ _ <≡> 0 =  ĩ₁ ĩ₁ 0<ṡ
  ṡ m' <≡> ṡ n'  with m' <≡> n'
  … | ĩ₀ m'<n' =  ĩ₀ ṡ<ṡ m'<n'
  … | ĩ₁ ĩ₀ refl =  ĩ₁ ĩ₀ refl
  … | ĩ₁ ĩ₁ m'>n' =  ĩ₁ ĩ₁ ṡ<ṡ m'>n'

  -- Get ≤ or >

  _≤>_ :  ∀ m n →  m ≤ n  ⨿  m > n
  m ≤> n  with m <≡> n
  … | ĩ₀ m<n =  ĩ₀ <⇒≤ m<n
  … | ĩ₁ ĩ₀ refl =  ĩ₀ ≤-refl
  … | ĩ₁ ĩ₁ m>n =  ĩ₁ m>n

  -- Get < or ≥

  _<≥_ :  ∀ m n →  m < n  ⨿  m ≥ n
  m <≥ n  with n ≤> m
  … | ĩ₀ n≤m =  ĩ₁ n≤m
  … | ĩ₁ n>m =  ĩ₀ n>m

  -- Turn ≤ into < or ≡

  ≤⇒<≡ :  m ≤ n →  m < n  ⨿  m ≡ n
  ≤⇒<≡ {m} {n} m≤n  with m <≥ n
  … | ĩ₀ m<n =  ĩ₀ m<n
  … | ĩ₁ m≥n =  ĩ₁ ≤-antisym m≤n m≥n

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

  -- <ᵈ/< is well-founded

  <ᵈ-wf :  Acc _<ᵈ_ n
  <ᵈ-wf =  acc go
   where
    go :  m <ᵈ n →  Acc _<ᵈ_ m
    go <ᵈ-ṡrefl =  <ᵈ-wf
    go (<ᵈṡ m'<n') =  go m'<n'

  <-wf :  Acc _<_ n
  <-wf =  acc-sub ≤⇒≤ᵈ <ᵈ-wf

--------------------------------------------------------------------------------
-- Equality decision for ℕ

instance

  ℕ-≡Dec :  ≡Dec ℕ
  ℕ-≡Dec ._≟_ =  _≟'_
   where
    infix 4 _≟'_
    _≟'_ :  ∀ a b →  Dec $ a ≡ b
    0 ≟' 0 =  yes refl
    0 ≟' ṡ _ =  no λ ()
    ṡ _ ≟' 0 =  no λ ()
    ṡ m' ≟' ṡ n'  with m' ≟' n'
    … | yes refl =  yes refl
    … | no m'≢n' =  no λ{ refl → m'≢n' refl }

--------------------------------------------------------------------------------
-- Order decision

instance

  ≤-Dec :  Dec $ m ≤ n
  ≤-Dec {ṡ m} {ṡ n}  with ≤-Dec {m} {n}
  … | yes m≤n =  yes $ ṡ≤ṡ m≤n
  … | no ¬m≤n =  no λ{ (ṡ≤ṡ m≤n) → ¬m≤n m≤n }
  ≤-Dec {0} =  yes 0≤
  ≤-Dec {ṡ _} {0} =  no λ ()

--------------------------------------------------------------------------------
-- >0 :  Positivity

infix 4 _>0
_>0 :  ℕ →  Set₀
ṡ _ >0 =  ⊤
0 >0 =  ⊥

--------------------------------------------------------------------------------
-- + :  Addition

open import Agda.Builtin.Nat public using (
  -- infixl 6 _+_
  -- _+_ :  ℕ →  ℕ →  ℕ
  _+_)

-- + ? preserves >0

+?->0 :  m >0 →  m + n >0
+?->0 {m = ṡ _} =  _

abstract

  -- Clear the right-hand side of +

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
  … | ĩ₀ m<n =  absurd $ ≡⇒¬< m+l≡n+l (+-smonoˡ m<n)
  … | ĩ₁ ĩ₀ m≡n =  m≡n
  … | ĩ₁ ĩ₁ m>n =  absurd $ ≡⇒¬< (◠ m+l≡n+l) (+-smonoˡ m>n)

  +-injʳ :  l + m ≡ l + n →  m ≡ n
  +-injʳ {l} {m} {n}  rewrite +-comm {l} {m} | +-comm {l} {n} =  +-injˡ

--------------------------------------------------------------------------------
-- * :  Multiplication

open import Agda.Builtin.Nat public using (
  -- infixl 7 _*_
  -- _*_ :  ℕ →  ℕ →  ℕ
  _*_)

-- * preserves >0

*->0 :  m >0 →  n >0 →  m * n >0
*->0 {m = ṡ _} {n = ṡ _} =  _

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

  -- * is unital with the unit 1

  *-1ˡ :  1 * n ≡ n
  *-1ˡ =  +-0

  *-1ʳ :  n * 1 ≡ n
  *-1ʳ {n} =  *-comm {n} ◇ *-1ˡ

  -- Simplify * with 2

  *-2ˡ :  2 * n ≡ n + n
  *-2ˡ {n} =  cong (n +_) *-1ˡ

  *-2ʳ :  n * 2 ≡ n + n
  *-2ʳ {n} =  *-comm {n} ◇ *-2ˡ {n}

  -- * is monotone

  *-monoˡ :  l ≤ m →  l * n ≤ m * n
  *-monoˡ 0≤ =  0≤
  *-monoˡ (ṡ≤ṡ l'≤m') =  +-monoʳ $ *-monoˡ l'≤m'

  *-monoʳ :  ∀{l m n} →  m ≤ n →  l * m ≤ l * n
  *-monoʳ {l} {m} {n}  rewrite *-comm {l} {m} | *-comm {l} {n} =  *-monoˡ

  *-mono :  k ≤ l →  m ≤ n →  k * m ≤ l * n
  *-mono {l = l} k≤l m≤n =  ≤-trans (*-monoˡ k≤l) (*-monoʳ {l} m≤n)

  -- * is strictly monotone when one argument is positive

  *-smonoˡ :  l >0 →  m < n →  m * l < n * l
  *-smonoˡ {l = ṡ _} _ ṡm≤n =  ≤-trans (ṡ≤ṡ +-incrˡ) (*-monoˡ ṡm≤n)

  *-smonoʳ :  l >0 →  m < n →  l * m < l * n
  *-smonoʳ {l} {m} {n}  rewrite *-comm {l} {m} | *-comm {l} {n} =  *-smonoˡ

  -- Divide both sides of ≤ by a positive number

  *-monoˡ-inv :  l >0 →  m * l ≤ n * l →  m ≤ n
  *-monoˡ-inv {_} {m} {n} l>0 ml≤nl  with m ≤> n
  … | ĩ₀ m≤n =  m≤n
  … | ĩ₁ m>n =  absurd $ ≤⇒¬> ml≤nl $ *-smonoˡ l>0 m>n

  *-monoʳ-inv :  l >0 →  l * m ≤ l * n →  m ≤ n
  *-monoʳ-inv {l} {m} {n}  rewrite *-comm {l} {m} | *-comm {l} {n} =
    *-monoˡ-inv

  -- Divide both sides of <

  *-smonoˡ-inv :  ∀{l m n} →  m * l < n * l →  m < n
  *-smonoˡ-inv {_} {m} {n} ml<nl  with m <≥ n
  … | ĩ₀ m<n =  m<n
  … | ĩ₁ m≥n =  absurd $ <⇒¬≥ ml<nl $ *-monoˡ m≥n

  *-smonoʳ-inv :  l * m < l * n →  m < n
  *-smonoʳ-inv {l} {m} {n}  rewrite *-comm {l} {m} | *-comm {l} {n} =
    *-smonoˡ-inv

  -- * with a positive argument is injective

  *-injˡ :  l >0 →  m * l ≡ n * l →  m ≡ n
  *-injˡ {m = m} {n} l>0 m*l≡n*l  with m <≡> n
  … | ĩ₀ m<n =  absurd $ ≡⇒¬< m*l≡n*l (*-smonoˡ l>0 m<n)
  … | ĩ₁ ĩ₀ m≡n =  m≡n
  … | ĩ₁ ĩ₁ m>n =  absurd $ ≡⇒¬< (◠ m*l≡n*l) (*-smonoˡ l>0 m>n)

  *-injʳ :  l >0 →  l * m ≡ l * n →  m ≡ n
  *-injʳ {l} {m} {n}  rewrite *-comm {l} {m} | *-comm {l} {n} =  *-injˡ

--------------------------------------------------------------------------------
-- ∸ :  Truncated subtraction

open import Agda.Builtin.Nat public using () renaming (
  -- infixl 6 _-_
  -- _-_ :  ℕ →  ℕ →  ℕ
  _-_ to _∸_)

abstract

  -- m plus n ∸ m equals n

  +ˡ-∸ :  m + n ∸ m ≡ n
  +ˡ-∸ {0} =  refl
  +ˡ-∸ {ṡ m'} =  +ˡ-∸ {m'}

  +ʳ-∸ :  m + n ∸ n ≡ m
  +ʳ-∸ {m} {n} rewrite +-comm {m} {n} =  +ˡ-∸ {n}

  -- m plus n ∸ m equals n if m ≤ n

  ≤⇒∸-+ˡ :  m ≤ n →  m + (n ∸ m) ≡ n
  ≤⇒∸-+ˡ 0≤ =  refl
  ≤⇒∸-+ˡ (ṡ≤ṡ m'≤n') =  cong ṡ_ $ ≤⇒∸-+ˡ m'≤n'

  ≤⇒∸-+ʳ :  m ≤ n →  n ∸ m + m ≡ n
  ≤⇒∸-+ʳ {m} m≤n =  +-comm {n = m} ◇ ≤⇒∸-+ˡ m≤n

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

--------------------------------------------------------------------------------
-- ∀≥˙ n F f :  F i (f i) holds for every i ≥ n

∀≥˙ :  ℕ →  (∀ i → A˙ i → Set ł) →  (∀ i → A˙ i) →  Set ł
∀≥˙ n F f =  ∀ i →  i ≥ n →  F i (f i)

abstract

  -- ∀≥˙ respects ≡˙

  ∀≥˙-resp :  f ≡˙ g →  ∀≥˙ n F f →  ∀≥˙ n F g
  ∀≥˙-resp f≡g ∀≥f i  rewrite ◠ f≡g i =  ∀≥f i

  -- ∀≥˙ holds if there is no exception

  ∀⇒∀≥˙ :  (∀ i → F i (f i)) →  ∀≥˙ n F f
  ∀⇒∀≥˙ Ffi i _ =  Ffi i

  -- ∀≥˙ n is preserved by upd˙ if the added element satisfies the condition

  ∀≥˙-upd˙-sat :  F i a →  ∀≥˙ n F f →  ∀≥˙ n F (upd˙ i a f)
  ∀≥˙-upd˙-sat {i = i} Fia ∀≥f j j≥n  with j ≟ i
  … | no _ =  ∀≥f j j≥n
  … | yes refl =  Fia

  -- ∀≥˙ is preserved by upd˙ i, updating the bound by ṡ i ⊔ -

  ∀≥˙-upd˙ :  ∀≥˙ n F f →  ∀≥˙ (ṡ i ⊔ n) F (upd˙ i a f)
  ∀≥˙-upd˙ {n = n} {i = i} ∀≥f j ṡi⊔n≥j  with j ≟ i
  … | no _ =  ∀≥f j $ ⊔≤-introʳ {ṡ _} ṡi⊔n≥j
  … | yes refl =  absurd $ <-irrefl $ ⊔≤-introˡ {m = n} ṡi⊔n≥j

  -- ∀≥˙ is preserved by upd˙ at the bound, updating the bound by ṡ

  ∀≥˙-upd˙-ṡ : ∀≥˙ n F f →  ∀≥˙ (ṡ n) F (upd˙ n a f)
  ∀≥˙-upd˙-ṡ {n} {F = F} {a = a} ∀≥f  with ∀≥˙-upd˙ {F = F} {a = a} ∀≥f
  … | ∀≥updf  rewrite ṡ⊔-same {n} =  ∀≥updf

--------------------------------------------------------------------------------
-- Cofin˙ F f :  F i (f i) holds for all but finitely many i's

Cofin˙ :  (∀ i → A˙ i → Set ł) →  (∀ i → A˙ i) →  Set ł
Cofin˙ F f =  ∑ n ,  ∀≥˙ n F f

abstract

  -- Cofin˙ respects ≡˙

  Cofin˙-resp :  f ≡˙ g →  Cofin˙ F f →  Cofin˙ F g
  Cofin˙-resp {F = F} f≡g (n , ∀≥f) =  n , ∀≥˙-resp {F = F} f≡g ∀≥f

  -- Cofin˙ holds if there is no exception

  ∀⇒Cofin˙ :  (∀ i → F i (f i)) →  Cofin˙ F f
  ∀⇒Cofin˙ {F = F} Ffi =  0 , ∀⇒∀≥˙ {F = F} Ffi

  -- Cofin˙ is preserved by upd˙

  Cofin˙-upd˙ :  Cofin˙ F f →  Cofin˙ F (upd˙ i a f)
  Cofin˙-upd˙ {F = F} (-, ∀≥f) =  -, ∀≥˙-upd˙ {F = F} ∀≥f

  -- If Cofin˙ F f holds, then there exists some i such that F i (f i) holds

  Cofin˙-∑ :  Cofin˙ F f →  ∑ i , F i (f i)
  Cofin˙-∑ (n , ∀≥f) =  n , ∀≥f n ≤-refl
