--------------------------------------------------------------------------------
-- Zoi (zero, one, or infinity) number
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Zoi where

open import Base.Level using (Level)
open import Base.Func using (id)
open import Base.Few using (⊤; ⊥)
open import Base.Eq using (_≡_; refl; ◠_; _≡˙_; refl˙)
open import Base.Prod using (∑-syntax; π₀; π₁; _,_)
open import Base.Dec using (yes; no; ≡Dec; _≟_)

--------------------------------------------------------------------------------
-- Zoi :  Zoi (zero, one, or infinity) number

data  Zoi :  Set₀  where
  0ᶻ 1ᶻ ∞ᶻ :  Zoi

private variable
  l m n :  Zoi

-- +ᶻ :  Addition of zois

infixl 6 _+ᶻ_
_+ᶻ_ :  Zoi →  Zoi →  Zoi
0ᶻ +ᶻ n =  n
∞ᶻ +ᶻ n =  ∞ᶻ
n +ᶻ 0ᶻ =  n
_ +ᶻ _ =  ∞ᶻ

-- ✓ᶻ :  Validity of a zoi

infix 4 ✓ᶻ_
✓ᶻ_ :  Zoi →  Set₀
✓ᶻ ∞ᶻ =  ⊥
✓ᶻ _ =  ⊤

-- ≤ᶻ :  Order of zois

infix 4 _≤ᶻ_
_≤ᶻ_ :  Zoi →  Zoi →  Set₀
0ᶻ ≤ᶻ _ =  ⊤
_ ≤ᶻ ∞ᶻ =  ⊤
1ᶻ ≤ᶻ 1ᶻ =  ⊤
_ ≤ᶻ _ =  ⊥

instance

  -- Equality decision for Zoi

  Zoi-≡Dec :  ≡Dec Zoi
  Zoi-≡Dec ._≟_ 0ᶻ 0ᶻ =  yes refl
  Zoi-≡Dec ._≟_ 1ᶻ 1ᶻ =  yes refl
  Zoi-≡Dec ._≟_ ∞ᶻ ∞ᶻ =  yes refl
  Zoi-≡Dec ._≟_ 0ᶻ 1ᶻ =  no λ ()
  Zoi-≡Dec ._≟_ 0ᶻ ∞ᶻ =  no λ ()
  Zoi-≡Dec ._≟_ 1ᶻ 0ᶻ =  no λ ()
  Zoi-≡Dec ._≟_ 1ᶻ ∞ᶻ =  no λ ()
  Zoi-≡Dec ._≟_ ∞ᶻ 0ᶻ =  no λ ()
  Zoi-≡Dec ._≟_ ∞ᶻ 1ᶻ =  no λ ()

abstract

  -- n +ᶻ 0ᶻ equals n

  +ᶻ-0ᶻ :  n +ᶻ 0ᶻ ≡ n
  +ᶻ-0ᶻ {0ᶻ} =  refl
  +ᶻ-0ᶻ {1ᶻ} =  refl
  +ᶻ-0ᶻ {∞ᶻ} =  refl

  -- +ᶻ is commutative

  +ᶻ-comm :  m +ᶻ n ≡ n +ᶻ m
  +ᶻ-comm {0ᶻ} {0ᶻ} =  refl
  +ᶻ-comm {0ᶻ} {1ᶻ} =  refl
  +ᶻ-comm {0ᶻ} {∞ᶻ} =  refl
  +ᶻ-comm {1ᶻ} {0ᶻ} =  refl
  +ᶻ-comm {1ᶻ} {1ᶻ} =  refl
  +ᶻ-comm {1ᶻ} {∞ᶻ} =  refl
  +ᶻ-comm {∞ᶻ} {0ᶻ} =  refl
  +ᶻ-comm {∞ᶻ} {1ᶻ} =  refl
  +ᶻ-comm {∞ᶻ} {∞ᶻ} =  refl

  -- +ᶻ is associative

  +ᶻ-assocˡ :  (l +ᶻ m) +ᶻ n ≡ l +ᶻ (m +ᶻ n)
  +ᶻ-assocˡ {0ᶻ} =  refl
  +ᶻ-assocˡ {∞ᶻ} =  refl
  +ᶻ-assocˡ {1ᶻ} {0ᶻ} =  refl
  +ᶻ-assocˡ {1ᶻ} {∞ᶻ} =  refl
  +ᶻ-assocˡ {1ᶻ} {1ᶻ} {0ᶻ} =  refl
  +ᶻ-assocˡ {1ᶻ} {1ᶻ} {∞ᶻ} =  refl
  +ᶻ-assocˡ {1ᶻ} {1ᶻ} {1ᶻ} =  refl

  +ᶻ-assocʳ :  l +ᶻ (m +ᶻ n) ≡ (l +ᶻ m) +ᶻ n
  +ᶻ-assocʳ {l} =  ◠ +ᶻ-assocˡ {l}

  -- ✓ᶻ holds after removal with respect to +ᶻ

  ✓ᶻ-rem :  ✓ᶻ m +ᶻ n →  ✓ᶻ n
  ✓ᶻ-rem {0ᶻ} =  id
  ✓ᶻ-rem {1ᶻ} {0ᶻ} =  _

  -- If m ≤ᶻ n holds, then there exists l s.t. l +ᶻ m ≡ n

  ≤ᶻ⇒∑+ᶻ :  m ≤ᶻ n →  ∑ l , l +ᶻ m ≡ n
  ≤ᶻ⇒∑+ᶻ {0ᶻ} {n} _ =  n , +ᶻ-0ᶻ
  ≤ᶻ⇒∑+ᶻ {_} {∞ᶻ} _ =  ∞ᶻ , refl
  ≤ᶻ⇒∑+ᶻ {1ᶻ} {1ᶻ} _ =  0ᶻ , refl

--------------------------------------------------------------------------------
-- Set, as a map to Zoi

private variable
  ł :  Level
  A :  Set ł
  l˙ m˙ m'˙ n˙ n'˙ :  A → Zoi

-- 0ᶻ˙, 1ᶻ˙ :  Empty and universal set

0ᶻ˙ 1ᶻ˙ :  A → Zoi
0ᶻ˙ _ =  0ᶻ
1ᶻ˙ _ =  1ᶻ

-- +ᶻ˙ :  Set addition

infixl 6 _+ᶻ˙_
_+ᶻ˙_ :  (A → Zoi) →  (A → Zoi) →  (A → Zoi)
(m˙ +ᶻ˙ n˙) a =  m˙ a +ᶻ n˙ a

-- ✓ᶻ˙ :  Set validity

infix 4 ✓ᶻ˙_
✓ᶻ˙_ :  ∀{A : Set ł} →  (A → Zoi) →  Set ł
✓ᶻ˙ n˙ =  ∀ a →  ✓ᶻ (n˙ a)

-- ≤ᶻ˙ :  Set inclusion

infix 4 _≤ᶻ˙_
_≤ᶻ˙_ :  ∀{A : Set ł} →  (A → Zoi) →  (A → Zoi) →  Set ł
m˙ ≤ᶻ˙ n˙ =  ∀ a →  m˙ a ≤ᶻ n˙ a

abstract

  -- +ᶻ˙ and ≡˙

  +ᶻ˙-cong :  m˙ ≡˙ m'˙ →  n˙ ≡˙ n'˙ →  m˙ +ᶻ˙ n˙ ≡˙ m'˙ +ᶻ˙ n'˙
  +ᶻ˙-cong m≡m' n≡n' a  rewrite m≡m' a | n≡n' a =  refl

  +ᶻ˙-congˡ :  m˙ ≡˙ m'˙ →  m˙ +ᶻ˙ n˙ ≡˙ m'˙ +ᶻ˙ n˙
  +ᶻ˙-congˡ m≡m' =  +ᶻ˙-cong m≡m' refl˙

  +ᶻ˙-congʳ :  n˙ ≡˙ n'˙ →  m˙ +ᶻ˙ n˙ ≡˙ m˙ +ᶻ˙ n'˙
  +ᶻ˙-congʳ {m˙ = m˙} =  +ᶻ˙-cong {m˙ = m˙} refl˙

  -- n˙ +ᶻ˙ 0ᶻ˙ equals n˙

  +ᶻ˙-0ᶻ˙ :  n˙ +ᶻ˙ 0ᶻ˙ ≡˙ n˙
  +ᶻ˙-0ᶻ˙ {n˙ = n˙} a =  +ᶻ-0ᶻ {n˙ a}

  -- +ᶻ˙ is commutative

  +ᶻ˙-comm :  m˙ +ᶻ˙ n˙ ≡˙ n˙ +ᶻ˙ m˙
  +ᶻ˙-comm {m˙ = m˙} a =  +ᶻ-comm {m˙ a}

  -- +ᶻ˙ is associative

  +ᶻ˙-assocˡ :  (l˙ +ᶻ˙ m˙) +ᶻ˙ n˙ ≡˙ l˙ +ᶻ˙ (m˙ +ᶻ˙ n˙)
  +ᶻ˙-assocˡ {l˙ = l˙} a =  +ᶻ-assocˡ {l˙ a}

  +ᶻ˙-assocʳ :  l˙ +ᶻ˙ (m˙ +ᶻ˙ n˙) ≡˙ (l˙ +ᶻ˙ m˙) +ᶻ˙ n˙
  +ᶻ˙-assocʳ {l˙ = l˙} a =  +ᶻ-assocʳ {l˙ a}

  -- ✓ᶻ˙ and ≡˙

  ✓ᶻ˙-resp :  m˙ ≡˙ n˙ →  ✓ᶻ˙ m˙ →  ✓ᶻ˙ n˙
  ✓ᶻ˙-resp m≡n ✓m a  rewrite ◠ m≡n a =  ✓m a

  -- If m˙ ≤ᶻ˙ n˙ holds, then there exists l˙ s.t. l˙ +ᶻ˙ m˙ ≡˙ n˙

  ≤ᶻ˙⇒∑+ᶻ˙ :  m˙ ≤ᶻ˙ n˙ →  ∑ l˙ , l˙ +ᶻ˙ m˙ ≡˙ n˙
  ≤ᶻ˙⇒∑+ᶻ˙ m≤n .π₀ a =  ≤ᶻ⇒∑+ᶻ (m≤n a) .π₀
  ≤ᶻ˙⇒∑+ᶻ˙ m≤n .π₁ a =  ≤ᶻ⇒∑+ᶻ (m≤n a) .π₁
