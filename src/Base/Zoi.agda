--------------------------------------------------------------------------------
-- Zoi (zero, one, or infinity) number
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Zoi where

open import Base.Level using (Level)
open import Base.Func using (id)
open import Base.Few using (⊤; ⊥; ¬_)
open import Base.Eq using (_≡_; refl; ◠_; _◇_; _≡˙_; refl˙)
open import Base.Dec using (Dec; yes; no; ≡Dec; _≟_; ≟-refl; upd˙)
open import Base.Prod using (∑-syntax; π₀; π₁; _,_)

--------------------------------------------------------------------------------
-- Zoi :  Zoi (zero, one, or infinity) number

data  Zoi :  Set₀  where
  0ᶻ 1ᶻ ∞ᶻ :  Zoi

private variable
  k l m n :  Zoi

-- ≤ᶻ :  Order of zois

infix 4 _≤ᶻ_
_≤ᶻ_ :  Zoi →  Zoi →  Set₀
0ᶻ ≤ᶻ _ =  ⊤
_ ≤ᶻ ∞ᶻ =  ⊤
1ᶻ ≤ᶻ 1ᶻ =  ⊤
_ ≤ᶻ _ =  ⊥

-- ✓ᶻ :  Validity of a zoi

infix 4 ✓ᶻ_
✓ᶻ_ :  Zoi →  Set₀
✓ᶻ a =  a ≤ᶻ 1ᶻ

-- +ᶻ :  Addition of zois

infixl 6 _+ᶻ_
_+ᶻ_ :  Zoi →  Zoi →  Zoi
0ᶻ +ᶻ n =  n
∞ᶻ +ᶻ n =  ∞ᶻ
n +ᶻ 0ᶻ =  n
_ +ᶻ _ =  ∞ᶻ

-- ∸ᶻ :  Truncated subtraction of zois

infixl 6 _∸ᶻ_
_∸ᶻ_ :  Zoi →  Zoi →  Zoi
m ∸ᶻ 0ᶻ =  m
m ∸ᶻ ∞ᶻ =  0ᶻ
0ᶻ ∸ᶻ n =  0ᶻ
1ᶻ ∸ᶻ 1ᶻ =  0ᶻ
∞ᶻ ∸ᶻ 1ᶻ =  ∞ᶻ

instance

  -- Zoi is inhabited

  Zoi-Dec :  Dec Zoi
  Zoi-Dec =  yes 0ᶻ

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

  -- ∞ᶻ is the maximum element w.r.t. ≤ᶻ

  ∞ᶻ-max :  n ≤ᶻ ∞ᶻ
  ∞ᶻ-max {0ᶻ} =  _
  ∞ᶻ-max {1ᶻ} =  _
  ∞ᶻ-max {∞ᶻ} =  _

  -- ≤ᶻ is reflexive, transitive, and antisymmetric

  ≤ᶻ-refl :  n ≤ᶻ n
  ≤ᶻ-refl {0ᶻ} =  _
  ≤ᶻ-refl {1ᶻ} =  _
  ≤ᶻ-refl {∞ᶻ} =  _

  ≤ᶻ-trans :  l ≤ᶻ m →  m ≤ᶻ n →  l ≤ᶻ n
  ≤ᶻ-trans {0ᶻ} _ _ =  _
  ≤ᶻ-trans {n = ∞ᶻ} _ _ =  ∞ᶻ-max
  ≤ᶻ-trans {1ᶻ} {1ᶻ} {1ᶻ} _ _ =  _
  ≤ᶻ-trans {1ᶻ} {0ᶻ} {0ᶻ} ()
  ≤ᶻ-trans {∞ᶻ} {0ᶻ} {0ᶻ} ()
  ≤ᶻ-trans {∞ᶻ} {0ᶻ} {1ᶻ} ()

  ≤ᶻ-antisym :  m ≤ᶻ n →  n ≤ᶻ m →  m ≡ n
  ≤ᶻ-antisym {0ᶻ} {0ᶻ} _ _ =  refl
  ≤ᶻ-antisym {1ᶻ} {1ᶻ} _ _ =  refl
  ≤ᶻ-antisym {∞ᶻ} {∞ᶻ} _ _ =  refl

  -- n +ᶻ 0ᶻ equals n

  +ᶻ-0 :  n +ᶻ 0ᶻ ≡ n
  +ᶻ-0 {0ᶻ} =  refl
  +ᶻ-0 {1ᶻ} =  refl
  +ᶻ-0 {∞ᶻ} =  refl

  -- n +ᶻ ∞ᶻ equals ∞ᶻ

  +ᶻ-∞ :  n +ᶻ ∞ᶻ ≡ ∞ᶻ
  +ᶻ-∞ {0ᶻ} =  refl
  +ᶻ-∞ {1ᶻ} =  refl
  +ᶻ-∞ {∞ᶻ} =  refl

  -- +ᶻ is commutative

  +ᶻ-comm :  m +ᶻ n ≡ n +ᶻ m
  +ᶻ-comm {m} {0ᶻ}  rewrite +ᶻ-0 {m} =  refl
  +ᶻ-comm {0ᶻ} {n}  rewrite +ᶻ-0 {n} =  refl
  +ᶻ-comm {m} {∞ᶻ}  rewrite +ᶻ-∞ {m} =  refl
  +ᶻ-comm {∞ᶻ} {n}  rewrite +ᶻ-∞ {n} =  refl
  +ᶻ-comm {1ᶻ} {1ᶻ} =  refl

  -- +ᶻ is associative

  +ᶻ-assocʳ :  (l +ᶻ m) +ᶻ n ≡ l +ᶻ (m +ᶻ n)
  +ᶻ-assocʳ {0ᶻ} =  refl
  +ᶻ-assocʳ {∞ᶻ} =  refl
  +ᶻ-assocʳ {1ᶻ} {0ᶻ} =  refl
  +ᶻ-assocʳ {1ᶻ} {∞ᶻ} =  refl
  +ᶻ-assocʳ {1ᶻ} {1ᶻ} {0ᶻ} =  refl
  +ᶻ-assocʳ {1ᶻ} {1ᶻ} {∞ᶻ} =  refl
  +ᶻ-assocʳ {1ᶻ} {1ᶻ} {1ᶻ} =  refl

  +ᶻ-assocˡ :  l +ᶻ (m +ᶻ n) ≡ (l +ᶻ m) +ᶻ n
  +ᶻ-assocˡ {l} =  ◠ +ᶻ-assocʳ {l}

  -- ✓ᶻ is preserved by removal w.r.t. +ᶻ

  ✓ᶻ-rem :  ✓ᶻ m +ᶻ n →  ✓ᶻ n
  ✓ᶻ-rem {0ᶻ} =  id
  ✓ᶻ-rem {1ᶻ} {0ᶻ} =  _

  -- +ᶻ is monotone

  +ᶻ-monoˡ :  l ≤ᶻ m →  l +ᶻ n ≤ᶻ m +ᶻ n
  +ᶻ-monoˡ {_} {∞ᶻ} _ =  ∞ᶻ-max
  +ᶻ-monoˡ {_} {0ᶻ} {∞ᶻ} _ =  ∞ᶻ-max
  +ᶻ-monoˡ {_} {1ᶻ} {∞ᶻ} _ =  ∞ᶻ-max
  +ᶻ-monoˡ {_} {1ᶻ} {1ᶻ} _ =  ∞ᶻ-max
  +ᶻ-monoˡ {0ᶻ} {_} {0ᶻ} _ =  _
  +ᶻ-monoˡ {0ᶻ} {0ᶻ} {1ᶻ} _ =  _
  +ᶻ-monoˡ {1ᶻ} {1ᶻ} {0ᶻ} _ =  _

  +ᶻ-monoʳ :  l ≤ᶻ m →  n +ᶻ l ≤ᶻ n +ᶻ m
  +ᶻ-monoʳ {l} {m} {n}  rewrite +ᶻ-comm {n} {l} | +ᶻ-comm {n} {m} =  +ᶻ-monoˡ

  +ᶻ-mono :  k ≤ᶻ l →  m ≤ᶻ n →  k +ᶻ m ≤ᶻ l +ᶻ n
  +ᶻ-mono {l = l} k≤l m≤n =  ≤ᶻ-trans (+ᶻ-monoˡ k≤l) (+ᶻ-monoʳ {n = l} m≤n)

  -- m plus n ∸ᶻ m equals n if m ≤ᶻ n

  ≤ᶻ⇒∸-+ˡ :  m ≤ᶻ n →  m +ᶻ (n ∸ᶻ m) ≡ n
  ≤ᶻ⇒∸-+ˡ {0ᶻ} _ =  refl
  ≤ᶻ⇒∸-+ˡ {1ᶻ} {1ᶻ} _ =  refl
  ≤ᶻ⇒∸-+ˡ {1ᶻ} {∞ᶻ} _ =  refl
  ≤ᶻ⇒∸-+ˡ {∞ᶻ} {∞ᶻ} _ =  refl

  ≤ᶻ⇒∸-+ʳ :  m ≤ᶻ n →  (n ∸ᶻ m) +ᶻ m ≡ n
  ≤ᶻ⇒∸-+ʳ {m} m≤n =  +ᶻ-comm {n = m} ◇ ≤ᶻ⇒∸-+ˡ m≤n

--------------------------------------------------------------------------------
-- Set, as a map to Zoi

private variable
  ł :  Level
  A :  Set ł
  Aᶻ A'ᶻ Bᶻ B'ᶻ Cᶻ :  A → Zoi

-- ✔ᶻ :  Set validity

infix 4 ✔ᶻ_
✔ᶻ_ :  ∀{A : Set ł} →  (A → Zoi) →  Set ł
✔ᶻ Aᶻ =  ∀ a →  ✓ᶻ (Aᶻ a)

-- ⊆ᶻ :  Set inclusion

infix 4 _⊆ᶻ_
_⊆ᶻ_ :  ∀{A : Set ł} →  (A → Zoi) →  (A → Zoi) →  Set ł
Aᶻ ⊆ᶻ Bᶻ =  ∀ a →  Aᶻ a ≤ᶻ Bᶻ a

-- ∅ᶻ, ⊤ᶻ :  Empty and universal sets

∅ᶻ ⊤ᶻ :  A → Zoi
∅ᶻ _ =  0ᶻ
⊤ᶻ _ =  1ᶻ

-- ^ᶻ :  Singleton set

infix 8 ^ᶻ_
^ᶻ_ :  {{≡Dec A}} →  A →  (A → Zoi)
^ᶻ a =  upd˙ a 1ᶻ ∅ᶻ

-- ⊎ᶻ :  Set addition

infixl 6 _⊎ᶻ_
_⊎ᶻ_ :  (A → Zoi) →  (A → Zoi) →  (A → Zoi)
(Aᶻ ⊎ᶻ Bᶻ) a =  Aᶻ a +ᶻ Bᶻ a

-- ∖ᶻ :  Set difference

infixl 6 _∖ᶻ_
_∖ᶻ_ :  (A → Zoi) →  (A → Zoi) →  (A → Zoi)
(Aᶻ ∖ᶻ Bᶻ) a =  Aᶻ a ∸ᶻ Bᶻ a

abstract

  -- ✔ᶻ and ≡˙

  ✔ᶻ-resp :  Aᶻ ≡˙ Bᶻ →  ✔ᶻ Aᶻ →  ✔ᶻ Bᶻ
  ✔ᶻ-resp A≡B ✓A a  rewrite ◠ A≡B a =  ✓A a

  -- ⊎ᶻ and ≡˙

  ⊎ᶻ-cong :  Aᶻ ≡˙ A'ᶻ →  Bᶻ ≡˙ B'ᶻ →  Aᶻ ⊎ᶻ Bᶻ ≡˙ A'ᶻ ⊎ᶻ B'ᶻ
  ⊎ᶻ-cong A≡A' C≡C' a  rewrite A≡A' a | C≡C' a =  refl

  ⊎ᶻ-congˡ :  Aᶻ ≡˙ A'ᶻ →  Aᶻ ⊎ᶻ Bᶻ ≡˙ A'ᶻ ⊎ᶻ Bᶻ
  ⊎ᶻ-congˡ A≡A' =  ⊎ᶻ-cong A≡A' refl˙

  ⊎ᶻ-congʳ :  Bᶻ ≡˙ B'ᶻ →  Aᶻ ⊎ᶻ Bᶻ ≡˙ Aᶻ ⊎ᶻ B'ᶻ
  ⊎ᶻ-congʳ {Aᶻ = Aᶻ} =  ⊎ᶻ-cong {Aᶻ = Aᶻ} refl˙

  -- Aᶻ ⊎ᶻ ∅ᶻ equals Aᶻ

  ⊎ᶻ-∅ᶻ :  Aᶻ ⊎ᶻ ∅ᶻ ≡˙ Aᶻ
  ⊎ᶻ-∅ᶻ {Aᶻ = Aᶻ} a =  +ᶻ-0 {Aᶻ a}

  -- ⊎ᶻ is commutative

  ⊎ᶻ-comm :  Aᶻ ⊎ᶻ Bᶻ ≡˙ Bᶻ ⊎ᶻ Aᶻ
  ⊎ᶻ-comm {Aᶻ = Aᶻ} a =  +ᶻ-comm {Aᶻ a}

  -- ⊎ᶻ is associative

  ⊎ᶻ-assocʳ :  (Aᶻ ⊎ᶻ Bᶻ) ⊎ᶻ Cᶻ ≡˙ Aᶻ ⊎ᶻ (Bᶻ ⊎ᶻ Cᶻ)
  ⊎ᶻ-assocʳ {Aᶻ = Aᶻ} a =  +ᶻ-assocʳ {Aᶻ a}

  ⊎ᶻ-assocˡ :  Aᶻ ⊎ᶻ (Bᶻ ⊎ᶻ Cᶻ) ≡˙ (Aᶻ ⊎ᶻ Bᶻ) ⊎ᶻ Cᶻ
  ⊎ᶻ-assocˡ {Aᶻ = Aᶻ} a =  +ᶻ-assocˡ {Aᶻ a}

  -- ^ᶻ a ⊎ᶻ ^ᶻ a is invalid

  ^ᶻ-no2 :  ∀{{_ : ≡Dec A}} {a : A} →  ¬ ✔ᶻ ^ᶻ a ⊎ᶻ ^ᶻ a
  ^ᶻ-no2 {a = a} ✔^a⊎^a  with ✔^a⊎^a a
  … | ✓∞  rewrite ≟-refl {a = a} =  ✓∞

  -- If Aᶻ ⊆ᶻ Bᶻ holds, then Aᶻ ⊎ᶻ (Bᶻ ∖ᶻ Aᶻ) equals Bᶻ

  ⊆ᶻ⇒∖-⊎ˡ :  Aᶻ ⊆ᶻ Bᶻ →  Aᶻ ⊎ᶻ (Bᶻ ∖ᶻ Aᶻ) ≡˙ Bᶻ
  ⊆ᶻ⇒∖-⊎ˡ A⊆B a =  ≤ᶻ⇒∸-+ˡ (A⊆B a)

  ⊆ᶻ⇒∖-⊎ʳ :  Aᶻ ⊆ᶻ Bᶻ →  (Bᶻ ∖ᶻ Aᶻ) ⊎ᶻ Aᶻ ≡˙ Bᶻ
  ⊆ᶻ⇒∖-⊎ʳ A⊆B a =  ≤ᶻ⇒∸-+ʳ (A⊆B a)

  -- ^ᶻ a is valid

  ^ᶻ-✔ :  ∀{{_ : ≡Dec A}} {a : A} →  ✔ᶻ ^ᶻ a
  ^ᶻ-✔ {a = a} b  with b ≟ a
  … | yes refl =  _
  … | no _ =  _
