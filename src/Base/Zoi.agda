--------------------------------------------------------------------------------
-- Zoi (zero, one, or infinity) number
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Zoi where

open import Base.Level using (Level)
open import Base.Func using (id)
open import Base.Few using (⊤; ⊥; ¬_)
open import Base.Eq using (_≡_; refl; ◠_; _≡˙_; refl˙)
open import Base.Dec using (Dec; yes; no; ≡Dec; _≟_; ≟-refl; upd˙)
open import Base.Prod using (∑-syntax; π₀; π₁; _,_)

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

  -- ✓ᶻ is preserved by removal w.r.t. +ᶻ

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
  Aᶻ A'ᶻ Bᶻ B'ᶻ Cᶻ :  A → Zoi

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

-- ✔ᶻ :  Set validity

infix 4 ✔ᶻ_
✔ᶻ_ :  ∀{A : Set ł} →  (A → Zoi) →  Set ł
✔ᶻ Aᶻ =  ∀ a →  ✓ᶻ (Aᶻ a)

-- ⊆ᶻ :  Set inclusion

infix 4 _⊆ᶻ_
_⊆ᶻ_ :  ∀{A : Set ł} →  (A → Zoi) →  (A → Zoi) →  Set ł
Aᶻ ⊆ᶻ Bᶻ =  ∀ a →  Aᶻ a ≤ᶻ Bᶻ a

abstract

  -- ⊎ᶻ and ≡˙

  ⊎ᶻ-cong :  Aᶻ ≡˙ A'ᶻ →  Bᶻ ≡˙ B'ᶻ →  Aᶻ ⊎ᶻ Bᶻ ≡˙ A'ᶻ ⊎ᶻ B'ᶻ
  ⊎ᶻ-cong A≡A' C≡C' a  rewrite A≡A' a | C≡C' a =  refl

  ⊎ᶻ-congˡ :  Aᶻ ≡˙ A'ᶻ →  Aᶻ ⊎ᶻ Bᶻ ≡˙ A'ᶻ ⊎ᶻ Bᶻ
  ⊎ᶻ-congˡ A≡A' =  ⊎ᶻ-cong A≡A' refl˙

  ⊎ᶻ-congʳ :  Bᶻ ≡˙ B'ᶻ →  Aᶻ ⊎ᶻ Bᶻ ≡˙ Aᶻ ⊎ᶻ B'ᶻ
  ⊎ᶻ-congʳ {Aᶻ = Aᶻ} =  ⊎ᶻ-cong {Aᶻ = Aᶻ} refl˙

  -- Aᶻ ⊎ᶻ ∅ᶻ equals Aᶻ

  ⊎ᶻ-∅ᶻ :  Aᶻ ⊎ᶻ ∅ᶻ ≡˙ Aᶻ
  ⊎ᶻ-∅ᶻ {Aᶻ = Aᶻ} a =  +ᶻ-0ᶻ {Aᶻ a}

  -- ⊎ᶻ is commutative

  ⊎ᶻ-comm :  Aᶻ ⊎ᶻ Bᶻ ≡˙ Bᶻ ⊎ᶻ Aᶻ
  ⊎ᶻ-comm {Aᶻ = Aᶻ} a =  +ᶻ-comm {Aᶻ a}

  -- ⊎ᶻ is associative

  ⊎ᶻ-assocˡ :  (Aᶻ ⊎ᶻ Bᶻ) ⊎ᶻ Cᶻ ≡˙ Aᶻ ⊎ᶻ (Bᶻ ⊎ᶻ Cᶻ)
  ⊎ᶻ-assocˡ {Aᶻ = Aᶻ} a =  +ᶻ-assocˡ {Aᶻ a}

  ⊎ᶻ-assocʳ :  Aᶻ ⊎ᶻ (Bᶻ ⊎ᶻ Cᶻ) ≡˙ (Aᶻ ⊎ᶻ Bᶻ) ⊎ᶻ Cᶻ
  ⊎ᶻ-assocʳ {Aᶻ = Aᶻ} a =  +ᶻ-assocʳ {Aᶻ a}

  -- ✔ᶻ and ≡˙

  ✔ᶻ-resp :  Aᶻ ≡˙ Bᶻ →  ✔ᶻ Aᶻ →  ✔ᶻ Bᶻ
  ✔ᶻ-resp A≡B ✓A a  rewrite ◠ A≡B a =  ✓A a

  -- If Aᶻ ⊆ᶻ Bᶻ holds, then there exists Cᶻ s.t. Cᶻ ⊎ᶻ Aᶻ ≡˙ Bᶻ

  ⊆ᶻ⇒∑⊎ᶻ :  Aᶻ ⊆ᶻ Bᶻ →  ∑ Cᶻ , Cᶻ ⊎ᶻ Aᶻ ≡˙ Bᶻ
  ⊆ᶻ⇒∑⊎ᶻ A⊆B .π₀ a =  ≤ᶻ⇒∑+ᶻ (A⊆B a) .π₀
  ⊆ᶻ⇒∑⊎ᶻ A⊆B .π₁ a =  ≤ᶻ⇒∑+ᶻ (A⊆B a) .π₁

  -- ^ᶻ a ⊎ᶻ ^ᶻ a is invalid

  ^ᶻ-no2 :  ∀{{_ : ≡Dec A}} {a : A} →  ¬ ✔ᶻ ^ᶻ a ⊎ᶻ ^ᶻ a
  ^ᶻ-no2 {a = a} ✔^a⊎^a  with ✔^a⊎^a a
  … | ✓∞  rewrite ≟-refl {a = a} =  ✓∞
