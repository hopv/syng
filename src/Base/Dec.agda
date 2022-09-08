--------------------------------------------------------------------------------
-- Decision
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Dec where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.Func using (_$_)
open import Base.Few using (¬_; ⇒¬¬; absurd)
open import Base.Eq using (_≡_; _≢_; refl; _≡˙_)
open import Base.Prod using (_×_; _,_; -,_)
open import Base.Sum using (_⊎_; ĩ₀_; ĩ₁_; ⊎-case)

private variable
  ł ł' ł'' :  Level
  A B :  Set ł

--------------------------------------------------------------------------------
-- Decision on a proposition (or a type)

data  Dec (A : Set ł) :  Set ł  where
  yes :  A →  Dec A
  no :  ¬ A →  Dec A

-- Decision on a one-argument predicate

Dec¹ :  ∀{A : Set ł} →  (A → Set ł') →  Set (ł ⊔ᴸ ł')
Dec¹ F =  ∀ a →  Dec (F a)

-- Decision on a two-argument predicate

Dec² :  ∀{A : Set ł} {B : Set ł'} →  (A → B → Set ł'') →  Set (ł ⊔ᴸ ł' ⊔ᴸ ł'')
Dec² F =  ∀ a b →  Dec (F a b)

abstract

  -- Derive Dec on ¬

  infix 3 ¬?_
  ¬?_ :  Dec A →  Dec (¬ A)
  ¬? yes a =  no $ ⇒¬¬ a
  ¬? no ¬a =  yes ¬a

  -- Derive Dec on ×

  infixr 1 _×?_
  _×?_ :  Dec A →  Dec B →  Dec (A × B)
  yes a ×? yes b =  yes (a , b)
  no ¬a ×? _ =  no λ (a , _) → ¬a a
  _ ×? no ¬b =  no λ (-, b) → ¬b b

  -- Derive Dec on ⊎

  infixr 0 _⊎?_
  _⊎?_ :  Dec A →  Dec B →  Dec (A ⊎ B)
  yes a ⊎? _ =  yes $ ĩ₀ a
  _ ⊎? yes b =  yes $ ĩ₁ b
  no ¬a ⊎? no ¬b =  no $ ⊎-case ¬a ¬b

--------------------------------------------------------------------------------
-- ≡Dec :  Equality decision

record  ≡Dec (A : Set ł) :  Set ł  where
  constructor ≡dec
  infix 4 _≡?_
  field
    _≡?_ :  Dec² {A = A} _≡_
    ≡?-refl :  ∀{a} →  (a ≡? a) ≡ yes refl
open ≡Dec {{…}} public

private variable
  I :  Set ł
  A˙ :  I →  Set ł
  f g :  ∀ i →  A˙ i
  a b :  A
  i j :  I

--------------------------------------------------------------------------------
-- upd˙ :  Update a map at an index

upd˙ :  {{≡Dec I}} →  ∀(i : I) →  A˙ i →  (∀ j →  A˙ j) →  (∀ j →  A˙ j)
upd˙ i a f j  with j ≡? i
… | no _ =  f j
… | yes refl =  a

abstract

  -- Congruence on upd˙

  upd˙-cong :  {{_ : ≡Dec I}} →  f ≡˙ g →  upd˙ {I = I} i a f  ≡˙  upd˙ i a g
  upd˙-cong {i = i} f≡g j  with j ≡? i
  … | yes refl =  refl
  … | no _ =  f≡g j

  -- Self upd˙

  upd˙-self :  {{_ : ≡Dec I}} →  upd˙ {I = I} i (f i) f  ≡˙  f
  upd˙-self {i = i} j  with j ≡? i
  … | yes refl =  refl
  … | no _ =  refl

  -- Double upd˙

  upd˙-2 :  {{_ : ≡Dec I}} →  upd˙ {I = I} i a (upd˙ i b f)  ≡˙  upd˙ i a f
  upd˙-2 {i = i} j  with j ≡? i
  … | yes refl =  refl
  … | no j≢i  with j ≡? i
  …   | yes refl =  absurd $ j≢i refl
  …   | no _ =  refl

  -- Swap upd˙ on different indices

  upd˙-swap :  {{_ : ≡Dec I}} →  i ≢ j →
    upd˙ {I = I} i a (upd˙ j b f) ≡˙ upd˙ j b (upd˙ i a f)
  upd˙-swap {i = i} {j} i≢j k  with k ≡? i
  … | yes refl  with k ≡? j
  …   | yes refl =  absurd $ i≢j refl
  …   | no _  rewrite ≡?-refl {a = k} =  refl
  upd˙-swap {i = i} {j} _ k | no k≢i  with k ≡? j
  …   | yes refl  with k ≡? i
  …     | yes refl =  absurd $ k≢i refl
  …     | no _ =  refl
  upd˙-swap {i = i} {j} _ k | no k≢i | no _  with k ≡? i
  …     | yes refl =  absurd $ k≢i refl
  …     | no _ =  refl
