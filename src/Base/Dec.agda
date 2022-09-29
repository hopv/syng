--------------------------------------------------------------------------------
-- Decision
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Dec where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.Func using (_$_; _›_; it)
open import Base.Few using (⟨2⟩; 0₂; 1₂; ⊤; ⊥; ¬_; ⇒¬¬; absurd)
open import Base.Eq using (_≡_; _≢_; refl; _≡˙_; _◇˙_; Uip; eq≡; const⇒Uip)

private variable
  ł ł' ł'' :  Level
  A B :  Set ł

--------------------------------------------------------------------------------
-- Dec :  Decision on a proposition

data  Dec (A : Set ł) :  Set ł  where
  yes :  A →  Dec A
  no :  ¬ A →  Dec A

-- Get Dec A from an instance

dec :  ∀(A : Set ł) →  {{Dec A}} →  Dec A
dec _ {{a?}} =  a?

-- Yes :  The decision is yes

Yes :  Dec A →  Set₀
Yes (yes _) =  ⊤
Yes (no _) =  ⊥

instance

  -- Dec on ⟨2⟩, ⊤ and ⊥

  ⟨2⟩-Dec :  Dec $ ⟨2⟩ {ł}
  ⟨2⟩-Dec =  yes 0₂

  ⊤-Dec :  Dec $ ⊤ {ł}
  ⊤-Dec =  yes _

  ⊥-Dec :  Dec $ ⊥ {ł}
  ⊥-Dec =  no absurd

  -- Derive Dec on →

  →-Dec :  {{Dec A}} →  {{Dec B}} →  Dec (A → B)
  →-Dec {{_}} {{yes b}} =  yes λ _ → b
  →-Dec {{no ¬a}} =  yes λ a → absurd $ ¬a a
  →-Dec {{yes a}} {{no ¬b}} =  no λ a⇒b → absurd $ ¬b $ a⇒b a

--------------------------------------------------------------------------------
-- Inhabitance

-- Inh A :  A is inhabited

record  Inh (A : Set ł) :  Set ł  where
  field
    -- auto :  Arbitrarily taken inhabitant of A
    auto :  A

open Inh {{…}} public

instance

  -- Derive Inh from Dec

  Dec-Inh :  {{a? : Dec A}} →  {Yes a?} →  Inh A
  Dec-Inh {{yes a}} .auto =  a

--------------------------------------------------------------------------------
-- ≡Dec :  Equality decision

record  ≡Dec (A : Set ł) :  Set ł  where
  infix 4 _≟_
  field
    -- Equality decision for A
    _≟_ :  ∀(a b : A) →  Dec $ a ≡ b

open ≡Dec {{…}} public

instance

  -- Get Dec $ a ≡ b out of ≡Dec

  ≡-Dec :  {{≡Dec A}} →  {a b : A} →  Dec $ a ≡ b
  ≡-Dec =  _ ≟ _

  -- Equality decision for ⟨2⟩, ⊤ and ⊥

  ⟨2⟩-≡Dec :  ≡Dec {ł} ⟨2⟩
  ⟨2⟩-≡Dec ._≟_ 0₂ 0₂ =  yes refl
  ⟨2⟩-≡Dec ._≟_ 1₂ 1₂ =  yes refl
  ⟨2⟩-≡Dec ._≟_ 0₂ 1₂ =  no λ ()
  ⟨2⟩-≡Dec ._≟_ 1₂ 0₂ =  no λ ()

  ⊤-≡Dec :  ≡Dec {ł} ⊤
  ⊤-≡Dec ._≟_ _ _ =  yes refl

  ⊥-≡Dec :  ≡Dec {ł} ⊥
  ⊥-≡Dec ._≟_ ()

-- Derive ≡Dec by a injection

inj⇒≡Dec :  {{≡Dec B}} →
  ∀{f : A → B} (f-inj : ∀{a a'} → f a ≡ f a' → a ≡ a') →  ≡Dec A
inj⇒≡Dec {f = f} f-inj ._≟_ a a'  with f a ≟ f a'
… | yes fa≡fa' =  yes $ f-inj fa≡fa'
… | no fa≢fa' =  no λ{ refl → fa≢fa' refl }

instance abstract

  -- ≡Dec implies Uip

  ≡Dec⇒Uip :  {{≡Dec A}} →  Uip A
  ≡Dec⇒Uip {A = A} =  const⇒Uip k-const
   where
    k :  ∀{a b : A} →  a ≡ b →  a ≡ b
    k {a} {b} eq  with a ≟ b
    … | yes eq' =  eq'
    … | no a≢b =  absurd $ a≢b eq
    k-const :  ∀{a b : A} (eq eq' : a ≡ b) →  k eq ≡ k eq'
    k-const {a} {b} eq _  with a ≟ b
    … | yes _ =  refl
    … | no a≢b  with a≢b eq
    …   | ()

abstract

  -- On the yes result of ≟

  ≡-≟ :  ∀{{_ : ≡Dec A}} {a b : A} (eq : a ≡ b) →  (a ≟ b) ≡ yes eq
  ≡-≟ {a = a} {b} eq  with a ≟ b
  … | yes eq'  rewrite eq≡ eq' eq =  refl
  … | no a≢b  with a≢b eq
  …   | ()

  ≟-refl :  ∀{{_ : ≡Dec A}} {a : A} →  (a ≟ a) ≡ yes refl
  ≟-refl =  ≡-≟ refl

private variable
  I :  Set ł
  A˙ :  I →  Set ł
  f g :  ∀ i →  A˙ i
  a b a' b' :  A
  i j :  I

--------------------------------------------------------------------------------
-- upd˙ :  Update a map at an index

upd˙ :  {{≡Dec I}} →  ∀(i : I) →  A˙ i →  (∀ j →  A˙ j) →  ∀ j →  A˙ j
upd˙ i a f j  with j ≟ i
… | no _ =  f j
… | yes refl =  a

abstract

  -- Congruence on upd˙

  upd˙-cong :  {{_ : ≡Dec I}} →  f ≡˙ g →  upd˙ {I = I} i a f  ≡˙  upd˙ i a g
  upd˙-cong {i = i} f≡g j  with j ≟ i
  … | yes refl =  refl
  … | no _ =  f≡g j

  -- Self upd˙

  upd˙-self :  {{_ : ≡Dec I}} →  upd˙ {I = I} i (f i) f  ≡˙  f
  upd˙-self {i = i} j  with j ≟ i
  … | yes refl =  refl
  … | no _ =  refl

  -- Double upd˙

  upd˙-2 :  {{_ : ≡Dec I}} →  upd˙ {I = I} i a (upd˙ i b f)  ≡˙  upd˙ i a f
  upd˙-2 {i = i} j  with j ≟ i
  … | yes refl =  refl
  … | no j≢i  with j ≟ i
  …   | yes refl =  absurd $ j≢i refl
  …   | no _ =  refl

  -- Swap upd˙ on different indices

  upd˙-swap :  {{_ : ≡Dec I}} →  i ≢ j →
    upd˙ {I = I} i a (upd˙ j b f) ≡˙ upd˙ j b (upd˙ i a f)
  upd˙-swap {i = i} {j} i≢j k  with k ≟ i
  … | yes refl  with k ≟ j
  …   | yes refl =  absurd $ i≢j refl
  …   | no _  rewrite ≟-refl {a = k} =  refl
  upd˙-swap {i = i} {j} _ k | no k≢i  with k ≟ j
  …   | yes refl  with k ≟ i
  …     | yes refl =  absurd $ k≢i refl
  …     | no _ =  refl
  upd˙-swap {i = i} {j} _ k | no k≢i | no _  with k ≟ i
  …     | yes refl =  absurd $ k≢i refl
  …     | no _ =  refl

--------------------------------------------------------------------------------
-- upd˙² :  Update a map at two indices

upd˙² :  {{≡Dec I}} →  ∀(i : I) →  A˙ i →  ∀(j : I) →  A˙ j →
  (∀ k →  A˙ k) →  ∀ k →  A˙ k
upd˙² i a j b  =  upd˙ i a › upd˙ j b

abstract

  -- Self upd˙²

  upd˙²-self :  {{_ : ≡Dec I}} →
    i ≢ j →  upd˙² {I = I} i (f i) j (f j) f  ≡˙  f
  upd˙²-self {i = i} {j = j} i≢j k  with k ≟ j
  … | no _  with k ≟ i
  …   | yes refl =  refl
  …   | no _ =  refl
  upd˙²-self {i = i} {j = j} i≢j k | yes refl  with k ≟ i
  …   | yes refl =  absurd $ i≢j refl
  …   | no _ =  refl

  -- Double upd˙²

  upd˙²-2 :  {{_ : ≡Dec I}} →
    i ≢ j →  upd˙² {I = I} i a j b (upd˙² i a' j b' f)  ≡˙  upd˙² i a j b f
  upd˙²-2 i≢j =  upd˙-cong (upd˙-swap i≢j) ◇˙ upd˙-2 ◇˙ upd˙-cong upd˙-2
