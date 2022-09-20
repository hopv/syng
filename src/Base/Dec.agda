--------------------------------------------------------------------------------
-- Decision
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Dec where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.Func using (_$_; _›_; it)
open import Base.Few using (⟨2⟩; 0₂; 1₂; ⊤; ⊥; ¬_; ⇒¬¬; absurd)
open import Base.Eq using (_≡_; _≢_; refl; _≡˙_; _◇˙_)
open import Base.Prod using (_×_; _,_; -,_; _,-)
open import Base.Sum using (_⊎_; ĩ₀_; ĩ₁_; ⊎-case)
open import Base.Option using (¿_; ň; š_)

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

--  Get A from an instance yes-type decision

by-dec :  {{a? : Dec A}} →  {Yes a?} →  A
by-dec {{yes a}} =  a

instance

  -- Dec on ⊤ and ⊥

  ⊤-Dec :  Dec $ ⊤ {ł}
  ⊤-Dec =  yes _

  ⊥-Dec :  Dec $ ⊥ {ł}
  ⊥-Dec =  no absurd

  -- Derive Dec on →

  →-Dec :  {{Dec A}} →  {{Dec B}} →  Dec (A → B)
  →-Dec {{_}} {{yes b}} =  yes λ _ → b
  →-Dec {{no ¬a}} =  yes λ a → absurd $ ¬a a
  →-Dec {{yes a}} {{no ¬b}} =  no λ a⇒b → absurd $ ¬b $ a⇒b a

  -- Derive Dec on ×

  ×-Dec :  {{Dec A}} →  {{Dec B}} →  Dec $ A × B
  ×-Dec {{yes a}} {{yes b}} =  yes (a , b)
  ×-Dec {{no ¬a}} =  no λ (a ,-) → ¬a a
  ×-Dec {{_}} {{no ¬b}} =  no λ (-, b) → ¬b b

  -- Derive Dec on ⊎

  ⊎-Dec :  {{Dec A}} →  {{Dec B}} →  Dec $ A ⊎ B
  ⊎-Dec {{yes a}} =  yes $ ĩ₀ a
  ⊎-Dec {{_}} {{yes b}} =  yes $ ĩ₁ b
  ⊎-Dec {{no ¬a}} {{no ¬b}} =  no $ ⊎-case ¬a ¬b

--------------------------------------------------------------------------------
-- ≡Dec :  Equality decision

record  ≡Dec (A : Set ł) :  Set ł  where
  constructor ≡dec
  infix 4 _≡?_
  field
    -- Equality decision for A
    _≡?_ :  ∀(a b : A) →  Dec $ a ≡ b

    -- a ≡? a returns yes refl
    ---- It's trivial that it returns yes x for some x, but the fact that x is
    ---- refl cannot be derived from ≡?'s type only, under the --without-K flag
    ≡?-refl :  ∀{a} →  (a ≡? a) ≡ yes refl

open ≡Dec {{…}} public

instance

  ≡-Dec :  {{≡Dec A}} →  {a b : A} →  Dec $ a ≡ b
  ≡-Dec =  _ ≡? _

private variable
  I :  Set ł
  A˙ :  I →  Set ł
  f g :  ∀ i →  A˙ i
  a b a' b' :  A
  i j :  I

instance

  -- Equality decision for ⟨2⟩, ⊤ and ⊥

  ⟨2⟩-≡Dec :  ≡Dec {ł} ⟨2⟩
  ⟨2⟩-≡Dec ._≡?_ 0₂ 0₂ =  yes refl
  ⟨2⟩-≡Dec ._≡?_ 1₂ 1₂ =  yes refl
  ⟨2⟩-≡Dec ._≡?_ 0₂ 1₂ =  no λ ()
  ⟨2⟩-≡Dec ._≡?_ 1₂ 0₂ =  no λ ()
  ⟨2⟩-≡Dec .≡?-refl {0₂} =  refl
  ⟨2⟩-≡Dec .≡?-refl {1₂} =  refl

  ⊤-≡Dec :  ≡Dec {ł} ⊤
  ⊤-≡Dec ._≡?_ _ _ =  yes refl
  ⊤-≡Dec .≡?-refl =  refl

  ⊥-≡Dec :  ≡Dec {ł} ⊥
  ⊥-≡Dec ._≡?_ ()
  ⊥-≡Dec .≡?-refl {a = a}  with a
  … | ()

  -- Equality decision for ×, ⊎ and ¿

  ×-≡Dec :  {{≡Dec A}} →  {{≡Dec B}} →  ≡Dec $ A × B
  ×-≡Dec ._≡?_ (a , b) (a' , b')  with a ≡? a' | b ≡? b'
  … | yes refl | yes refl =  yes refl
  … | no a≢a' | _ =  no λ{ refl → a≢a' refl }
  … | _ | no b≢b' =  no λ{ refl → b≢b' refl }
  ×-≡Dec .≡?-refl {a , b}  rewrite ≡?-refl {a = a} | ≡?-refl {a = b} =  refl

  ⊎-≡Dec :  {{≡Dec A}} →  {{≡Dec B}} →  ≡Dec $ A ⊎ B
  ⊎-≡Dec ._≡?_ (ĩ₀ a) (ĩ₀ a')  with a ≡? a'
  … | yes refl =  yes refl
  … | no a≢a' =  no λ{ refl → a≢a' refl }
  ⊎-≡Dec ._≡?_ (ĩ₁ b) (ĩ₁ b')  with b ≡? b'
  … | yes refl =  yes refl
  … | no b≢b' =  no λ{ refl → b≢b' refl }
  ⊎-≡Dec ._≡?_ (ĩ₀ _) (ĩ₁ _) =  no λ ()
  ⊎-≡Dec ._≡?_ (ĩ₁ _) (ĩ₀ _) =  no λ ()
  ⊎-≡Dec .≡?-refl {ĩ₀ a}  rewrite ≡?-refl {a = a} =  refl
  ⊎-≡Dec .≡?-refl {ĩ₁ b}  rewrite ≡?-refl {a = b} =  refl

  ¿-≡Dec :  {{≡Dec A}} →  ≡Dec $ ¿ A
  ¿-≡Dec ._≡?_ ň ň =  yes refl
  ¿-≡Dec ._≡?_ (š a) (š a')  with a ≡? a'
  … | yes refl =  yes refl
  … | no a≢a' =  no λ{ refl → a≢a' refl }
  ¿-≡Dec ._≡?_ ň (š _) =  no λ ()
  ¿-≡Dec ._≡?_ (š _) ň =  no λ ()
  ¿-≡Dec .≡?-refl {ň} =  refl
  ¿-≡Dec .≡?-refl {š a}  rewrite ≡?-refl {a = a} =  refl

--------------------------------------------------------------------------------
-- upd˙ :  Update a map at an index

upd˙ :  {{≡Dec I}} →  ∀(i : I) →  A˙ i →  (∀ j →  A˙ j) →  ∀ j →  A˙ j
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

--------------------------------------------------------------------------------
-- upd˙² :  Update a map at two indices

upd˙² :  {{≡Dec I}} →  ∀(i : I) →  A˙ i →  ∀(j : I) →  A˙ j →
  (∀ k →  A˙ k) →  ∀ k →  A˙ k
upd˙² i a j b  =  upd˙ i a › upd˙ j b

abstract

  -- Self upd˙²

  upd˙²-self :  {{_ : ≡Dec I}} →
    i ≢ j →  upd˙² {I = I} i (f i) j (f j) f  ≡˙  f
  upd˙²-self {i = i} {j = j} i≢j k  with k ≡? j
  … | no _  with k ≡? i
  …   | yes refl =  refl
  …   | no _ =  refl
  upd˙²-self {i = i} {j = j} i≢j k | yes refl  with k ≡? i
  …   | yes refl =  absurd $ i≢j refl
  …   | no _ =  refl

  -- Double upd˙²

  upd˙²-2 :  {{_ : ≡Dec I}} →
    i ≢ j →  upd˙² {I = I} i a j b (upd˙² i a' j b' f)  ≡˙  upd˙² i a j b f
  upd˙²-2 i≢j =  upd˙-cong (upd˙-swap i≢j) ◇˙ upd˙-2 ◇˙ upd˙-cong upd˙-2
