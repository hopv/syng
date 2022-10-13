--------------------------------------------------------------------------------
-- Syntactic set
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Base.Sety where

open import Base.Func using (_$_; _∘_; id)
open import Base.Few using (⟨2⟩; ⊤; ⊥; absurd)
open import Base.Eq using (_≡_; refl; ◠_; cong; cong₂; subst)
open import Base.Dec using (Dec; yes; no; Yes; ≡Dec; _≟_)
open import Base.Bool using (𝔹)
open import Base.Zoi using (Zoi)
open import Base.Option using (¿_)
open import Base.Prod using (_×_; _,_; -,_; _,-)
open import Base.Sum using (_⨿_; ĩ₀_; ĩ₁_)
open import Base.Nat using (ℕ)
open import Base.Natp using (ℕ⁺)
open import Base.List using (List; List⁺; [_]⁺; hd⁺)
open import Base.Seq using (Seq∞; hdˢ; repˢ)
open import Base.Str using (Char; Str)
open import Base.Ratp using (ℚ⁺)

--------------------------------------------------------------------------------
-- Setʸ :  Syntactic set, or syntax for a subset of Set₀

infixr -1 _→ʸ_
infixr 0 _⨿ʸ_
infixr 1 _×ʸ_
infix 8 ¿ʸ_

data  Setʸ :  Set₀  where
  ⟨2⟩ʸ ⊤ʸ ⊥ʸ 𝔹ʸ Zoiʸ ℕʸ ℕ⁺ʸ Charʸ Strʸ ℚ⁺ʸ Setʸʸ :  Setʸ
  ¿ʸ_ Listʸ List⁺ʸ Seq∞ʸ :  Setʸ →  Setʸ
  _→ʸ_ _×ʸ_ _⨿ʸ_ :  Setʸ →  Setʸ →  Setʸ

-- ⸨ ⸩ʸ :  Interpret Setʸ as Set₀

⸨_⸩ʸ :  Setʸ  →  Set₀
⸨ ⟨2⟩ʸ ⸩ʸ =  ⟨2⟩
⸨ ⊤ʸ ⸩ʸ =  ⊤
⸨ ⊥ʸ ⸩ʸ =  ⊥
⸨ 𝔹ʸ ⸩ʸ =  𝔹
⸨ Zoiʸ ⸩ʸ =  Zoi
⸨ ℕʸ ⸩ʸ =  ℕ
⸨ ℕ⁺ʸ ⸩ʸ =  ℕ⁺
⸨ Charʸ ⸩ʸ =  Char
⸨ Strʸ ⸩ʸ =  Str
⸨ ℚ⁺ʸ ⸩ʸ =  ℚ⁺
⸨ Setʸʸ ⸩ʸ =  Setʸ
⸨ ¿ʸ Aʸ ⸩ʸ =  ¿ ⸨ Aʸ ⸩ʸ
⸨ Listʸ Aʸ ⸩ʸ =  List ⸨ Aʸ ⸩ʸ
⸨ List⁺ʸ Aʸ ⸩ʸ =  List⁺ ⸨ Aʸ ⸩ʸ
⸨ Seq∞ʸ Aʸ ⸩ʸ =  Seq∞ ⸨ Aʸ ⸩ʸ
⸨ Aʸ →ʸ Bʸ ⸩ʸ =  ⸨ Aʸ ⸩ʸ → ⸨ Bʸ ⸩ʸ
⸨ Aʸ ×ʸ Bʸ ⸩ʸ =  ⸨ Aʸ ⸩ʸ × ⸨ Bʸ ⸩ʸ
⸨ Aʸ ⨿ʸ Bʸ ⸩ʸ =  ⸨ Aʸ ⸩ʸ ⨿ ⸨ Bʸ ⸩ʸ

instance

  -- Setʸ is inhabited

  Setʸ-Dec :  Dec Setʸ
  Setʸ-Dec =  yes ⟨2⟩ʸ

private variable
  A B :  Set₀
  Aʸ :  Setʸ

--------------------------------------------------------------------------------
-- Syn A :  A has a syntactic representation

record  Syn (A : Set₀) :  Set₁  where
  field
    -- Syntactic representation of A
    setʸ :  Setʸ
    -- ⸨ setʸ ⸩ʸ equals A
    ⸨⸩ʸ≡ :  ⸨ setʸ ⸩ʸ  ≡  A

open Syn {{…}} public

-- Conversion between ⸨ setʸ ⸩ʸ and A

⸨⸩ʸ⇒ :  {{_ : Syn A}} →  ⸨ setʸ {A} ⸩ʸ →  A
⸨⸩ʸ⇒ a =  subst id ⸨⸩ʸ≡ a

⇒⸨⸩ʸ :  {{_ : Syn A}} →  A →  ⸨ setʸ {A} ⸩ʸ
⇒⸨⸩ʸ a =  subst id (◠ ⸨⸩ʸ≡) a

instance

  -- Instances for Syn

  ⟨2⟩-Syn :  Syn ⟨2⟩
  ⟨2⟩-Syn .setʸ =  ⟨2⟩ʸ
  ⟨2⟩-Syn .⸨⸩ʸ≡ =  refl

  ⊤-Syn :  Syn ⊤
  ⊤-Syn .setʸ =  ⊤ʸ
  ⊤-Syn .⸨⸩ʸ≡ =  refl

  ⊥-Syn :  Syn ⊥
  ⊥-Syn .setʸ =  ⊥ʸ
  ⊥-Syn .⸨⸩ʸ≡ =  refl

  𝔹-Syn :  Syn 𝔹
  𝔹-Syn .setʸ =  𝔹ʸ
  𝔹-Syn .⸨⸩ʸ≡ =  refl

  Zoi-Syn :  Syn Zoi
  Zoi-Syn .setʸ =  Zoiʸ
  Zoi-Syn .⸨⸩ʸ≡ =  refl

  ℕ-Syn :  Syn ℕ
  ℕ-Syn .setʸ =  ℕʸ
  ℕ-Syn .⸨⸩ʸ≡ =  refl

  ℕ⁺-Syn :  Syn ℕ⁺
  ℕ⁺-Syn .setʸ =  ℕ⁺ʸ
  ℕ⁺-Syn .⸨⸩ʸ≡ =  refl

  Char-Syn :  Syn Char
  Char-Syn .setʸ =  Charʸ
  Char-Syn .⸨⸩ʸ≡ =  refl

  Str-Syn :  Syn Str
  Str-Syn .setʸ =  Strʸ
  Str-Syn .⸨⸩ʸ≡ =  refl

  ℚ⁺-Syn :  Syn ℚ⁺
  ℚ⁺-Syn .setʸ =  ℚ⁺ʸ
  ℚ⁺-Syn .⸨⸩ʸ≡ =  refl

  Setʸ-Syn :  Syn Setʸ
  Setʸ-Syn .setʸ =  Setʸʸ
  Setʸ-Syn .⸨⸩ʸ≡ =  refl

  ¿-Syn :  {{Syn A}} →  Syn (¿ A)
  ¿-Syn {A} .setʸ =  ¿ʸ setʸ {A}
  ¿-Syn {A} .⸨⸩ʸ≡ =  cong ¿_ $ ⸨⸩ʸ≡ {A}

  List-Syn :  {{Syn A}} →  Syn (List A)
  List-Syn {A} .setʸ =  Listʸ $ setʸ {A}
  List-Syn {A} .⸨⸩ʸ≡ =  cong List $ ⸨⸩ʸ≡ {A}

  List⁺-Syn :  {{Syn A}} →  Syn (List⁺ A)
  List⁺-Syn {A} .setʸ =  List⁺ʸ $ setʸ {A}
  List⁺-Syn {A} .⸨⸩ʸ≡ =  cong List⁺ $ ⸨⸩ʸ≡ {A}

  Seq∞-Syn :  {{Syn A}} →  Syn (Seq∞ A)
  Seq∞-Syn {A} .setʸ =  Seq∞ʸ $ setʸ {A}
  Seq∞-Syn {A} .⸨⸩ʸ≡ =  cong Seq∞ $ ⸨⸩ʸ≡ {A}

  →-Syn :  {{Syn A}} →  {{Syn B}} →  Syn (A → B)
  →-Syn {A} {B} .setʸ =  setʸ {A} →ʸ setʸ {B}
  →-Syn {A} {B} .⸨⸩ʸ≡ =  cong₂ (λ A B → A → B) (⸨⸩ʸ≡ {A}) (⸨⸩ʸ≡ {B})

  ×-Syn :  {{Syn A}} →  {{Syn B}} →  Syn (A × B)
  ×-Syn {A} {B} .setʸ =  setʸ {A} ×ʸ setʸ {B}
  ×-Syn {A} {B} .⸨⸩ʸ≡ =  cong₂ _×_ (⸨⸩ʸ≡ {A}) (⸨⸩ʸ≡ {B})

  ⨿-Syn :  {{Syn A}} →  {{Syn B}} →  Syn (A ⨿ B)
  ⨿-Syn {A} {B} .setʸ =  setʸ {A} ⨿ʸ setʸ {B}
  ⨿-Syn {A} {B} .⸨⸩ʸ≡ =  cong₂ _⨿_ (⸨⸩ʸ≡ {A}) (⸨⸩ʸ≡ {B})

--------------------------------------------------------------------------------
-- Equality decision for Setʸ

-- Rough numbering for Setʸ

roughʸ :  Setʸ →  ℕ
roughʸ ⟨2⟩ʸ =  0
roughʸ ⊤ʸ =  1
roughʸ ⊥ʸ =  2
roughʸ 𝔹ʸ =  3
roughʸ Zoiʸ =  4
roughʸ ℕʸ =  5
roughʸ ℕ⁺ʸ =  6
roughʸ Charʸ =  7
roughʸ Strʸ =  8
roughʸ ℚ⁺ʸ =  9
roughʸ Setʸʸ =  10
roughʸ (¿ʸ _) =  11
roughʸ (Listʸ _) =  12
roughʸ (List⁺ʸ _) =  13
roughʸ (Seq∞ʸ _) =  14
roughʸ (_ →ʸ _) =  15
roughʸ (_ ×ʸ _) =  16
roughʸ (_ ⨿ʸ _) =  17

instance

  Setʸ-≡Dec :  ≡Dec Setʸ
  Setʸ-≡Dec ._≟_ =  _≟'_
   where
    infix 4 _≟'_
    _≟'_ :  ∀ Aʸ Bʸ →  Dec $ Aʸ ≡ Bʸ
    Aʸ ≟' Bʸ  with roughʸ Aʸ ≟ roughʸ Bʸ
    … | no rA≢rB =  no λ{ refl → rA≢rB refl }
    ⟨2⟩ʸ ≟' ⟨2⟩ʸ | yes _ =  yes refl
    ⊤ʸ ≟' ⊤ʸ | yes _ =  yes refl
    ⊥ʸ ≟' ⊥ʸ | yes _ =  yes refl
    𝔹ʸ ≟' 𝔹ʸ | yes _ =  yes refl
    Zoiʸ ≟' Zoiʸ | yes _ =  yes refl
    ℕʸ ≟' ℕʸ | yes _ =  yes refl
    ℕ⁺ʸ ≟' ℕ⁺ʸ | yes _ =  yes refl
    Charʸ ≟' Charʸ | yes _ =  yes refl
    Strʸ ≟' Strʸ | yes _ =  yes refl
    ℚ⁺ʸ ≟' ℚ⁺ʸ | yes _ =  yes refl
    Setʸʸ ≟' Setʸʸ | yes _ =  yes refl
    ¿ʸ Aʸ ≟' ¿ʸ Bʸ | yes _  with Aʸ ≟' Bʸ
    … | yes refl =  yes refl
    … | no A≢B =  no λ{ refl → A≢B refl }
    Listʸ Aʸ ≟' Listʸ Bʸ | yes _  with Aʸ ≟' Bʸ
    … | yes refl =  yes refl
    … | no A≢B =  no λ{ refl → A≢B refl }
    List⁺ʸ Aʸ ≟' List⁺ʸ Bʸ | yes _  with Aʸ ≟' Bʸ
    … | yes refl =  yes refl
    … | no A≢B =  no λ{ refl → A≢B refl }
    Seq∞ʸ Aʸ ≟' Seq∞ʸ Bʸ | yes _  with Aʸ ≟' Bʸ
    … | yes refl =  yes refl
    … | no A≢B =  no λ{ refl → A≢B refl }
    (Aʸ →ʸ Bʸ) ≟' (Cʸ →ʸ Dʸ) | yes _  with Aʸ ≟' Cʸ | Bʸ ≟' Dʸ
    … | yes refl | yes refl =  yes refl
    … | no A≢C | _ =  no λ{ refl → A≢C refl }
    … | _ | no B≢D =  no λ{ refl → B≢D refl }
    (Aʸ ×ʸ Bʸ) ≟' (Cʸ ×ʸ Dʸ) | yes _  with Aʸ ≟' Cʸ | Bʸ ≟' Dʸ
    … | yes refl | yes refl =  yes refl
    … | no A≢C | _ =  no λ{ refl → A≢C refl }
    … | _ | no B≢D =  no λ{ refl → B≢D refl }
    (Aʸ ⨿ʸ Bʸ) ≟' (Cʸ ⨿ʸ Dʸ) | yes _  with Aʸ ≟' Cʸ | Bʸ ≟' Dʸ
    … | yes refl | yes refl =  yes refl
    … | no A≢C | _ =  no λ{ refl → A≢C refl }
    … | _ | no B≢D =  no λ{ refl → B≢D refl }
