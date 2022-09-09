--------------------------------------------------------------------------------
-- Exclusivity box
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Syho.Model.Lib.Exc where

open import Base.Level using (Level)
open import Base.Func using (id)
open import Base.Few using (⊥; ⊤)
open import Base.Eq using (_≡_; refl)
open import Base.Option using (¿_; š_; ň)

private variable
  ł :  Level
  A :  Set ł

--------------------------------------------------------------------------------
-- Exc A :  Exclusivity box

infix 8 #ˣ_

data  Exc (A : Set ł) :  Set ł  where

  -- Pending
  ?ˣ :  Exc A

  -- Exclusively set
  #ˣ_ :  A →  Exc A

  -- Invalid
  ↯ˣ :  Exc A

private variable
  a b c :  A
  aˇ :  ¿ A
  x y z :  Exc A

-- ∙ˣ :  Product over Exc A

infixr 7 _∙ˣ_
_∙ˣ_ :  Exc A →  Exc A →  Exc A
?ˣ ∙ˣ x =  x
↯ˣ ∙ˣ x =  ↯ˣ
x ∙ˣ ?ˣ =  x
_ ∙ˣ _ =  ↯ˣ

-- ✓ˣ :  Agreement between ¿ A and Exc A

infix 4 _✓ˣ_
_✓ˣ_ :  ∀{A : Set ł} →  ¿ A →  Exc A →  Set ł
_ ✓ˣ ?ˣ =  ⊤
_ ✓ˣ ↯ˣ =  ⊥
š a ✓ˣ #ˣ b =  a ≡ b
ň ✓ˣ #ˣ _ =  ⊥

abstract

  -- ∙ˣ is commutative

  ∙ˣ-comm :  x ∙ˣ y  ≡  y ∙ˣ x
  ∙ˣ-comm {x = ?ˣ} {?ˣ} =  refl
  ∙ˣ-comm {x = ?ˣ} {↯ˣ} =  refl
  ∙ˣ-comm {x = ?ˣ} {#ˣ _} =  refl
  ∙ˣ-comm {x = ↯ˣ} {?ˣ} =  refl
  ∙ˣ-comm {x = ↯ˣ} {↯ˣ} =  refl
  ∙ˣ-comm {x = ↯ˣ} {#ˣ _} =  refl
  ∙ˣ-comm {x = #ˣ _} {?ˣ} =  refl
  ∙ˣ-comm {x = #ˣ _} {↯ˣ} =  refl
  ∙ˣ-comm {x = #ˣ _} {#ˣ _} =  refl

  -- ∙ˣ is associative

  ∙ˣ-assocˡ :  (x ∙ˣ y) ∙ˣ z  ≡  x ∙ˣ (y ∙ˣ z)
  ∙ˣ-assocˡ {x = ?ˣ} =  refl
  ∙ˣ-assocˡ {x = ↯ˣ} =  refl
  ∙ˣ-assocˡ {x = #ˣ _} {?ˣ} =  refl
  ∙ˣ-assocˡ {x = #ˣ _} {↯ˣ} =  refl
  ∙ˣ-assocˡ {x = #ˣ _} {#ˣ _} {?ˣ} =  refl
  ∙ˣ-assocˡ {x = #ˣ _} {#ˣ _} {↯ˣ} =  refl
  ∙ˣ-assocˡ {x = #ˣ _} {#ˣ _} {#ˣ _} =  refl

  -- ✓ˣ holds after removing an element with respect to ∙ˣ

  ✓ˣ-rem :  aˇ ✓ˣ x ∙ˣ y →  aˇ ✓ˣ y
  ✓ˣ-rem {x = ?ˣ} =  id
  ✓ˣ-rem {aˇ = š _} {#ˣ _} {?ˣ} =  _

  -- Update ň into š a and y into #ˣ a, preserving ✓ˣ x ∙ˣ

  ✓ˣ-alloc :  ň ✓ˣ x ∙ˣ y →  š a ✓ˣ x ∙ˣ #ˣ a
  ✓ˣ-alloc {x = ?ˣ} {?ˣ} _ =  refl
  ✓ˣ-alloc {x = ?ˣ} {#ˣ _} ()
  ✓ˣ-alloc {x = ?ˣ} {↯ˣ} ()

  -- Agreement from ✓ˣ x ∙ˣ #ˣ

  ✓ˣ-agree : aˇ ✓ˣ x ∙ˣ #ˣ b →  aˇ ≡ š b
  ✓ˣ-agree {aˇ = š _} {?ˣ} refl =  refl

  -- Update aˇ into ň and #ˣ b into ?ˣ, preserving ✓ˣ x ∙ˣ

  ✓ˣ-free : aˇ ✓ˣ x ∙ˣ #ˣ b →  ň ✓ˣ x ∙ˣ ?ˣ
  ✓ˣ-free {x = ?ˣ} _ =  _

  -- Update aˇ into š c and #ˣ b into #ˣ c, preserving ✓ˣ x ∙ˣ

  ✓ˣ-update : aˇ ✓ˣ x ∙ˣ #ˣ b →  š c ✓ˣ x ∙ˣ #ˣ c
  ✓ˣ-update {x = ?ˣ} _ =  refl
