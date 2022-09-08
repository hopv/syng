--------------------------------------------------------------------------------
-- Exclusivity box
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Syho.Model.Lib.Exc where

open import Base.Level using (Level)
open import Base.Func using (id)
open import Base.Few using (⊥; ⊤)
open import Base.Eq using (_≡_; refl)

private variable
  ł :  Level
  A :  Set ł
  a b :  A

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
  x y z :  Exc A

-- ✓ˣ :  Validity of Exc A

infix 3 ✓ˣ_
✓ˣ_ :  Exc A →  Set₀
✓ˣ ↯ˣ =  ⊥
✓ˣ _ =  ⊤

-- ∙ˣ :  Product over Exc A

infixl 7 _∙ˣ_
_∙ˣ_ :  Exc A →  Exc A →  Exc A
?ˣ ∙ˣ x =  x
↯ˣ ∙ˣ x =  ↯ˣ
x ∙ˣ ?ˣ =  x
_ ∙ˣ _ =  ↯ˣ

-- ←ˣ :  Agreement between A and Exc A

infix 4 _←ˣ_
_←ˣ_ :  ∀{A : Set ł} →  A →  Exc A →  Set ł
a ←ˣ #ˣ b =  a ≡ b
_ ←ˣ ?ˣ =  ⊤
_ ←ˣ ↯ˣ =  ⊥

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

  -- x ∙ˣ ?ˣ is x

  ∙ˣ-?ˣ :  x ∙ˣ ?ˣ ≡ x
  ∙ˣ-?ˣ {x = x}  rewrite ∙ˣ-comm {x = x} {?ˣ} =  refl

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

  ✓ˣ-rem :  ✓ˣ x ∙ˣ y →  ✓ˣ y
  ✓ˣ-rem {x = ?ˣ} =  id
  ✓ˣ-rem {x = #ˣ _} {y = ?ˣ} =  _
