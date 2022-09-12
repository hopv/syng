--------------------------------------------------------------------------------
-- Exclusive ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Syho.Model.ERA.Exc where

open import Base.Level using (Level)
open import Base.Func using (id)
open import Base.Few using (⊥; ⊤)
open import Base.Eq using (_≡_; refl; ◠_; _◇_)
open import Base.Prod using (_,_)
open import Base.Option using (¿_; š_; ň)
open import Syho.Model.ERA.Base using (ERA)

open ERA using (Env; Res; _≈_; _✓_; _∙_; ε; ⌞_⌟; refl˜; ◠˜_; _◇˜_; ⊑-refl;
  ∙-congˡ; ∙-unitˡ; ∙-comm; ∙-assocˡ; ✓-resp; ✓-rem; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ;
  ⌞⌟-idem; ⌞⌟-ε)

private variable
  ł :  Level
  A :  Set ł

--------------------------------------------------------------------------------
-- Exc A :  Exclusive box

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
aˇ ✓ˣ #ˣ b =  aˇ ≡ š b

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
  ✓ˣ-rem {x = #ˣ _} {?ˣ} =  _

  -- Update ň into š a and ?ˣ into #ˣ a, preserving ✓ˣ - ∙ˣ x

  ✓ˣ-alloc :  ň ✓ˣ x →  š a ✓ˣ #ˣ a ∙ˣ x
  ✓ˣ-alloc {x = ?ˣ} _ =  refl

  -- Agreement from ✓ˣ x ∙ˣ #ˣ

  ✓ˣ-agree :  aˇ ✓ˣ #ˣ b ∙ˣ x →  aˇ ≡ š b
  ✓ˣ-agree {x = ?ˣ} refl =  refl

  -- Update aˇ into ň and #ˣ b into ?ˣ, preserving ✓ˣ - ∙ˣ x

  ✓ˣ-free :  aˇ ✓ˣ #ˣ b ∙ˣ x →  ň ✓ˣ x
  ✓ˣ-free {x = ?ˣ} _ =  _

  -- Update aˇ into š c and #ˣ b into #ˣ c, preserving ✓ˣ - ∙ˣ x

  ✓ˣ-update :  aˇ ✓ˣ #ˣ b ∙ˣ x →  š c ✓ˣ #ˣ c ∙ˣ x
  ✓ˣ-update {x = ?ˣ} _ =  refl

--------------------------------------------------------------------------------
-- Excᴱᴿᴬ A :  Exclusive ERA

Excᴱᴿᴬ :  Set ł →  ERA ł ł ł ł
Excᴱᴿᴬ A .Env =  ¿ A
Excᴱᴿᴬ A .Res =  Exc A
Excᴱᴿᴬ _ ._≈_ =  _≡_
Excᴱᴿᴬ _ ._✓_ =  _✓ˣ_
Excᴱᴿᴬ _ ._∙_ =  _∙ˣ_
Excᴱᴿᴬ _ .ε =  ?ˣ
Excᴱᴿᴬ _ .⌞_⌟ _ =  ?ˣ
Excᴱᴿᴬ _ .refl˜ =  refl
Excᴱᴿᴬ _ .◠˜_ =  ◠_
Excᴱᴿᴬ _ ._◇˜_ =  _◇_
Excᴱᴿᴬ _ .∙-congˡ refl =  refl
Excᴱᴿᴬ _ .∙-unitˡ =  refl
Excᴱᴿᴬ _ .∙-comm {a = x} =  ∙ˣ-comm {x = x}
Excᴱᴿᴬ _ .∙-assocˡ {a = x} =  ∙ˣ-assocˡ {x = x}
Excᴱᴿᴬ _ .✓-resp refl =  id
Excᴱᴿᴬ _ .✓-rem {a = x} =  ✓ˣ-rem {x = x}
Excᴱᴿᴬ _ .⌞⌟-cong _ =  refl
Excᴱᴿᴬ _ .⌞⌟-add =  ?ˣ , refl
Excᴱᴿᴬ _ .⌞⌟-unitˡ =  refl
Excᴱᴿᴬ _ .⌞⌟-idem =  refl
