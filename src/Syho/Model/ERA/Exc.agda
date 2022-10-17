--------------------------------------------------------------------------------
-- Exclusive ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Syho.Model.ERA.Exc where

open import Base.Level using (Level)
open import Base.Func using (id)
open import Base.Few using (⊥; ⊤)
open import Base.Eq using (_≡_; refl; ◠_; _◇_)
open import Base.Option using (¿_; š_; ň)
open import Base.Prod using (_,_)
open import Syho.Model.ERA.Base using (ERA)

open ERA using (Res; _≈_; _∙_; ε; ⌞_⌟; Env; _✓_; refl˜; ◠˜_; _◇˜_; ∙-congˡ;
  ∙-unitˡ; ∙-comm; ∙-assocʳ; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem; ✓-resp; ✓-rem)

private variable
  ł :  Level
  A :  Set ł

--------------------------------------------------------------------------------
-- Exc A :  Exclusive box

infix 8 #ˣ_

data  Exc (A : Set ł) :  Set ł  where

  -- Pending
  εˣ :  Exc A

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
εˣ ∙ˣ x =  x
↯ˣ ∙ˣ x =  ↯ˣ
x ∙ˣ εˣ =  x
_ ∙ˣ _ =  ↯ˣ

-- ✓ˣ :  Agreement between ¿ A and Exc A

infix 4 _✓ˣ_
_✓ˣ_ :  ∀{A : Set ł} →  ¿ A →  Exc A →  Set ł
_ ✓ˣ εˣ =  ⊤
_ ✓ˣ ↯ˣ =  ⊥
aˇ ✓ˣ #ˣ b =  aˇ ≡ š b

abstract

  -- x ∙ˣ εˣ equals x

  ∙ˣ-ε :  x ∙ˣ εˣ  ≡  x
  ∙ˣ-ε {x = εˣ} =  refl
  ∙ˣ-ε {x = #ˣ _} =  refl
  ∙ˣ-ε {x = ↯ˣ} =  refl

  -- x ∙ˣ ↯ˣ equals ↯ˣ

  ∙ˣ-↯ :  x ∙ˣ ↯ˣ  ≡  ↯ˣ
  ∙ˣ-↯ {x = εˣ} =  refl
  ∙ˣ-↯ {x = #ˣ _} =  refl
  ∙ˣ-↯ {x = ↯ˣ} =  refl

  -- ∙ˣ is commutative

  ∙ˣ-comm :  x ∙ˣ y  ≡  y ∙ˣ x
  ∙ˣ-comm {x = x} {εˣ}  rewrite ∙ˣ-ε {x = x} =  refl
  ∙ˣ-comm {x = εˣ} {y}  rewrite ∙ˣ-ε {x = y} =  refl
  ∙ˣ-comm {x = x} {↯ˣ}  rewrite ∙ˣ-↯ {x = x} =  refl
  ∙ˣ-comm {x = ↯ˣ} {y}  rewrite ∙ˣ-↯ {x = y} =  refl
  ∙ˣ-comm {x = #ˣ _} {#ˣ _} =  refl

  -- ∙ˣ is associative

  ∙ˣ-assocʳ :  (x ∙ˣ y) ∙ˣ z  ≡  x ∙ˣ (y ∙ˣ z)
  ∙ˣ-assocʳ {x = εˣ} =  refl
  ∙ˣ-assocʳ {x = ↯ˣ} =  refl
  ∙ˣ-assocʳ {x = #ˣ _} {εˣ} =  refl
  ∙ˣ-assocʳ {x = #ˣ _} {↯ˣ} =  refl
  ∙ˣ-assocʳ {x = #ˣ _} {#ˣ _} {εˣ} =  refl
  ∙ˣ-assocʳ {x = #ˣ _} {#ˣ _} {↯ˣ} =  refl
  ∙ˣ-assocʳ {x = #ˣ _} {#ˣ _} {#ˣ _} =  refl

  -- ň ✓ˣ x entails x ≡ εˣ

  ň-✓ˣ :  ň ✓ˣ x →  x ≡ εˣ
  ň-✓ˣ {x = εˣ} _ =  refl

  -- ✓ˣ is preserved by removal w.r.t. ∙ˣ

  ✓ˣ-rem :  aˇ ✓ˣ x ∙ˣ y →  aˇ ✓ˣ y
  ✓ˣ-rem {x = εˣ} =  id
  ✓ˣ-rem {y = εˣ} _ =  _

  -- Update ň into š a and εˣ into #ˣ a, preserving ✓ˣ - ∙ˣ x

  ✓ˣ-new :  ň ✓ˣ x →  š a ✓ˣ #ˣ a ∙ˣ x
  ✓ˣ-new {x = εˣ} _ =  refl

  -- Agreement from ✓ˣ x ∙ˣ #ˣ

  ✓ˣ-agree :  aˇ ✓ˣ #ˣ b ∙ˣ x →  aˇ ≡ š b
  ✓ˣ-agree {x = εˣ} refl =  refl

  -- Update aˇ into ň and #ˣ b into εˣ, preserving ✓ˣ - ∙ˣ x

  ✓ˣ-free :  aˇ ✓ˣ #ˣ b ∙ˣ x →  ň ✓ˣ x
  ✓ˣ-free {x = εˣ} _ =  _

  -- Update aˇ into š c and #ˣ b into #ˣ c, preserving ✓ˣ - ∙ˣ x

  ✓ˣ-upd :  aˇ ✓ˣ #ˣ b ∙ˣ x →  š c ✓ˣ #ˣ c ∙ˣ x
  ✓ˣ-upd {x = εˣ} _ =  refl

--------------------------------------------------------------------------------
-- Excᴱᴿᴬ A :  Exclusive ERA

Excᴱᴿᴬ :  Set ł →  ERA ł ł ł ł
Excᴱᴿᴬ A .Res =  Exc A
Excᴱᴿᴬ _ ._≈_ =  _≡_
Excᴱᴿᴬ _ ._∙_ =  _∙ˣ_
Excᴱᴿᴬ _ .ε =  εˣ
Excᴱᴿᴬ _ .⌞_⌟ _ =  εˣ
Excᴱᴿᴬ A .Env =  ¿ A
Excᴱᴿᴬ _ ._✓_ =  _✓ˣ_
Excᴱᴿᴬ _ .refl˜ =  refl
Excᴱᴿᴬ _ .◠˜_ =  ◠_
Excᴱᴿᴬ _ ._◇˜_ =  _◇_
Excᴱᴿᴬ _ .∙-congˡ refl =  refl
Excᴱᴿᴬ _ .∙-unitˡ =  refl
Excᴱᴿᴬ _ .∙-comm {a = x} =  ∙ˣ-comm {x = x}
Excᴱᴿᴬ _ .∙-assocʳ {a = x} =  ∙ˣ-assocʳ {x = x}
Excᴱᴿᴬ _ .⌞⌟-cong _ =  refl
Excᴱᴿᴬ _ .⌞⌟-add =  εˣ , refl
Excᴱᴿᴬ _ .⌞⌟-unitˡ =  refl
Excᴱᴿᴬ _ .⌞⌟-idem =  refl
Excᴱᴿᴬ _ .✓-resp refl =  id
Excᴱᴿᴬ _ .✓-rem {a = x} =  ✓ˣ-rem {x = x}
