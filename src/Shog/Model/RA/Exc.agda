--------------------------------------------------------------------------------
-- Exclusive resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Level using (Level)
open import Base.Setoid using (Setoid)
module Shog.Model.RA.Exc {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) {ℓ✓ : Level} where
open Setoid S using (_≈_; refl˜; ◠˜_; _◇˜_) renaming (Car to A)

open import Base.Func using (id)
open import Base.Prod using (_,_)
open import Base.Few using (⊤; ⊥)
open import Shog.Model.RA using (RA)

open RA renaming (_≈_ to _≈'_; refl˜ to refl'; ◠˜_ to ◠'_; _◇˜_ to _◇'_)

--------------------------------------------------------------------------------
-- Exc : ExcRA's carrier

infix 8 #ˣ_
data  Exc :  Set ℓ  where
  -- Pending
  ?ˣ :  Exc
  -- Exclusively set
  #ˣ_ :  A →  Exc
  -- Invalid
  ↯ˣ :  Exc

private variable
  a b : A

--------------------------------------------------------------------------------
-- Internal definitions
private

  -- Equivalence
  infix 4 _≈ˣ_
  _≈ˣ_ :  Exc → Exc → Set ℓ≈
  ?ˣ ≈ˣ ?ˣ =  ⊤
  ↯ˣ ≈ˣ ↯ˣ =  ⊤
  #ˣ a ≈ˣ #ˣ b =  a ≈ b
  _ ≈ˣ _ =  ⊥

  -- Validity
  infix 3 ✓ˣ_
  ✓ˣ_ :  Exc → Set ℓ✓
  ✓ˣ ↯ˣ =  ⊥
  ✓ˣ _ =  ⊤

  -- Product
  infixl 7 _∙ˣ_
  _∙ˣ_ :  Exc → Exc → Exc
  ?ˣ ∙ˣ x =  x
  ↯ˣ ∙ˣ x =  ↯ˣ
  x ∙ˣ ?ˣ =  x
  _ ∙ˣ _ =  ↯ˣ

-- Lemmas
private abstract

  ≈ˣ-refl :  ∀ x →  x ≈ˣ x
  ≈ˣ-refl ?ˣ =  _
  ≈ˣ-refl ↯ˣ =  _
  ≈ˣ-refl (#ˣ _) =  refl˜

  ≈ˣ-sym :  ∀ x y →  x ≈ˣ y →  y ≈ˣ x
  ≈ˣ-sym ?ˣ ?ˣ =  _
  ≈ˣ-sym ↯ˣ ↯ˣ =  _
  ≈ˣ-sym (#ˣ _) (#ˣ _) =  ◠˜_

  ≈ˣ-trans :  ∀ x y z →  x ≈ˣ y →  y ≈ˣ z →  x ≈ˣ z
  ≈ˣ-trans ?ˣ ?ˣ ?ˣ =  _
  ≈ˣ-trans ↯ˣ ↯ˣ ↯ˣ =  _
  ≈ˣ-trans (#ˣ _) (#ˣ _) (#ˣ _) =  _◇˜_

  ∙ˣ-congˡ :  ∀ x y z →  x ≈ˣ y →  x ∙ˣ z  ≈ˣ  y ∙ˣ z
  ∙ˣ-congˡ ?ˣ ?ˣ z _ =  ≈ˣ-refl z
  ∙ˣ-congˡ ↯ˣ ↯ˣ _ _ =  _
  ∙ˣ-congˡ (#ˣ a) (#ˣ b) ?ˣ a≈b =  a≈b
  ∙ˣ-congˡ (#ˣ _) (#ˣ _) ↯ˣ _ =  _
  ∙ˣ-congˡ (#ˣ _) (#ˣ _) (#ˣ _) _ =  _

  ∙ˣ-comm :  ∀ x y →  x ∙ˣ y  ≈ˣ  y ∙ˣ x
  ∙ˣ-comm ?ˣ ?ˣ =  _
  ∙ˣ-comm ?ˣ ↯ˣ =  _
  ∙ˣ-comm ?ˣ (#ˣ _) =  refl˜
  ∙ˣ-comm ↯ˣ ?ˣ =  _
  ∙ˣ-comm ↯ˣ ↯ˣ =  _
  ∙ˣ-comm ↯ˣ (#ˣ _) =  _
  ∙ˣ-comm (#ˣ _) ?ˣ =  refl˜
  ∙ˣ-comm (#ˣ _) ↯ˣ =  _
  ∙ˣ-comm (#ˣ _) (#ˣ _) =  _

  ∙ˣ-assocˡ :  ∀ x y z →  (x ∙ˣ y) ∙ˣ z  ≈ˣ  x ∙ˣ (y ∙ˣ z)
  ∙ˣ-assocˡ ?ˣ x y =  ≈ˣ-refl (x ∙ˣ y)
  ∙ˣ-assocˡ ↯ˣ _ _ =  _
  ∙ˣ-assocˡ (#ˣ a) ?ˣ y =  ≈ˣ-refl (#ˣ a ∙ˣ y)
  ∙ˣ-assocˡ (#ˣ _) ↯ˣ y =  _
  ∙ˣ-assocˡ (#ˣ _) (#ˣ _) ?ˣ =  _
  ∙ˣ-assocˡ (#ˣ _) (#ˣ _) ↯ˣ =  _
  ∙ˣ-assocˡ (#ˣ _) (#ˣ _) (#ˣ _) =  _

  ✓ˣ-resp :  ∀ x y →  x ≈ˣ y →  ✓ˣ x →  ✓ˣ y
  ✓ˣ-resp ?ˣ ?ˣ _ _ =  _
  ✓ˣ-resp (#ˣ _) (#ˣ _) _ _ =  _

  ✓ˣ-rem :  ∀ x y →  ✓ˣ x ∙ˣ y →  ✓ˣ y
  ✓ˣ-rem ?ˣ _ =  id
  ✓ˣ-rem (#ˣ _) ?ˣ =  _

--------------------------------------------------------------------------------
-- ExcRA : Exclusive resource algebra

ExcRA : RA ℓ ℓ≈ ℓ✓
ExcRA .Car =  Exc
ExcRA ._≈'_ =  _≈ˣ_
ExcRA .✓_ =  ✓ˣ_
ExcRA ._∙_ =  _∙ˣ_
ExcRA .ε =  ?ˣ
ExcRA .⌞_⌟ _ =  ?ˣ
ExcRA .refl' {x} =  ≈ˣ-refl x
ExcRA .◠'_ {x} =  ≈ˣ-sym x _
ExcRA ._◇'_ {x} =  ≈ˣ-trans x _ _
ExcRA .∙-congˡ {x} =  ∙ˣ-congˡ x _ _
ExcRA .∙-unitˡ {x} =  ≈ˣ-refl x
ExcRA .∙-comm {x} =  ∙ˣ-comm x _
ExcRA .∙-assocˡ {x} =  ∙ˣ-assocˡ x _ _
ExcRA .✓-resp =  ✓ˣ-resp _ _
ExcRA .✓-rem {x} {y} =  ✓ˣ-rem x y
ExcRA .✓-ε =  _
ExcRA .⌞⌟-cong =  _
ExcRA .⌞⌟-add =  ?ˣ , _
ExcRA .⌞⌟-unitˡ {x} =  ≈ˣ-refl x
ExcRA .⌞⌟-idem =  _

open RA ExcRA using () renaming (_↝_ to _↝⁺_)

--------------------------------------------------------------------------------
-- Lemmas

abstract

  -- Update on #ˣ

  #ˣ-↝ :  #ˣ a  ↝⁺  #ˣ b
  #ˣ-↝ ?ˣ =  _
  -- The frame z can only be ?ˣ; otherwise ✓ z ∙ #ˣ a does not hold
