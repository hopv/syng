--------------------------------------------------------------------------------
-- Exclusive resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Setoid using (Setoid)
module Shog.Model.RA.Ex {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) where
open Setoid S renaming (Car to A)

open import Base.Level using (Level; 0ˡ)
open import Base.Func using (id)
open import Base.Prod using (_,_)
open import Base.Few using (⊤; ⊥)
open import Shog.Model.RA using (RA)

--------------------------------------------------------------------------------
-- Ex : ExRA's carrier

data  Ex :  Set ℓ  where
  -- Pending
  ?ˣ :  Ex
  -- Exclusively set
  #ˣ :  A →  Ex
  -- Invalid
  ↯ˣ :  Ex

--------------------------------------------------------------------------------
-- Internal definitions
private

  -- Equivalence
  infix 4 _≈ˣ_
  _≈ˣ_ :  Ex → Ex → Set ℓ≈
  ?ˣ ≈ˣ ?ˣ =  ⊤
  ↯ˣ ≈ˣ ↯ˣ =  ⊤
  #ˣ a ≈ˣ #ˣ b =  a ≈ b
  _ ≈ˣ _ =  ⊥

  -- Validity
  infix 3 ✓ˣ_
  ✓ˣ_ :  Ex → Set
  ✓ˣ_ ↯ˣ =  ⊥
  ✓ˣ_ _ =  ⊤

  -- Product
  infixl 7 _∙ˣ_
  _∙ˣ_ :  Ex → Ex → Ex
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
  ≈ˣ-sym (#ˣ _) (#ˣ _) =  sym˜

  ≈ˣ-trans :  ∀ x y z →  x ≈ˣ y →  y ≈ˣ z →  x ≈ˣ z
  ≈ˣ-trans ?ˣ ?ˣ ?ˣ =  _
  ≈ˣ-trans ↯ˣ ↯ˣ ↯ˣ =  _
  ≈ˣ-trans (#ˣ _) (#ˣ _) (#ˣ _) =  _»˜_

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

  ✓ˣ-rem :  ∀ x y →  ✓ˣ y ∙ˣ x →  ✓ˣ x
  ✓ˣ-rem _ ?ˣ =  id
  ✓ˣ-rem ?ˣ (#ˣ _) =  _

--------------------------------------------------------------------------------
-- ExRA : Exclusive resource algebra

open RA

ExRA : RA ℓ ℓ≈ 0ˡ
ExRA .Car =  Ex
ExRA ._≈_ =  _≈ˣ_
ExRA .✓_ =  ✓ˣ_
ExRA ._∙_ =  _∙ˣ_
ExRA .ε =  ?ˣ
ExRA .⌞_⌟ _ =  ?ˣ
ExRA .refl˜ {x} =  ≈ˣ-refl x
ExRA .sym˜ {x} =  ≈ˣ-sym x _
ExRA ._»˜_ {x} =  ≈ˣ-trans x _ _
ExRA .∙-congˡ {x} =  ∙ˣ-congˡ x _ _
ExRA .∙-unitˡ {x} =  ≈ˣ-refl x
ExRA .∙-comm {x} =  ∙ˣ-comm x _
ExRA .∙-assocˡ {x} =  ∙ˣ-assocˡ x _ _
ExRA .✓-resp =  ✓ˣ-resp _ _
ExRA .✓-rem {x} {y} =  ✓ˣ-rem x y
ExRA .✓-ε =  _
ExRA .⌞⌟-cong =  _
ExRA .⌞⌟-add =  ?ˣ , _
ExRA .⌞⌟-unitˡ {x} =  ≈ˣ-refl x
ExRA .⌞⌟-idem =  _
