--------------------------------------------------------------------------------
-- Fractional-agreement resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Setoid using (Setoid)
module Shog.Model.RA.FracAg {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) where
open Setoid S using () renaming (Car to A)

open import Base.Level using (_⊔ˡ_)
open import Base.Few using (⊤; ⊥)
open import Base.Prod using (_×_; _,_)
open import Base.RatPos using (ℚ⁺; _≈ᴿ⁺_; _+ᴿ⁺_; _≤1ᴿ⁺; ≈ᴿ⁺-refl; ≈ᴿ⁺-sym;
  ≈ᴿ⁺-trans; ≡⇒≈ᴿ⁺; +ᴿ⁺-congˡ; +ᴿ⁺-comm; +ᴿ⁺-assocˡ; ≤1ᴿ⁺-resp; ≤1ᴿ⁺-rem)
open import Base.List using (List; []; _++_; ++-assocˡ)
open import Base.List.Set S using (_≈ᴸ_; homo; ≈ᴸ-refl; ≈ᴸ-sym; ≈ᴸ-trans; ≡⇒≈ᴸ;
  ++-congˡ; ++-comm; ++-idem; ++-⊆ᴸ-introʳ; homo-[]; homo-mono; homo-resp)
open import Shog.Model.RA using (RA)

--------------------------------------------------------------------------------
-- FracAg : FracAgRA's carrier

infix 8 ⟨_⟩ᶠ_
data  FracAg : Set ℓ  where
  ⟨_⟩ᶠ_ :  ℚ⁺ → List A → FracAg
  εᶠ :  FracAg

private variable
  x y z : FracAg

--------------------------------------------------------------------------------
-- Internal definitions
private

  -- Equivalence
  infix 4 _≈ᶠ_
  _≈ᶠ_ :  FracAg →  FracAg →  Set (ℓ ⊔ˡ ℓ≈)
  ⟨ p ⟩ᶠ as ≈ᶠ ⟨ q ⟩ᶠ bs =  p ≈ᴿ⁺ q  ×  as ≈ᴸ bs
  εᶠ ≈ᶠ εᶠ =  ⊤
  _ ≈ᶠ _ =  ⊥

  -- Validity
  infix 3 ✓ᶠ_
  ✓ᶠ_ :  FracAg →  Set (ℓ ⊔ˡ ℓ≈)
  ✓ᶠ ⟨ p ⟩ᶠ a =  p ≤1ᴿ⁺  ×  homo a
  ✓ᶠ εᶠ =  ⊤

  -- Product
  infixl 7 _∙ᶠ_
  _∙ᶠ_ :  FracAg →  FracAg →  FracAg
  εᶠ ∙ᶠ y =  y
  x ∙ᶠ εᶠ =  x
  ⟨ p ⟩ᶠ as ∙ᶠ ⟨ q ⟩ᶠ bs =  ⟨ p +ᴿ⁺ q ⟩ᶠ (as ++ bs)

--------------------------------------------------------------------------------
-- Lemmas
private abstract

  ≈ᶠ-refl :  x ≈ᶠ x
  ≈ᶠ-refl {⟨ p ⟩ᶠ _} =  ≈ᴿ⁺-refl {p} , ≈ᴸ-refl
  ≈ᶠ-refl {εᶠ} =  _

  ≈ᶠ-sym :  x ≈ᶠ y →  y ≈ᶠ x
  ≈ᶠ-sym {⟨ p ⟩ᶠ _} {⟨ q ⟩ᶠ _} (p≈q , as≈bs) =
    ≈ᴿ⁺-sym {p} {q} p≈q , ≈ᴸ-sym as≈bs
  ≈ᶠ-sym {εᶠ} {εᶠ} _ =  _

  ≈ᶠ-trans :  x ≈ᶠ y →  y ≈ᶠ z →  x ≈ᶠ z
  ≈ᶠ-trans {⟨ p ⟩ᶠ _} {⟨ q ⟩ᶠ _} {⟨ r ⟩ᶠ _} (p≈q , as≈bs) (q≈r , bs≈cs) =
    ≈ᴿ⁺-trans {p} {q} {r} p≈q q≈r , ≈ᴸ-trans as≈bs bs≈cs
  ≈ᶠ-trans {εᶠ} {εᶠ} {εᶠ} _ _ =  _

  ∙ᶠ-congˡ :  ∀ x y z →  x ≈ᶠ y →  x ∙ᶠ z  ≈ᶠ  y ∙ᶠ z
  ∙ᶠ-congˡ (⟨ p ⟩ᶠ _) (⟨ q ⟩ᶠ _) (⟨ r ⟩ᶠ _) (p≈q , as≈bs) =
    +ᴿ⁺-congˡ {p} {q} {r} p≈q , ++-congˡ as≈bs
  ∙ᶠ-congˡ (⟨ _ ⟩ᶠ _) (⟨ _ ⟩ᶠ _) εᶠ x≈y =  x≈y
  ∙ᶠ-congˡ εᶠ εᶠ _ _ =  ≈ᶠ-refl

  ∙ᶠ-comm :  ∀ x y →  x ∙ᶠ y  ≈ᶠ  y ∙ᶠ x
  ∙ᶠ-comm εᶠ y@(⟨ _ ⟩ᶠ _) =  ≈ᶠ-refl {y}
  ∙ᶠ-comm x@(⟨ _ ⟩ᶠ _) εᶠ =  ≈ᶠ-refl {x}
  ∙ᶠ-comm εᶠ εᶠ =  ≈ᶠ-refl
  ∙ᶠ-comm (⟨ p ⟩ᶠ as) (⟨ q ⟩ᶠ bs) =
    ≡⇒≈ᴿ⁺ (+ᴿ⁺-comm {p} {q}) , ++-comm {as} {bs}

  ∙ᶠ-assocˡ :  ∀ x y z →  (x ∙ᶠ y) ∙ᶠ z  ≈ᶠ  x ∙ᶠ (y ∙ᶠ z)
  ∙ᶠ-assocˡ (⟨ p ⟩ᶠ as) (⟨ q ⟩ᶠ _) (⟨ r ⟩ᶠ _) =
    ≡⇒≈ᴿ⁺ (+ᴿ⁺-assocˡ {p} {q} {r}) , ≡⇒≈ᴸ (++-assocˡ {as = as})
  ∙ᶠ-assocˡ εᶠ _ _ =  ≈ᶠ-refl
  ∙ᶠ-assocˡ (⟨ _ ⟩ᶠ _) εᶠ _ =  ≈ᶠ-refl
  ∙ᶠ-assocˡ x@(⟨ _ ⟩ᶠ _) y@(⟨ _ ⟩ᶠ _) εᶠ =  ≈ᶠ-refl {x ∙ᶠ y}

  ✓ᶠ-resp :  ∀ x y →  x ≈ᶠ y →  ✓ᶠ x →  ✓ᶠ y
  ✓ᶠ-resp (⟨ _ ⟩ᶠ _) (⟨ _ ⟩ᶠ _) (p≈q , as≈bs) (p≤1 , homo'as) =
    ≤1ᴿ⁺-resp p≈q p≤1 , homo-resp as≈bs homo'as
  ✓ᶠ-resp εᶠ εᶠ _ _ =  _

  ✓ᶠ-rem :  ∀ x y →  ✓ᶠ y ∙ᶠ x →  ✓ᶠ x
  ✓ᶠ-rem (⟨ p ⟩ᶠ _) (⟨ q ⟩ᶠ _) (q+p≤1 , homo'as++bs) =
    ≤1ᴿ⁺-rem {_} {q} q+p≤1 , homo-mono ++-⊆ᴸ-introʳ homo'as++bs
  ✓ᶠ-rem εᶠ _ _ =  _
  ✓ᶠ-rem (⟨ _ ⟩ᶠ _) εᶠ ✓x =  ✓x

--------------------------------------------------------------------------------
-- FracAgRA : Fractional resource algebra

open RA

FracAgRA : RA ℓ (ℓ ⊔ˡ ℓ≈) (ℓ ⊔ˡ ℓ≈)
FracAgRA .Car =  FracAg
FracAgRA ._≈_ =  _≈ᶠ_
FracAgRA .✓_ =  ✓ᶠ_
FracAgRA ._∙_ =  _∙ᶠ_
FracAgRA .ε =  εᶠ
FracAgRA .⌞_⌟ _ =  εᶠ
FracAgRA .refl˜ =  ≈ᶠ-refl
FracAgRA .sym˜ =  ≈ᶠ-sym
FracAgRA ._»˜_ =  ≈ᶠ-trans
FracAgRA .∙-congˡ =  ∙ᶠ-congˡ _ _ _
FracAgRA .∙-unitˡ =  ≈ᶠ-refl
FracAgRA .∙-comm {x} =  ∙ᶠ-comm x _
FracAgRA .∙-assocˡ {x} =  ∙ᶠ-assocˡ x _ _
FracAgRA .✓-resp =  ✓ᶠ-resp _ _
FracAgRA .✓-rem {_} {y} =  ✓ᶠ-rem _ y
FracAgRA .✓-ε =  _
FracAgRA .⌞⌟-cong _ =  ≈ᶠ-refl
FracAgRA .⌞⌟-add =  εᶠ , ≈ᶠ-refl
FracAgRA .⌞⌟-unitˡ =  ≈ᶠ-refl
FracAgRA .⌞⌟-idem =  ≈ᶠ-refl
