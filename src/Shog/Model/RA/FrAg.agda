--------------------------------------------------------------------------------
-- Fractional-agreement resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Setoid using (Setoid)
module Shog.Model.RA.FrAg {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) where
open Setoid S using (_≈_; refl˜) renaming (Car to A)

open import Base.Level using (_⌴_)
open import Base.Few using (⊤; ⊥; absurd)
open import Base.Prod using (_×_; _,_)
open import Base.Func using (_$_)
open import Base.RatPos using (ℚ⁺; _≈ᴿ⁺_; _+ᴿ⁺_; _≤1ᴿ⁺; 1ᴿ⁺; ≈ᴿ⁺-refl; ≈ᴿ⁺-sym;
  ≈ᴿ⁺-trans; ≡⇒≈ᴿ⁺; +ᴿ⁺-congˡ; +ᴿ⁺-comm; +ᴿ⁺-assocˡ; ≤1ᴿ⁺-resp; ≤1ᴿ⁺-rem;
  1≤1ᴿ⁺; ?+1-not-≤1ᴿ⁺)
open import Base.List using (List; []; _++_; [_]; ++-assocˡ)
open import Base.List.Set S using (_≈ᴸ_; homo; ≈ᴸ-refl; ≈ᴸ-sym; ≈ᴸ-trans; ≡⇒≈ᴸ;
  ++-congˡ; ++-comm; ++-idem; ++-⊆ᴸ-introʳ; homo-[]; homo-mono; homo-resp;
  [?]-cong; homo-[?]; homo-agree)
open import Shog.Model.RA using (RA)

--------------------------------------------------------------------------------
-- FrAg : FrAgᴿᴬ's carrier

infix 8 ⟨_⟩ᶠᴸ_
data  FrAg : Set ℓ  where
  ⟨_⟩ᶠᴸ_ :  ℚ⁺ → List A → FrAg  -- Fractional agreement, internal
  εᶠ :  FrAg  -- Unit

--------------------------------------------------------------------------------
-- ⟨ p ⟩ᶠ a : Specifying the value a with the fraction p

infix 8 ⟨_⟩ᶠ_
⟨_⟩ᶠ_ :  ℚ⁺ → A → FrAg
⟨ p ⟩ᶠ a =  ⟨ p ⟩ᶠᴸ [ a ]

private variable
  x y z : FrAg
  p q :  ℚ⁺
  a b :  A

--------------------------------------------------------------------------------
-- Internal definitions

private

  -- Equivalence
  infix 4 _≈ᶠ_
  _≈ᶠ_ :  FrAg →  FrAg →  Set (ℓ ⌴ ℓ≈)
  ⟨ p ⟩ᶠᴸ as ≈ᶠ ⟨ q ⟩ᶠᴸ bs =  p ≈ᴿ⁺ q  ×  as ≈ᴸ bs
  εᶠ ≈ᶠ εᶠ =  ⊤
  _ ≈ᶠ _ =  ⊥

  -- Validity
  infix 3 ✓ᶠ_
  ✓ᶠ_ :  FrAg →  Set (ℓ ⌴ ℓ≈)
  ✓ᶠ ⟨ p ⟩ᶠᴸ a =  p ≤1ᴿ⁺  ×  homo a
  ✓ᶠ εᶠ =  ⊤

  -- Product
  infixl 7 _∙ᶠ_
  _∙ᶠ_ :  FrAg →  FrAg →  FrAg
  εᶠ ∙ᶠ y =  y
  x ∙ᶠ εᶠ =  x
  ⟨ p ⟩ᶠᴸ as ∙ᶠ ⟨ q ⟩ᶠᴸ bs =  ⟨ p +ᴿ⁺ q ⟩ᶠᴸ (as ++ bs)

--------------------------------------------------------------------------------
-- Internal lemmas

private abstract

  ≈ᶠ-refl :  x ≈ᶠ x
  ≈ᶠ-refl {⟨ p ⟩ᶠᴸ _} =  ≈ᴿ⁺-refl {p} , ≈ᴸ-refl
  ≈ᶠ-refl {εᶠ} =  _

  ≈ᶠ-sym :  x ≈ᶠ y →  y ≈ᶠ x
  ≈ᶠ-sym {⟨ p ⟩ᶠᴸ _} {⟨ q ⟩ᶠᴸ _} (p≈q , as≈bs) =
    ≈ᴿ⁺-sym {p} {q} p≈q , ≈ᴸ-sym as≈bs
  ≈ᶠ-sym {εᶠ} {εᶠ} _ =  _

  ≈ᶠ-trans :  x ≈ᶠ y →  y ≈ᶠ z →  x ≈ᶠ z
  ≈ᶠ-trans {⟨ p ⟩ᶠᴸ _} {⟨ q ⟩ᶠᴸ _} {⟨ r ⟩ᶠᴸ _} (p≈q , as≈bs) (q≈r , bs≈cs) =
    ≈ᴿ⁺-trans {p} {q} {r} p≈q q≈r , ≈ᴸ-trans as≈bs bs≈cs
  ≈ᶠ-trans {εᶠ} {εᶠ} {εᶠ} _ _ =  _

  ∙ᶠ-congˡ :  ∀ x y z →  x ≈ᶠ y →  x ∙ᶠ z  ≈ᶠ  y ∙ᶠ z
  ∙ᶠ-congˡ (⟨ p ⟩ᶠᴸ _) (⟨ q ⟩ᶠᴸ _) (⟨ r ⟩ᶠᴸ _) (p≈q , as≈bs) =
    +ᴿ⁺-congˡ {p} {q} {r} p≈q , ++-congˡ as≈bs
  ∙ᶠ-congˡ (⟨ _ ⟩ᶠᴸ _) (⟨ _ ⟩ᶠᴸ _) εᶠ x≈y =  x≈y
  ∙ᶠ-congˡ εᶠ εᶠ _ _ =  ≈ᶠ-refl

  ∙ᶠ-comm :  ∀ x y →  x ∙ᶠ y  ≈ᶠ  y ∙ᶠ x
  ∙ᶠ-comm εᶠ y@(⟨ _ ⟩ᶠᴸ _) =  ≈ᶠ-refl {y}
  ∙ᶠ-comm x@(⟨ _ ⟩ᶠᴸ _) εᶠ =  ≈ᶠ-refl {x}
  ∙ᶠ-comm εᶠ εᶠ =  ≈ᶠ-refl
  ∙ᶠ-comm (⟨ p ⟩ᶠᴸ as) (⟨ q ⟩ᶠᴸ bs) =
    ≡⇒≈ᴿ⁺ (+ᴿ⁺-comm {p} {q}) , ++-comm {as} {bs}

  ∙ᶠ-assocˡ :  ∀ x y z →  (x ∙ᶠ y) ∙ᶠ z  ≈ᶠ  x ∙ᶠ (y ∙ᶠ z)
  ∙ᶠ-assocˡ (⟨ p ⟩ᶠᴸ as) (⟨ q ⟩ᶠᴸ _) (⟨ r ⟩ᶠᴸ _) =
    ≡⇒≈ᴿ⁺ (+ᴿ⁺-assocˡ {p} {q} {r}) , ≡⇒≈ᴸ (++-assocˡ {as = as})
  ∙ᶠ-assocˡ εᶠ _ _ =  ≈ᶠ-refl
  ∙ᶠ-assocˡ (⟨ _ ⟩ᶠᴸ _) εᶠ _ =  ≈ᶠ-refl
  ∙ᶠ-assocˡ x@(⟨ _ ⟩ᶠᴸ _) y@(⟨ _ ⟩ᶠᴸ _) εᶠ =  ≈ᶠ-refl {x ∙ᶠ y}

  ✓ᶠ-resp :  ∀ x y →  x ≈ᶠ y →  ✓ᶠ x →  ✓ᶠ y
  ✓ᶠ-resp (⟨ _ ⟩ᶠᴸ _) (⟨ _ ⟩ᶠᴸ _) (p≈q , as≈bs) (p≤1 , homo'as) =
    ≤1ᴿ⁺-resp p≈q p≤1 , homo-resp as≈bs homo'as
  ✓ᶠ-resp εᶠ εᶠ _ _ =  _

  ✓ᶠ-rem :  ∀ x y →  ✓ᶠ x ∙ᶠ y →  ✓ᶠ y
  ✓ᶠ-rem (⟨ p ⟩ᶠᴸ _) (⟨ q ⟩ᶠᴸ _) (p+q≤1 , homo'as++bs) =
    ≤1ᴿ⁺-rem {p} p+q≤1 , homo-mono ++-⊆ᴸ-introʳ homo'as++bs
  ✓ᶠ-rem _ εᶠ _ =  _
  ✓ᶠ-rem εᶠ (⟨ _ ⟩ᶠᴸ _) ✓x =  ✓x

--------------------------------------------------------------------------------
-- FrAgᴿᴬ : Fractional resource algebra

module _ where
  open RA

  FrAgᴿᴬ : RA ℓ (ℓ ⌴ ℓ≈) (ℓ ⌴ ℓ≈)
  FrAgᴿᴬ .Car =  FrAg
  FrAgᴿᴬ ._≈_ =  _≈ᶠ_
  FrAgᴿᴬ .✓_ =  ✓ᶠ_
  FrAgᴿᴬ ._∙_ =  _∙ᶠ_
  FrAgᴿᴬ .ε =  εᶠ
  FrAgᴿᴬ .⌞_⌟ _ =  εᶠ
  FrAgᴿᴬ .refl˜ =  ≈ᶠ-refl
  FrAgᴿᴬ .sym˜ =  ≈ᶠ-sym
  FrAgᴿᴬ ._»˜_ =  ≈ᶠ-trans
  FrAgᴿᴬ .∙-congˡ =  ∙ᶠ-congˡ _ _ _
  FrAgᴿᴬ .∙-unitˡ =  ≈ᶠ-refl
  FrAgᴿᴬ .∙-comm {x} =  ∙ᶠ-comm x _
  FrAgᴿᴬ .∙-assocˡ {x} =  ∙ᶠ-assocˡ x _ _
  FrAgᴿᴬ .✓-resp =  ✓ᶠ-resp _ _
  FrAgᴿᴬ .✓-rem {x} =  ✓ᶠ-rem x _
  FrAgᴿᴬ .✓-ε =  _
  FrAgᴿᴬ .⌞⌟-cong _ =  ≈ᶠ-refl
  FrAgᴿᴬ .⌞⌟-add =  εᶠ , ≈ᶠ-refl
  FrAgᴿᴬ .⌞⌟-unitˡ =  ≈ᶠ-refl
  FrAgᴿᴬ .⌞⌟-idem =  ≈ᶠ-refl

open RA FrAgᴿᴬ using (_∙_; ✓_; _↝_)

--------------------------------------------------------------------------------
-- Lemmas

abstract

  -- Congruence on ⟨ ⟩ᶠ

  ⟨⟩ᶠ-cong :  p ≈ᴿ⁺ q →  a ≈ b →  ⟨ p ⟩ᶠ a ≈ᶠ ⟨ q ⟩ᶠ b
  ⟨⟩ᶠ-cong p≈q a≈b =  p≈q , [?]-cong a≈b

  ⟨⟩ᶠ-congˡ :  p ≈ᴿ⁺ q →  ⟨ p ⟩ᶠ a ≈ᶠ ⟨ q ⟩ᶠ a
  ⟨⟩ᶠ-congˡ {p} {q} p≈q =  ⟨⟩ᶠ-cong {p} {q} p≈q refl˜

  ⟨⟩ᶠ-congʳ :  ∀ {p a b} →  a ≈ b →  ⟨ p ⟩ᶠ a ≈ᶠ ⟨ p ⟩ᶠ b
  ⟨⟩ᶠ-congʳ {p} a≈b =  ⟨⟩ᶠ-cong {p} {p} (≈ᴿ⁺-refl {p}) a≈b

  -- ⟨ p ⟩ᶠ a is valid for p ≤1ᴿ⁺

  ✓-⟨⟩ᶠ :  p ≤1ᴿ⁺ →  ✓ ⟨ p ⟩ᶠ a
  ✓-⟨⟩ᶠ p≤1 =  p≤1 , homo-[?]

  -- ⟨ 1ᴿ⁺ ⟩ᶠ a is valid

  ✓-⟨1⟩ᶠ :  ✓ ⟨ 1ᴿ⁺ ⟩ᶠ a
  ✓-⟨1⟩ᶠ =  ✓-⟨⟩ᶠ 1≤1ᴿ⁺

  -- Joining ⟨ ⟩ᶠ

  join-⟨⟩ᶠ : ∀ {p q a} →  ⟨ p ⟩ᶠ a ∙ ⟨ q ⟩ᶠ a ≈ᶠ ⟨ p +ᴿ⁺ q ⟩ᶠ a
  join-⟨⟩ᶠ {p} {q} =  ≈ᴿ⁺-refl {p +ᴿ⁺ q} , ++-idem

  -- Agreement

  agreeᶠ :  ✓ ⟨ p ⟩ᶠ a ∙ ⟨ q ⟩ᶠ b →  a ≈ b
  agreeᶠ (_ , homo'ab) =  homo-agree homo'ab

  -- Update

  updateᶠ :  ⟨ 1ᴿ⁺ ⟩ᶠ a ↝ ⟨ 1ᴿ⁺ ⟩ᶠ b
  updateᶠ εᶠ _ =  ✓-⟨1⟩ᶠ
  updateᶠ (⟨ p ⟩ᶠᴸ _) (p+1≤1 , _) =  absurd $ ?+1-not-≤1ᴿ⁺ {p} p+1≤1
