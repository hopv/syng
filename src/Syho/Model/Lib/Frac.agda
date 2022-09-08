--------------------------------------------------------------------------------
-- Fractional box
--------------------------------------------------------------------------------

module Syho.Model.Lib.Frac where

open import Base.Level using (Level)
open import Base.Func using (_$_)
open import Base.Few using (⊤; ⊥)
open import Base.Prod using (_×_; _,_)
open import Base.Option using (¿_; š_; ň)
open import Base.List using (List; _⧺_; _≈ᴸ_; ⧺-assocˡ; ≈ᴸ-refl; ≡⇒≈ᴸ; ≈ᴸ-sym;
  ≈ᴸ-trans; ⧺-congˡ; ⧺-comm)
open import Base.RatPos using (ℚ⁺; _≈ᴿ⁺_; _≤1ᴿ⁺; _+ᴿ⁺_; ≈ᴿ⁺-refl; ≡⇒≈ᴿ⁺;
  ≈ᴿ⁺-sym; ≈ᴿ⁺-trans; ≤1ᴿ⁺-resp; ≤1ᴿ⁺-rem; +ᴿ⁺-congˡ; +ᴿ⁺-comm; +ᴿ⁺-assocˡ)

private variable
  ł :  Level
  A :  Set ł

--------------------------------------------------------------------------------
-- Frac A :  Fractional box, which is either empty or a pair of a positive
-- fraction ℚ⁺ and a finite set List A

Frac :  Set ł →  Set ł
Frac A =  ¿ (ℚ⁺ × List A)

private variable
  x y z :  Frac A

-- ≈ᶠʳ :  Equivalence over Frac A

infix 4 _≈ᶠʳ_
_≈ᶠʳ_ :  ∀{A : Set ł} →  Frac A →  Frac A →  Set ł
š (p , as) ≈ᶠʳ š (q , bs) =  p ≈ᴿ⁺ q  ×  as ≈ᴸ bs
ň ≈ᶠʳ ň =  ⊤
_ ≈ᶠʳ _ =  ⊥

-- ✓ᶠʳ :  Validity of Frac A

infix 3 ✓ᶠʳ_
✓ᶠʳ_ :  Frac A →  Set₀
✓ᶠʳ š (p , _) =  p ≤1ᴿ⁺
✓ᶠʳ ň =  ⊤

-- ∙ᶠʳ :  Product over Frac A

infixl 7 _∙ᶠʳ_
_∙ᶠʳ_ :  Frac A →  Frac A →  Frac A
ň ∙ᶠʳ y =  y
x ∙ᶠʳ ň =  x
š (p , as) ∙ᶠʳ š (q , bs) =  š (p +ᴿ⁺ q , as ⧺ bs)

abstract

  -- ≈ᶠʳ is reflexive

  ≈ᶠʳ-refl :  x ≈ᶠʳ x
  ≈ᶠʳ-refl {x = š (p , _)} =  ≈ᴿ⁺-refl {p} , ≈ᴸ-refl
  ≈ᶠʳ-refl {x = ň} =  _

  -- ≈ᶠʳ is symmetric

  ≈ᶠʳ-sym :  x ≈ᶠʳ y →  y ≈ᶠʳ x
  ≈ᶠʳ-sym {x = š (p , _)} {š (q , _)} (p≈q , as≈bs) =
    ≈ᴿ⁺-sym {p} {q} p≈q , ≈ᴸ-sym as≈bs
  ≈ᶠʳ-sym {x = ň} {ň} _ =  _

  -- ≈ᶠʳ is transitive

  ≈ᶠʳ-trans :  x ≈ᶠʳ y →  y ≈ᶠʳ z →  x ≈ᶠʳ z
  ≈ᶠʳ-trans {x = š (p , _)} {š (q , _)} {š (r , _)} (p≈q , as≈bs) (q≈r , bs≈cs)
    = ≈ᴿ⁺-trans {p} {q} {r} p≈q q≈r , ≈ᴸ-trans as≈bs bs≈cs
  ≈ᶠʳ-trans {x = ň} {ň} {ň} _ _ =  _

  -- ✓ᶠʳ respects ≈ᶠʳ

  ✓ᶠʳ-resp :  x ≈ᶠʳ y →  ✓ᶠʳ x →  ✓ᶠʳ y
  ✓ᶠʳ-resp {x = š _} {š _} (p≈q , _) p≤1 =  ≤1ᴿ⁺-resp p≈q p≤1
  ✓ᶠʳ-resp {x = ň} {ň} _ _ =  _

  -- ✓ᶠʳ holds after removing an element with respect to ∙ᶠʳ

  ✓ᶠʳ-rem :  ✓ᶠʳ x ∙ᶠʳ y →  ✓ᶠʳ y
  ✓ᶠʳ-rem {x = š (p , _)} {š (q , _)} p+q≤1 =  ≤1ᴿ⁺-rem {p} p+q≤1
  ✓ᶠʳ-rem {x = ň} ✓y =  ✓y
  ✓ᶠʳ-rem {x = š _} {ň} _ =  _

  -- ∙ᶠʳ preserves ≈ᶠʳ

  ∙ᶠʳ-congˡ :  x ≈ᶠʳ y →  x ∙ᶠʳ z  ≈ᶠʳ  y ∙ᶠʳ z
  ∙ᶠʳ-congˡ {x = š (p , _)} {š (q , _)} {š (r , _)} (p≈q , as≈bs) =
    +ᴿ⁺-congˡ {p} {q} {r} p≈q , ⧺-congˡ as≈bs
  ∙ᶠʳ-congˡ {x = š _} {š _} {ň} x≈y =  x≈y
  ∙ᶠʳ-congˡ {x = ň} {ň} _ =  ≈ᶠʳ-refl

  -- ∙ᶠʳ is commutative with respect to ≈ᶠʳ

  ∙ᶠʳ-comm :  x ∙ᶠʳ y  ≈ᶠʳ  y ∙ᶠʳ x
  ∙ᶠʳ-comm {x = š (p , as)} {š (q , bs)} =
    ≡⇒≈ᴿ⁺ $ +ᴿ⁺-comm {p} {q} , ⧺-comm {as = as}
  ∙ᶠʳ-comm {x = ň} {y@(š _)} =  ≈ᶠʳ-refl {x = y}
  ∙ᶠʳ-comm {x = x@(š _)} {ň} =  ≈ᶠʳ-refl {x = x}
  ∙ᶠʳ-comm {x = ň} {ň} =  _

  -- ∙ᶠʳ is associative with respect to ≈ᶠʳ

  ∙ᶠʳ-assocˡ :  (x ∙ᶠʳ y) ∙ᶠʳ z  ≈ᶠʳ  x ∙ᶠʳ (y ∙ᶠʳ z)
  ∙ᶠʳ-assocˡ {x = š (p , as)} {š (q , _)} {š (r , _)} =
    ≡⇒≈ᴿ⁺ $ +ᴿ⁺-assocˡ {p} {q} {r} , ≡⇒≈ᴸ $ ⧺-assocˡ {as = as}
  ∙ᶠʳ-assocˡ {x = ň} =  ≈ᶠʳ-refl
  ∙ᶠʳ-assocˡ {x = š _} {ň} =  ≈ᶠʳ-refl
  ∙ᶠʳ-assocˡ {x = x@(š _)} {y@(š _)} {ň} =  ≈ᶠʳ-refl {x = x ∙ᶠʳ y}
