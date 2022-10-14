--------------------------------------------------------------------------------
-- Fractional Agreement ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Syho.Model.ERA.FracAg where

open import Base.Level using (Level)
open import Base.Func using (_$_; _›_)
open import Base.Few using (⊤; ⊥; absurd)
open import Base.Eq using (_≡_; refl)
open import Base.Option using (¿_; š_; ň)
open import Base.Prod using (_×_; _,_; -,_; _,-)
open import Base.List using (List; _∷_; []; _⧺_; [_]; _≈ᴸ_; ⧺-assocˡ; ∈ʰᵈ;
  ∈ᵗˡ_; ≈ᴸ-refl; ≡⇒≈ᴸ; ≈ᴸ-sym; ≈ᴸ-trans; ⧺-congˡ; ⧺-comm; ⧺-idem)
open import Base.Ratp using (ℚ⁺; 1ᴿ⁺; _≈ᴿ⁺_; _≤1ᴿ⁺; _+ᴿ⁺_; ≈ᴿ⁺-refl; ≡⇒≈ᴿ⁺;
  ≈ᴿ⁺-sym; ≈ᴿ⁺-trans; ≤1ᴿ⁺-resp; ≤1ᴿ⁺-rem; +ᴿ⁺-congˡ; +ᴿ⁺-comm; +ᴿ⁺-assocˡ;
  1≤1ᴿ⁺; ¬1+?≤1ᴿ⁺)
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Ag using (_✓ᴸ_; ✓ᴸ-resp; ✓ᴸ-rem; ✓ᴸ-š-[?]; ✓ᴸ-agree)

open ERA using (Res; _≈_; _∙_; ε; ⌞_⌟; Env; _✓_; refl˜; ◠˜_; _◇˜_; ∙-congˡ;
  ∙-unitˡ; ∙-comm; ∙-assocˡ; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem; ✓-resp; ✓-rem)

private variable
  ł :  Level
  A :  Set ł
  a b c :  A
  aˇ :  ¿ A
  bs ds :  List A
  p q :  ℚ⁺

--------------------------------------------------------------------------------
-- FracAg A :  Fractional agreement box, which is either empty or a pair of a
--             positive fraction ℚ⁺ and a finite set List A

FracAg :  Set ł →  Set ł
FracAg A =  ¿ (ℚ⁺ × List A)

private variable
  x y z :  FracAg A

-- ≈ᶠʳ :  Equivalence of FracAg A

infix 4 _≈ᶠʳ_
_≈ᶠʳ_ :  ∀{A : Set ł} →  FracAg A →  FracAg A →  Set ł
š (p , as) ≈ᶠʳ š (q , bs) =  p ≈ᴿ⁺ q  ×  as ≈ᴸ bs
ň ≈ᶠʳ ň =  ⊤
_ ≈ᶠʳ _ =  ⊥

-- ∙ᶠʳ :  Product over FracAg A

infixl 7 _∙ᶠʳ_
_∙ᶠʳ_ :  FracAg A →  FracAg A →  FracAg A
ň ∙ᶠʳ y =  y
x ∙ᶠʳ ň =  x
š (p , as) ∙ᶠʳ š (q , bs) =  š (p +ᴿ⁺ q , as ⧺ bs)

-- ✓ᶠʳ :  Agreement between ¿ A and FracAg A, with validity of the fraction

infix 3 _✓ᶠʳ_
_✓ᶠʳ_ :  ∀{A : Set ł} →  ¿ A →  FracAg A →  Set ł
_ ✓ᶠʳ ň =  ⊤
ň ✓ᶠʳ š _ =  ⊥
š a ✓ᶠʳ š (p , bs) =  p ≤1ᴿ⁺  ×  š a ✓ᴸ bs

abstract

  -- ≈ᶠʳ is reflexive

  ≈ᶠʳ-refl :  x ≈ᶠʳ x
  ≈ᶠʳ-refl {x = š (p ,-)} =  ≈ᴿ⁺-refl {p} , ≈ᴸ-refl
  ≈ᶠʳ-refl {x = ň} =  _

  -- ≈ᶠʳ is symmetric

  ≈ᶠʳ-sym :  x ≈ᶠʳ y →  y ≈ᶠʳ x
  ≈ᶠʳ-sym {x = š (p ,-)} {š (q ,-)} (p≈q , as≈bs) =
    ≈ᴿ⁺-sym {p} {q} p≈q , ≈ᴸ-sym as≈bs
  ≈ᶠʳ-sym {x = ň} {ň} _ =  _

  -- ≈ᶠʳ is transitive

  ≈ᶠʳ-trans :  x ≈ᶠʳ y →  y ≈ᶠʳ z →  x ≈ᶠʳ z
  ≈ᶠʳ-trans {x = š (p ,-)} {š (q ,-)} {š (r ,-)} (p≈q , as≈bs) (q≈r , bs≈cs)
    = ≈ᴿ⁺-trans {p} {q} {r} p≈q q≈r , ≈ᴸ-trans as≈bs bs≈cs
  ≈ᶠʳ-trans {x = ň} {ň} {ň} _ _ =  _

  -- ∙ᶠʳ preserves ≈ᶠʳ

  ∙ᶠʳ-congˡ :  x ≈ᶠʳ y →  x ∙ᶠʳ z  ≈ᶠʳ  y ∙ᶠʳ z
  ∙ᶠʳ-congˡ {x = š (p ,-)} {š (q ,-)} {š (r ,-)} (p≈q , as≈bs) =
    +ᴿ⁺-congˡ {p} {q} {r} p≈q , ⧺-congˡ as≈bs
  ∙ᶠʳ-congˡ {x = š _} {š _} {ň} x≈y =  x≈y
  ∙ᶠʳ-congˡ {x = ň} {ň} _ =  ≈ᶠʳ-refl

  -- ∙ᶠʳ is commutative w.r.t. ≈ᶠʳ

  ∙ᶠʳ-comm :  x ∙ᶠʳ y  ≈ᶠʳ  y ∙ᶠʳ x
  ∙ᶠʳ-comm {x = š (p , as)} {š (q , bs)} =
    ≡⇒≈ᴿ⁺ $ +ᴿ⁺-comm {p} {q} , ⧺-comm {as = as}
  ∙ᶠʳ-comm {x = ň} {y@(š _)} =  ≈ᶠʳ-refl {x = y}
  ∙ᶠʳ-comm {x = x@(š _)} {ň} =  ≈ᶠʳ-refl {x = x}
  ∙ᶠʳ-comm {x = ň} {ň} =  _

  -- ∙ᶠʳ is associative w.r.t. ≈ᶠʳ

  ∙ᶠʳ-assocˡ :  (x ∙ᶠʳ y) ∙ᶠʳ z  ≈ᶠʳ  x ∙ᶠʳ (y ∙ᶠʳ z)
  ∙ᶠʳ-assocˡ {x = š (p , as)} {š (q ,-)} {š (r ,-)} =
    ≡⇒≈ᴿ⁺ $ +ᴿ⁺-assocˡ {p} {q} {r} , ≡⇒≈ᴸ $ ⧺-assocˡ {as = as}
  ∙ᶠʳ-assocˡ {x = ň} =  ≈ᶠʳ-refl
  ∙ᶠʳ-assocˡ {x = š _} {ň} =  ≈ᶠʳ-refl
  ∙ᶠʳ-assocˡ {x = x@(š _)} {y@(š _)} {ň} =  ≈ᶠʳ-refl {x = x ∙ᶠʳ y}

  -- ∙ᶠʳ on š (- , [ - ])

  š[?]-∙ᶠʳ :  š (p , [ a ]) ∙ᶠʳ š (q , [ a ])  ≈ᶠʳ  š (p +ᴿ⁺ q , [ a ])
  š[?]-∙ᶠʳ {p = p} {q = q} =  ≈ᴿ⁺-refl {p = p +ᴿ⁺ q} , ⧺-idem {as = [ _ ]}

  -- ✓ᶠʳ respects ≈ᶠʳ

  ✓ᶠʳ-resp :  x ≈ᶠʳ y →  aˇ ✓ᶠʳ x →  aˇ ✓ᶠʳ y
  ✓ᶠʳ-resp {x = ň} {ň} _ _ =  _
  ✓ᶠʳ-resp {x = š (p ,-)} {š (q ,-)} {š _} (p≈q , bs≈cs) (p≤1 , aˇ✓bs) =
    ≤1ᴿ⁺-resp {p} {q} p≈q p≤1 , ✓ᴸ-resp bs≈cs aˇ✓bs

  -- ✓ᶠʳ is preserved by removal w.r.t. ∙ᶠʳ

  ✓ᶠʳ-rem :  aˇ ✓ᶠʳ x ∙ᶠʳ y →  aˇ ✓ᶠʳ y
  ✓ᶠʳ-rem {x = ň} aˇ✓y =  aˇ✓y
  ✓ᶠʳ-rem {x = š _} {ň} _ =  _
  ✓ᶠʳ-rem {aˇ = š _} {š (p ,-)} {š (q ,-)} (p+q≤1 , aˇ✓bs⧺cs) =
    ≤1ᴿ⁺-rem {p} {q} p+q≤1 , ✓ᴸ-rem aˇ✓bs⧺cs

  -- ✓ᶠʳ š (p , as) implies p ≤1ᴿ⁺

  ✓ᶠʳ-≤1 :   aˇ ✓ᶠʳ š (p , bs) →  p ≤1ᴿ⁺
  ✓ᶠʳ-≤1 {aˇ = š _} (p≤1 ,-) =  p≤1

  -- Update ň into š a and ň into š (1ᴿ⁺ , [ a ]), preserving ✓ᶠʳ - ∙ᶠʳ x

  ✓ᶠʳ-new :  ň ✓ᶠʳ x →  š a ✓ᶠʳ š (1ᴿ⁺ , [ a ]) ∙ᶠʳ x
  ✓ᶠʳ-new {x = ň} _ =  1≤1ᴿ⁺ , ✓ᴸ-š-[?]

  -- Agreement from ✓ᶠʳ š (p , [ - ]) ∙ᶠʳ x

  ✓ᶠʳ-agree :  aˇ ✓ᶠʳ š (p , [ b ]) ∙ᶠʳ x →  aˇ ≡ š b
  ✓ᶠʳ-agree {aˇ = š _} {x = ň} (-, aˇ✓[b]) =  ✓ᴸ-agree aˇ✓[b]
  ✓ᶠʳ-agree {aˇ = š _} {x = š _} (-, aˇ✓⧺[b]) =  ✓ᴸ-agree aˇ✓⧺[b]

  -- Agreement between the first two elements of a list

  ✓ᶠʳ-agree2 :  aˇ ✓ᶠʳ š (p , b ∷ c ∷ ds) →  b ≡ c
  ✓ᶠʳ-agree2 {aˇ = š _} (-, aˇ✓b∷c∷)  with aˇ✓b∷c∷ _ ∈ʰᵈ | aˇ✓b∷c∷ _ (∈ᵗˡ ∈ʰᵈ)
  … | refl | refl =  refl

  -- Update aˇ into ň and š (1ᴿ⁺ , bs) into ň, preserving ✓ᶠʳ - ∙ᶠʳ x

  ✓ᶠʳ-free :  aˇ ✓ᶠʳ š (1ᴿ⁺ , bs) ∙ᶠʳ x →  ň ✓ᶠʳ x
  ✓ᶠʳ-free {x = ň} _ =  _
  ✓ᶠʳ-free {aˇ = š _} {x = š (p ,-)} (1+p≤1 ,-) =  absurd $ ¬1+?≤1ᴿ⁺ {p} 1+p≤1

  -- Update aˇ into š c and š (1ᴿ⁺ , bs) into š (1ᴿ⁺ , [ c ]),
  -- preserving ✓ᶠʳ - ∙ᶠʳ x

  ✓ᶠʳ-update :  aˇ ✓ᶠʳ š (1ᴿ⁺ , bs) ∙ᶠʳ x  →  š c ✓ᶠʳ š (1ᴿ⁺ , [ c ]) ∙ᶠʳ x
  ✓ᶠʳ-update {x = x} =  ✓ᶠʳ-free {x = x} › ✓ᶠʳ-new {x = x}

--------------------------------------------------------------------------------
-- FracAgᴱᴿᴬ :  Fractional agreement ERA

FracAgᴱᴿᴬ :  Set ł →  ERA ł ł ł ł
FracAgᴱᴿᴬ A .Res =  FracAg A
FracAgᴱᴿᴬ _ ._≈_ =  _≈ᶠʳ_
FracAgᴱᴿᴬ _ ._∙_ =  _∙ᶠʳ_
FracAgᴱᴿᴬ _ .ε =  ň
FracAgᴱᴿᴬ _ .⌞_⌟ _ =  ň
FracAgᴱᴿᴬ A .Env =  ¿ A
FracAgᴱᴿᴬ _ ._✓_ =  _✓ᶠʳ_
FracAgᴱᴿᴬ _ .refl˜ =  ≈ᶠʳ-refl
FracAgᴱᴿᴬ _ .◠˜_ =  ≈ᶠʳ-sym
FracAgᴱᴿᴬ _ ._◇˜_ =  ≈ᶠʳ-trans
FracAgᴱᴿᴬ _ .∙-congˡ =  ∙ᶠʳ-congˡ
FracAgᴱᴿᴬ _ .∙-unitˡ =  ≈ᶠʳ-refl
FracAgᴱᴿᴬ _ .∙-comm {a = x} =  ∙ᶠʳ-comm {x = x}
FracAgᴱᴿᴬ _ .∙-assocˡ {a = x} =  ∙ᶠʳ-assocˡ {x = x}
FracAgᴱᴿᴬ _ .⌞⌟-cong _ =  _
FracAgᴱᴿᴬ _ .⌞⌟-add =  ň ,-
FracAgᴱᴿᴬ _ .⌞⌟-unitˡ =  ≈ᶠʳ-refl
FracAgᴱᴿᴬ _ .⌞⌟-idem =  _
FracAgᴱᴿᴬ _ .✓-resp =  ✓ᶠʳ-resp
FracAgᴱᴿᴬ _ .✓-rem {a = x} =  ✓ᶠʳ-rem {x = x}
