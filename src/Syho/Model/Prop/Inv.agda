--------------------------------------------------------------------------------
-- General invariant builder
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Inv where

open import Base.Level using (Level; _⊔ᴸ_; 2ᴸ)
open import Base.Func using (_$_; _›_)
open import Base.Few using (absurd)
open import Base.Eq using (_≡_; refl)
open import Base.Option using (¿_; š_; ň)
open import Base.Dec using (yes; no; _≡?_; ≡?-refl; upd˙)
open import Base.Nat using (ℕ; ṡ_; _≥_; _<_; _<ᵈ_; ≤-refl; <⇒≤; <-irrefl;
  ≤ᵈ-refl; ≤ᵈṡ; ≤ᵈ⇒≤; ≤⇒≤ᵈ)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨_; ⊨_; ⊤ᵒ; _∗ᵒ_;
  ∗ᵒ-Mono; ∗ᵒ-monoʳ; ?∗ᵒ-comm)

private variable
  ł :  Level
  X Y :  Set ł
  F :  X → Propᵒ ł
  i n :  ℕ
  xˇ˙ yˇ˙ :  ℕ → ¿ X
  xˇ :  ¿ X
  x y :  X

--------------------------------------------------------------------------------
-- Invᵍ :  General invariant bulder

abstract

  -- Invᵍ F xˇ˙ n :  xˇ˙ i interpreted with F, over all i < n

  Invᵍ :  (X → Propᵒ ł) →  (ℕ → ¿ X) →  ℕ →  Propᵒ (2ᴸ ⊔ᴸ ł)
  Invᵍ F xˇ˙ 0 =  ⊤ᵒ
  Invᵍ F xˇ˙ (ṡ n)  with xˇ˙ n
  … | ň =  Invᵍ F xˇ˙ n
  … | š y =  F y ∗ᵒ Invᵍ F xˇ˙ n

  -- Monoᵒ for Invᵍ

  Invᵍ-Mono :  Monoᵒ $ Invᵍ F xˇ˙ n
  Invᵍ-Mono {n = 0} =  _
  Invᵍ-Mono {xˇ˙ = xˇ˙} {ṡ n'}  with xˇ˙ n'
  … | ň =  Invᵍ-Mono {n = n'}
  … | š _ =  ∗ᵒ-Mono

  -- Get Invᵍ _ _ 0 for free

  Invᵍ-0 :  ⊨ Invᵍ F xˇ˙ 0
  Invᵍ-0 =  _

  -- Update an element for Invᵍ out of the bound

  Invᵍ-⇒upd-≥ :  i ≥ n →  Invᵍ F yˇ˙ n  ⊨  Invᵍ F (upd˙ i xˇ yˇ˙) n
  Invᵍ-⇒upd-≥ {_} {0} =  _
  Invᵍ-⇒upd-≥ {i} {ṡ n'} {yˇ˙ = yˇ˙} i>n'  with n' ≡? i
  … | yes refl =  absurd $ <-irrefl i>n'
  … | no _  with yˇ˙ n'
  …   | š _ =  ∗ᵒ-monoʳ $ Invᵍ-⇒upd-≥ $ <⇒≤ i>n'
  …   | ň =  Invᵍ-⇒upd-≥ $ <⇒≤ i>n'

  -- Add a new element to Invᵍ at the bound

  Invᵍ-add-š :  F x ∗ᵒ Invᵍ F yˇ˙ n  ⊨  Invᵍ F (upd˙ n (š x) yˇ˙) (ṡ n)
  Invᵍ-add-š {n = n}  rewrite ≡?-refl {a = n} =
    ∗ᵒ-monoʳ $ Invᵍ-⇒upd-≥ $ ≤-refl {n}

  Invᵍ-add-ň :  Invᵍ F xˇ˙ n  ⊨  Invᵍ F (upd˙ n ň xˇ˙) (ṡ n)
  Invᵍ-add-ň {n = n}  rewrite ≡?-refl {a = n} =  Invᵍ-⇒upd-≥ $ ≤-refl {n}

  -- Take out an element within the bound from Invᵍ

  Invᵍ-rem-<ᵈ :  xˇ˙ i ≡ š y →  i <ᵈ n →
    Invᵍ F xˇ˙ n  ⊨  F y ∗ᵒ Invᵍ F (upd˙ i ň xˇ˙) n
  Invᵍ-rem-<ᵈ {i = i} xˇi≡šy ≤ᵈ-refl  rewrite xˇi≡šy =
    ∗ᵒ-monoʳ (Invᵍ-add-ň {n = i})
  Invᵍ-rem-<ᵈ {xˇ˙ = xˇ˙} {i} xˇi≡šy (≤ᵈṡ {n = n'} i<ᵈn')  with n' ≡? i
  … | yes refl =  absurd $ <-irrefl $ ≤ᵈ⇒≤ i<ᵈn'
  … | no _  with xˇ˙ n'
  …   | ň =  Invᵍ-rem-<ᵈ xˇi≡šy i<ᵈn'
  …   | š _ =  ∗ᵒ-monoʳ (Invᵍ-rem-<ᵈ xˇi≡šy i<ᵈn') › ?∗ᵒ-comm

  Invᵍ-rem-< :  xˇ˙ i ≡ š y →  i < n →
    Invᵍ F xˇ˙ n  ⊨  F y ∗ᵒ Invᵍ F (upd˙ i ň xˇ˙) n
  Invᵍ-rem-< xˇi≡šy =  ≤⇒≤ᵈ › Invᵍ-rem-<ᵈ xˇi≡šy
