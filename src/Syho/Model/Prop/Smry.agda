--------------------------------------------------------------------------------
-- Map summary
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Smry where

open import Base.Level using (Level; _⊔ᴸ_; 1ᴸ)
open import Base.Func using (_$_; _›_; id)
open import Base.Few using (absurd)
open import Base.Eq using (_≡_; refl; ◠_; subst; _≡˙_; _◇˙_)
open import Base.Dec using (yes; no; _≟_; ≟-refl; upd˙; upd˙-self; upd˙-2)
open import Base.Option using (¿_; š_; ň)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Base.Nat using (ℕ; ṡ_; _≥_; _<_; _<ᵈ_; ≤-refl; <⇒≤; <-irrefl; _<≥_;
  ≤ᵈ-refl; ≤ᵈṡ; ≤ᵈ⇒≤; ≤⇒≤ᵈ)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨_; ⊨_; ⊤ᵒ; _∗ᵒ_;
  ∗ᵒ-Mono; ∗ᵒ-monoʳ; ?∗ᵒ-comm; ∗ᵒ-elimʳ)

private variable
  ł :  Level
  X Y :  Set ł
  F :  ℕ → X → Propᵒ ł
  i n :  ℕ
  xˇ˙ yˇ˙ :  ℕ → ¿ X
  xˇ :  ¿ X
  x y :  X

--------------------------------------------------------------------------------
-- Smry :  Map summary

abstract

  -- Smry F xˇ˙ n :  xˇ˙ i interpreted with F, over all i < n

  Smry :  (ℕ → X → Propᵒ ł) →  (ℕ → ¿ X) →  ℕ →  Propᵒ (1ᴸ ⊔ᴸ ł)
  Smry F xˇ˙ 0 =  ⊤ᵒ
  Smry F xˇ˙ (ṡ n)  with xˇ˙ n
  … | ň =  Smry F xˇ˙ n
  … | š y =  F n y ∗ᵒ Smry F xˇ˙ n

  -- Monoᵒ for Smry

  Smry-Mono :  Monoᵒ $ Smry F xˇ˙ n
  Smry-Mono {n = 0} =  _
  Smry-Mono {xˇ˙ = xˇ˙} {ṡ n'}  with xˇ˙ n'
  … | ň =  Smry-Mono {n = n'}
  … | š _ =  ∗ᵒ-Mono

  -- Update the map of Smry with ≡˙

  Smry-resp :  xˇ˙ ≡˙ yˇ˙  →   Smry F xˇ˙ n  ⊨  Smry F yˇ˙ n
  Smry-resp {n = 0} _ =  id
  Smry-resp {xˇ˙ = xˇ˙} {yˇ˙} {n = ṡ n'} xˇ≡yˇ  with xˇ˙ n' | yˇ˙ n' | xˇ≡yˇ n'
  … | ň | ň | _ =  Smry-resp {n = n'} xˇ≡yˇ
  … | š _ | š _ | refl =  ∗ᵒ-monoʳ $ Smry-resp {n = n'} xˇ≡yˇ

  -- Get Smry _ _ 0 for free

  Smry-0 :  ⊨ Smry F xˇ˙ 0
  Smry-0 =  _

  -- Update an element for Smry out of the bound

  Smry-⇒upd-≥ :  i ≥ n  →   Smry F yˇ˙ n  ⊨  Smry F (upd˙ i xˇ yˇ˙) n
  Smry-⇒upd-≥ {_} {0} =  _
  Smry-⇒upd-≥ {i} {ṡ n'} {yˇ˙ = yˇ˙} i>n'  with n' ≟ i
  … | yes refl =  absurd $ <-irrefl i>n'
  … | no _  with yˇ˙ n'
  …   | š _ =  ∗ᵒ-monoʳ $ Smry-⇒upd-≥ $ <⇒≤ i>n'
  …   | ň =  Smry-⇒upd-≥ $ <⇒≤ i>n'

  -- Add a new element to Smry at the bound

  Smry-add-š :  F n x  ∗ᵒ  Smry F yˇ˙ n  ⊨  Smry F (upd˙ n (š x) yˇ˙) (ṡ n)
  Smry-add-š {n = n}  rewrite ≟-refl {a = n} =
    ∗ᵒ-monoʳ $ Smry-⇒upd-≥ $ ≤-refl {n}

  Smry-add-ň :  Smry F xˇ˙ n  ⊨  Smry F (upd˙ n ň xˇ˙) (ṡ n)
  Smry-add-ň {n = n}  rewrite ≟-refl {a = n} =  Smry-⇒upd-≥ $ ≤-refl {n}

  -- Take out an element within the bound from Smry

  Smry-rem-<ᵈ :  yˇ˙ i ≡ š x  →   i <ᵈ n  →
    Smry F yˇ˙ n  ⊨  F i x  ∗ᵒ  Smry F (upd˙ i ň yˇ˙) n
  Smry-rem-<ᵈ {i = i} yˇi≡šx ≤ᵈ-refl  rewrite yˇi≡šx =
    ∗ᵒ-monoʳ $ Smry-add-ň {n = i}
  Smry-rem-<ᵈ {yˇ˙ = yˇ˙} {i} yˇi≡šx (≤ᵈṡ {n = n'} i<ᵈn')  with n' ≟ i
  … | yes refl =  absurd $ <-irrefl $ ≤ᵈ⇒≤ i<ᵈn'
  … | no _  with yˇ˙ n'
  …   | ň =  Smry-rem-<ᵈ yˇi≡šx i<ᵈn'
  …   | š _ =  ∗ᵒ-monoʳ (Smry-rem-<ᵈ yˇi≡šx i<ᵈn') › ?∗ᵒ-comm

  Smry-rem-< :  yˇ˙ i ≡ š x  →   i < n  →
    Smry F yˇ˙ n  ⊨  F i x  ∗ᵒ  Smry F (upd˙ i ň yˇ˙) n
  Smry-rem-< yˇi≡šx =  ≤⇒≤ᵈ › Smry-rem-<ᵈ yˇi≡šx

  -- Insert an element to Smry

  Smry-ins-<ᵈ :  i <ᵈ n  →
    F i x  ∗ᵒ  Smry F yˇ˙ n  ⊨  Smry F (upd˙ i (š x) yˇ˙) n
  Smry-ins-<ᵈ {i} {yˇ˙ = yˇ˙} ≤ᵈ-refl  with yˇ˙ i
  … | ň =  Smry-add-š {n = i}
  … | š _ =  ∗ᵒ-monoʳ (∗ᵒ-elimʳ $ Smry-Mono {n = i}) › Smry-add-š {n = i}
  Smry-ins-<ᵈ {i} {yˇ˙ = yˇ˙} (≤ᵈṡ {n = n'} i<ᵈn')  with n' ≟ i
  … | yes refl =  absurd $ <-irrefl $ ≤ᵈ⇒≤ i<ᵈn'
  … | no _  with yˇ˙ n'
  …   | ň =  Smry-ins-<ᵈ i<ᵈn'
  …   | š _ =  ?∗ᵒ-comm › ∗ᵒ-monoʳ $ Smry-ins-<ᵈ i<ᵈn'

  Smry-ins-< :  i < n  →
    F i x  ∗ᵒ  Smry F yˇ˙ n  ⊨  Smry F (upd˙ i (š x) yˇ˙) n
  Smry-ins-< =  ≤⇒≤ᵈ › Smry-ins-<ᵈ

  Smry-ins :  F i x  ∗ᵒ  Smry F yˇ˙ n  ⊨  Smry F (upd˙ i (š x) yˇ˙) n
  Smry-ins {i = i} {n = n}  with i <≥ n
  … | ĩ₀ i<n =  Smry-ins-< i<n
  … | ĩ₁ i≥n =  ∗ᵒ-elimʳ (Smry-Mono {n = n}) › Smry-⇒upd-≥ i≥n

  -- Update an element of Smry
  -- It can be used in combination with Smry-rem-<

  Smry-upd :  yˇ˙ i ≡ š x  →
    F i x  ∗ᵒ  Smry F (upd˙ i ň yˇ˙) n  ⊨  Smry F yˇ˙ n
  Smry-upd {yˇ˙ = yˇ˙} {n = n} yˇi≡šx =  Smry-ins {n = n} › Smry-resp {n = n} $
    upd˙-2 ◇˙ subst (λ xˇ → upd˙ _ xˇ yˇ˙ ≡˙ yˇ˙) yˇi≡šx upd˙-self
