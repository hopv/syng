--------------------------------------------------------------------------------
-- On FracAgRA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Setoid using (Setoid)
module Shog.Model.RA.FracAg.More {ℓ ℓ≈} {S : Setoid ℓ ℓ≈} where
open Setoid S using (_≈_; refl˜) renaming (Car to A)

open import Base.RatPos using (ℚ⁺; _≈ᴿ⁺_; _+ᴿ⁺_; _≤1ᴿ⁺; 1ᴿ⁺; ≈ᴿ⁺-refl; 1≤1ᴿ⁺;
  ?+1-not-≤1ᴿ⁺)
open import Base.List.Set S using ([?]-cong; ++-idem; homo-[?]; homo-agree)
open import Base.Prod using (_,_)
open import Base.Few using (absurd)
open import Base.Func using (_$_)
open import Shog.Model.RA using (RA)
open import Shog.Model.RA.FracAg S using (FracAgRA; ⟨_⟩ᶠ_; ⟨_⟩ᶠᴸ_; εᶠ)
open RA FracAgRA using (_∙_; ✓_; _↝_) renaming (_≈_ to _≈ᶠ_)

private variable
  p q :  ℚ⁺
  a b :  A

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
