--------------------------------------------------------------------------------
-- Finite-map resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Shog.Model.RA using (RA)
module Shog.Model.RA.Fin {ℓ ℓ≈ ℓ✓} (Ra : RA ℓ ℓ≈ ℓ✓) where

open RA Ra using () renaming (Car to A; _≈_ to _≈'_; ✓_ to ✓'_; _∙_ to _∙'_;
  ε to ε'; ⌞_⌟ to ⌞_⌟'; refl˜ to refl'; sym˜ to sym'; _»˜_ to _»'_)

open import Base.Level using (_⊔ˡ_)
open import Base.Nat using (ℕ)
open import Base.Setoid using (≡-setoid)
open import Base.Prod using (Σ-syntax; _,_; proj₀; proj₁)
open import Base.Func using (_$_)
open import Base.List using (List; []; _++_)
open import Base.List.Set (≡-setoid ℕ) using (_∉ᴸ_; ∉ᴸ-[];
  ∉ᴸ-++-elim₀; ∉ᴸ-++-elim₁)

--------------------------------------------------------------------------------
-- Fin : Finᴿᴬ's carrier

record  Fin :  Set (ℓ ⊔ˡ ℓ≈)  where
  field
    fin :  ℕ → A
    supp :  List ℕ
    out-ε :  ∀ {i} →  i ∉ᴸ supp →  fin i ≈' ε'
open Fin

--------------------------------------------------------------------------------
-- Internal definitions
private
  open RA

  -- Equivalence
  infix 4 _≈ᶠ_
  _≈ᶠ_ :  Fin →  Fin →  Set ℓ≈
  F ≈ᶠ G =  ∀ i →  F .fin i ≈' G .fin i

  -- Validity
  infix 3 ✓ᶠ_
  ✓ᶠ_ :  Fin →  Set ℓ✓
  ✓ᶠ F =  ∀ i →  ✓' (F .fin i)

  -- Product
  infixl 7 _∙ᶠ_
  _∙ᶠ_ :  Fin →  Fin →  Fin
  (F ∙ᶠ G) .fin i =  F .fin i ∙' G .fin i
  (F ∙ᶠ G) .supp =  F .supp ++ G .supp
  (F ∙ᶠ G) .out-ε i∉++ =
    ∙-cong Ra (F .out-ε (∉ᴸ-++-elim₀ i∉++)) (G .out-ε (∉ᴸ-++-elim₁ i∉++)) »'
    ∙-unitˡ Ra

  -- Unit
  εᶠ :  Fin
  εᶠ .fin i =  ε'
  εᶠ .supp =  []
  εᶠ .out-ε _ =  refl'

  -- Core
  ⌞_⌟ᶠ :  Fin →  Fin
  ⌞ F ⌟ᶠ .fin i =  ⌞ F .fin i ⌟'
  ⌞ F ⌟ᶠ .supp =  F .supp
  ⌞ F ⌟ᶠ .out-ε i∉ =  ⌞⌟-cong Ra (F .out-ε i∉) »' ⌞⌟-ε Ra

-- Internal lemma
private abstract
  open RA

  ⌞⌟ᶠ-add :  ∀ F G →  Σ G' ,  G' ∙ᶠ ⌞ F ⌟ᶠ ≈ᶠ ⌞ G ∙ᶠ F ⌟ᶠ
  ⌞⌟ᶠ-add F G .proj₀ .fin i =  Ra .⌞⌟-add {F .fin i} {G .fin i} .proj₀
  ⌞⌟ᶠ-add F G .proj₀ .supp =  (G ∙ᶠ F) .supp
  ⌞⌟ᶠ-add F G .proj₀ .out-ε {i} i∉ =  sym' (∙-unitʳ Ra) »'
    ∙-congʳ Ra (sym' $ (Ra .⌞⌟-cong $ F .out-ε $ ∉ᴸ-++-elim₁ i∉) »' ⌞⌟-ε Ra) »'
    Ra .⌞⌟-add {F .fin i} {G .fin i} .proj₁ »'
    Ra .⌞⌟-cong ((G ∙ᶠ F) .out-ε i∉) »' ⌞⌟-ε Ra
  ⌞⌟ᶠ-add F G .proj₁ i =  Ra .⌞⌟-add {F .fin i} {G .fin i} .proj₁

--------------------------------------------------------------------------------
-- Finᴿᴬ : Finite-map resource algebra

module _ where
  open RA

  Finᴿᴬ : RA (ℓ ⊔ˡ ℓ≈) ℓ≈ ℓ✓
  Finᴿᴬ .Car =  Fin
  Finᴿᴬ ._≈_ =  _≈ᶠ_
  Finᴿᴬ .✓_ =  ✓ᶠ_
  Finᴿᴬ ._∙_ =  _∙ᶠ_
  Finᴿᴬ .ε =  εᶠ
  Finᴿᴬ .⌞_⌟ =  ⌞_⌟ᶠ
  Finᴿᴬ .refl˜ _ =  refl'
  Finᴿᴬ .sym˜ F≈G i =  sym' (F≈G i)
  Finᴿᴬ ._»˜_ F≈G G≈H i =  F≈G i »' G≈H i
  Finᴿᴬ .∙-congˡ F≈G i =  Ra .∙-congˡ (F≈G i)
  Finᴿᴬ .∙-unitˡ i =  Ra .∙-unitˡ
  Finᴿᴬ .∙-comm i =  Ra .∙-comm
  Finᴿᴬ .∙-assocˡ i =  Ra .∙-assocˡ
  Finᴿᴬ .✓-resp F≈G ✓F i =  Ra .✓-resp (F≈G i) (✓F i)
  Finᴿᴬ .✓-rem ✓F∙G i =  Ra .✓-rem (✓F∙G i)
  Finᴿᴬ .✓-ε i =  Ra .✓-ε
  Finᴿᴬ .⌞⌟-cong F≈G i =  Ra .⌞⌟-cong (F≈G i)
  Finᴿᴬ .⌞⌟-add {F} {G} =  ⌞⌟ᶠ-add F G
  Finᴿᴬ .⌞⌟-unitˡ i =  Ra .⌞⌟-unitˡ
  Finᴿᴬ .⌞⌟-idem i =  Ra .⌞⌟-idem
