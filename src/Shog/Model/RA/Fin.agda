--------------------------------------------------------------------------------
-- Finite-map resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Shog.Model.RA using (RA)
module Shog.Model.RA.Fin {ℓ ℓ≈ ℓ✓} (Ra : RA ℓ ℓ≈ ℓ✓) where

open RA Ra using () renaming (Car to A; _≈_ to _≈'_; ✓_ to ✓'_; _∙_ to _∙'_;
  ε to ε'; ⌞_⌟ to ⌞_⌟'; _↝_ to _↝'_; refl˜ to refl'; ◠˜_ to ◠'_; _◇˜_ to _◇'_;
  ✓-resp to ✓'-resp; ∙-congˡ to ∙'-congˡ; ∙-unitˡ to ∙'-unitˡ)

open import Base.Level using (_⌴_)
open import Base.Bool using (tt; ff)
open import Base.Eq using (_≡_; refl; ◠_)
open import Base.Setoid using (≡-setoid)
open import Base.Func using (_$_; flip)
open import Base.Few using (absurd)
open import Base.Prod using (∑-syntax; _,_; proj₀; proj₁)
open import Base.Nat using (ℕ; suc; _≡ᵇ_; ᵇ⇒≡; ≡⇒ᵇ)
open import Base.Nat.List using ([⊔]; suc[⊔]∉ᴸ)
open import Base.List using (List; _∷_; []; _++_)
open import Base.List.Set (≡-setoid ℕ) using (_∉ᴸ_; ∉ᴸ-[];
  ∉ᴸ-∷-elim₀; ∉ᴸ-∷-elim₁; ∉ᴸ-++-elim₀; ∉ᴸ-++-elim₁)

--------------------------------------------------------------------------------
-- Fin : FinRA's carrier

-- Type of out-ε
Out-ε :  (ℕ → A) → List ℕ → Set ℓ≈
Out-ε fin supp =  ∀ {i} →  i ∉ᴸ supp →  fin i ≈' ε'

record  Fin :  Set (ℓ ⌴ ℓ≈)  where
  field
    fin :  ℕ → A
    supp :  List ℕ
    out-ε :  Out-ε fin supp
open Fin

private variable
  a b : A
  F G : Fin

--------------------------------------------------------------------------------
-- Internal definitions

private module _ where
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
  (F ∙ᶠ G) .out-ε =  proof
   where abstract
    proof :  Out-ε ((F ∙ᶠ G) .fin) ((F ∙ᶠ G) .supp)
    proof i∉++ =
      ∙-cong Ra (F .out-ε (∉ᴸ-++-elim₀ i∉++)) (G .out-ε (∉ᴸ-++-elim₁ i∉++)) ◇'
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
  ⌞ F ⌟ᶠ .out-ε =  proof
   where abstract
    proof :  Out-ε (⌞ F ⌟ᶠ .fin) (⌞ F ⌟ᶠ .supp)
    proof i∉ =  ⌞⌟-cong Ra (F .out-ε i∉) ◇' ⌞⌟-ε Ra

--------------------------------------------------------------------------------
-- Internal lemma

private module _ where abstract
  open RA

  ⌞⌟ᶠ-add :  ∀ F G →  ∑ G' ,  G' ∙ᶠ ⌞ F ⌟ᶠ ≈ᶠ ⌞ G ∙ᶠ F ⌟ᶠ
  ⌞⌟ᶠ-add F G .proj₀ .fin i =  Ra .⌞⌟-add {F .fin i} {G .fin i} .proj₀
  ⌞⌟ᶠ-add F G .proj₀ .supp =  (G ∙ᶠ F) .supp
  ⌞⌟ᶠ-add F G .proj₀ .out-ε {i} i∉ =  ◠' ∙-unitʳ Ra ◇'
    ∙-congʳ Ra (◠'_ $ (Ra .⌞⌟-cong $ F .out-ε $ ∉ᴸ-++-elim₁ i∉) ◇' ⌞⌟-ε Ra) ◇'
    Ra .⌞⌟-add {F .fin i} {G .fin i} .proj₁ ◇'
    Ra .⌞⌟-cong ((G ∙ᶠ F) .out-ε i∉) ◇' ⌞⌟-ε Ra
  ⌞⌟ᶠ-add F G .proj₁ i =  Ra .⌞⌟-add {F .fin i} {G .fin i} .proj₁

--------------------------------------------------------------------------------
-- FinRA : Finite-map resource algebra

module _ where
  open RA

  FinRA : RA (ℓ ⌴ ℓ≈) ℓ≈ ℓ✓
  FinRA .Car =  Fin
  FinRA ._≈_ =  _≈ᶠ_
  FinRA .✓_ =  ✓ᶠ_
  FinRA ._∙_ =  _∙ᶠ_
  FinRA .ε =  εᶠ
  FinRA .⌞_⌟ =  ⌞_⌟ᶠ
  FinRA .refl˜ _ =  refl'
  FinRA .◠˜_ F≈G i =  ◠' F≈G i
  FinRA ._◇˜_ F≈G G≈H i =  F≈G i ◇' G≈H i
  FinRA .∙-congˡ F≈G i =  Ra .∙-congˡ (F≈G i)
  FinRA .∙-unitˡ i =  Ra .∙-unitˡ
  FinRA .∙-comm i =  Ra .∙-comm
  FinRA .∙-assocˡ i =  Ra .∙-assocˡ
  FinRA .✓-resp F≈G ✓F i =  Ra .✓-resp (F≈G i) (✓F i)
  FinRA .✓-rem ✓F∙G i =  Ra .✓-rem (✓F∙G i)
  FinRA .✓-ε i =  Ra .✓-ε
  FinRA .⌞⌟-cong F≈G i =  Ra .⌞⌟-cong (F≈G i)
  FinRA .⌞⌟-add {F} {G} =  ⌞⌟ᶠ-add F G
  FinRA .⌞⌟-unitˡ i =  Ra .⌞⌟-unitˡ
  FinRA .⌞⌟-idem i =  Ra .⌞⌟-idem

open RA FinRA using (_≈_; ✓_; _∙_; ⌞_⌟; ε; _↝_; _↝ˢ_; refl˜; _◇˜_; ✓-ε; ∙-unitˡ;
  ⌞⌟-ε)

--------------------------------------------------------------------------------
-- updᶠ: Updating an element at an index

abstract -- Definition is made abstract for better type inference

  updᶠ :  ℕ → A → Fin → Fin
  updᶠ i a F .fin j with i ≡ᵇ j
  ... | tt =  a
  ... | ff =  F .fin j
  updᶠ i _ F .supp =  i ∷ F .supp
  updᶠ i a F .out-ε {j} j∉i∷is with i ≡ᵇ j | ᵇ⇒≡ {i} {j}
  ... | tt | ⇒i≡j =  absurd $ ∉ᴸ-∷-elim₀ j∉i∷is $ ◠ ⇒i≡j _
  ... | ff | _ =  F .out-ε (∉ᴸ-∷-elim₁ j∉i∷is)

--------------------------------------------------------------------------------
-- injᶠ: Injecting an element at an index

injᶠ :  ℕ → A → Fin
injᶠ i a =  updᶠ i a ε

module _ {i : ℕ} where abstract

  ------------------------------------------------------------------------------
  -- On updᶠ

  -- updᶠ preserves ≈/✓/∙/⌞⌟/↝

  updᶠ-cong :  a ≈' b →  F ≈ G →  updᶠ i a F ≈ updᶠ i b G
  updᶠ-cong a≈b F≈G j with i ≡ᵇ j
  ... | tt =  a≈b
  ... | ff =  F≈G j

  updᶠ-✓ :  ✓' a →  ✓ F →  ✓ updᶠ i a F
  updᶠ-✓ ✓a ✓F j with i ≡ᵇ j
  ... | tt =  ✓a
  ... | ff =  ✓F j

  updᶠ-∙ :  updᶠ i a F ∙ updᶠ i b G  ≈  updᶠ i (a ∙' b) (F ∙ G)
  updᶠ-∙ j with i ≡ᵇ j
  ... | tt =  refl'
  ... | ff =  refl'

  updᶠ-⌞⌟ :  ⌞ updᶠ i a F ⌟  ≈  updᶠ i ⌞ a ⌟' ⌞ F ⌟
  updᶠ-⌞⌟ j with i ≡ᵇ j
  ... | tt =  refl'
  ... | ff =  refl'

  updᶠ-↝ :  a ↝' b →  updᶠ i a F ↝ updᶠ i b F
  updᶠ-↝ a↝b G ✓G∙iaF j with i ≡ᵇ j | ✓G∙iaF j
  ... | tt | ✓Gi∙a =  a↝b (G .fin j) ✓Gi∙a
  ... | ff | ✓Gj∙Fj =  ✓Gj∙Fj

  -- Double update

  updᶠ-2 :  updᶠ i a (updᶠ i b F) ≈ updᶠ i a F
  updᶠ-2 j with i ≡ᵇ j | ≡⇒ᵇ {i} {j}
  ... | tt | _ =  refl'
  ... | ff | i≢j with i ≡ᵇ j | ᵇ⇒≡ {i} {j}
    -- We need with i ≡ᵇ j to simplify updᶠ i b F j
  ...   | tt | ⇒i≡j =  absurd $ i≢j $ ⇒i≡j _
  ...   | ff | _ =  refl'

  ------------------------------------------------------------------------------
  -- On injᶠ

  -- injᶠ preserves ≈/✓/∙/ε/⌞⌟/↝

  injᶠ-cong :  a ≈' b →  injᶠ i a  ≈  injᶠ i b
  injᶠ-cong a≈b =  updᶠ-cong a≈b $ refl˜ {a = ε}

  injᶠ-✓ :  ✓' a →  ✓ injᶠ i a
  injᶠ-✓ ✓a =  updᶠ-✓ ✓a ✓-ε

  injᶠ-∙ :  injᶠ i a ∙ injᶠ i b  ≈  injᶠ i (a ∙' b)
  injᶠ-∙ =  _◇˜_ {injᶠ i _ ∙ injᶠ i _} {updᶠ i _ _} {injᶠ i _}
    updᶠ-∙ $ updᶠ-cong refl' (∙-unitˡ {a = ε})

  injᶠ-ε :  injᶠ i ε' ≈ ε
  injᶠ-ε j with i ≡ᵇ j
  ... | tt =  refl'
  ... | ff =  refl'

  injᶠ-⌞⌟ :  ⌞ injᶠ i a ⌟  ≈  injᶠ i ⌞ a ⌟'
  injᶠ-⌞⌟ =  _◇˜_ {⌞ injᶠ i _ ⌟} {updᶠ i ⌞ _ ⌟' ⌞ _ ⌟} {injᶠ i ⌞ _ ⌟'}
    updᶠ-⌞⌟ $ updᶠ-cong refl' ⌞⌟-ε

  injᶠ-↝ :  a ↝' b →  injᶠ i a ↝ injᶠ i b
  injᶠ-↝ =  updᶠ-↝

  -- Allocate at a fresh index

  allocᶠ :  ✓' a →  ε ↝ˢ λ F → ∑ i , F ≡ injᶠ i a
  allocᶠ {a} ✓a G ✓G∙ε =  injᶠ i₀ a , (_ , refl) , proof
   where
    i₀ :  ℕ
    i₀ =  suc $ [⊔] $ G .supp
    proof :  ✓ G ∙ injᶠ i₀ a
    proof j with i₀ ≡ᵇ j | ᵇ⇒≡ {i₀} {j}
    ... | ff | _ =  ✓G∙ε j
    ... | tt | ⇒i₀≡j with ⇒i₀≡j _
    ...   | refl =  flip ✓'-resp ✓a $ ◠'_ $
      ∙'-congˡ (G .out-ε suc[⊔]∉ᴸ) ◇' ∙'-unitˡ
