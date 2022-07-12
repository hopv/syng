--------------------------------------------------------------------------------
-- Finite-map resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Shog.Model.RA using (RA)
module Shog.Model.RA.Finmap {ℓ ℓ≈ ℓ✓} (Ra : RA ℓ ℓ≈ ℓ✓) where

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
open import Base.Nat using (ℕ; _≡ᵇ_; _⊔_; ≤-refl; ≡⇒ᵇ; ᵇ⇒≡; ⊔≤-introʳ)

import Base.Finmap
module ModFinmap =  Base.Finmap A (_≈' ε')
open ModFinmap using (Mostnull; finmap; mapfin; boundfin; mostnull; mergeᶠᵐ;
  updᶠᵐ; updaᶠᵐ; updaᶠᵐ-eq)
open ModFinmap public using (Finmap)

--------------------------------------------------------------------------------
-- Finmap : FinmapRA's carrier

private variable
  a b : A
  M N O : Finmap

--------------------------------------------------------------------------------
-- Internal definitions

private module _ where
  open RA

  -- Equivalence
  infix 4 _≈ᶠᵐ_
  _≈ᶠᵐ_ :  Finmap →  Finmap →  Set ℓ≈
  finmap f _ _ ≈ᶠᵐ finmap g _ _ =  ∀ i →  f i ≈' g i

  -- Validity
  infix 3 ✓ᶠᵐ_
  ✓ᶠᵐ_ :  Finmap →  Set ℓ✓
  ✓ᶠᵐ (finmap f _ _) =  ∀ i →  ✓' f i

  -- Product
  infixl 7 _∙ᶠᵐ_
  _∙ᶠᵐ_ :  Finmap →  Finmap →  Finmap
  M ∙ᶠᵐ M' =  mergeᶠᵐ _∙'_ (λ a≈ε b≈ε → ∙-cong Ra a≈ε b≈ε ◇' ∙-unitˡ Ra) M M'

  -- Unit
  εᶠᵐ :  Finmap
  εᶠᵐ .mapfin _ =  ε'
  εᶠᵐ .boundfin =  0
  εᶠᵐ .mostnull _ =  refl'

  -- Core
  ⌞_⌟ᶠᵐ :  Finmap →  Finmap
  ⌞ finmap f _ _ ⌟ᶠᵐ .mapfin i =  ⌞ f i ⌟'
  ⌞ finmap _ n _ ⌟ᶠᵐ .boundfin =  n
  ⌞ finmap _ _ monu ⌟ᶠᵐ .mostnull n≤j =  ⌞⌟-cong Ra (monu n≤j) ◇' ⌞⌟-ε Ra

--------------------------------------------------------------------------------
-- Internal lemma

private module _ where abstract
  open RA

  ⌞⌟ᶠᵐ-add :  ∀ M N →  ∑ N' ,  N' ∙ᶠᵐ ⌞ M ⌟ᶠᵐ ≈ᶠᵐ ⌞ N ∙ᶠᵐ M ⌟ᶠᵐ
  ⌞⌟ᶠᵐ-add (finmap f _ _) (finmap g _ _) .proj₀ .mapfin i =
    Ra .⌞⌟-add {f i} {g i} .proj₀
  ⌞⌟ᶠᵐ-add (finmap _ m _) (finmap _ n _) .proj₀ .boundfin =  n ⊔ m
  ⌞⌟ᶠᵐ-add M@(finmap f m monu) N@(finmap g n _) .proj₀ .mostnull =  proof
   where abstract
    proof :  Mostnull (λ i → Ra .⌞⌟-add {f i} {g i} .proj₀) (n ⊔ m)
    proof {i} n⊔m≤i =  ◠' ∙-unitʳ Ra ◇'
      ∙-congʳ Ra
        (◠'_ $ (Ra .⌞⌟-cong $ monu $ ⊔≤-introʳ {n} n⊔m≤i) ◇' ⌞⌟-ε Ra) ◇'
      Ra .⌞⌟-add {f i} {g i} .proj₁ ◇'
      Ra .⌞⌟-cong ((N ∙ᶠᵐ M) .mostnull n⊔m≤i) ◇' ⌞⌟-ε Ra
  ⌞⌟ᶠᵐ-add (finmap f _ _) (finmap g _ _) .proj₁ i =
    Ra .⌞⌟-add {f i} {g i} .proj₁

--------------------------------------------------------------------------------
-- FinmapRA : Finite-map resource algebra

module _ where
  open RA

  FinmapRA : RA (ℓ ⌴ ℓ≈) ℓ≈ ℓ✓
  FinmapRA .Car =  Finmap
  FinmapRA ._≈_ =  _≈ᶠᵐ_
  FinmapRA .✓_ =  ✓ᶠᵐ_
  FinmapRA ._∙_ =  _∙ᶠᵐ_
  FinmapRA .ε =  εᶠᵐ
  FinmapRA .⌞_⌟ =  ⌞_⌟ᶠᵐ
  FinmapRA .refl˜ _ =  refl'
  FinmapRA .◠˜_ M≈N i =  ◠' M≈N i
  FinmapRA ._◇˜_ M≈N N≈O i =  M≈N i ◇' N≈O i
  FinmapRA .∙-congˡ M≈N i =  Ra .∙-congˡ (M≈N i)
  FinmapRA .∙-unitˡ i =  Ra .∙-unitˡ
  FinmapRA .∙-comm i =  Ra .∙-comm
  FinmapRA .∙-assocˡ i =  Ra .∙-assocˡ
  FinmapRA .✓-resp M≈N ✓M i =  Ra .✓-resp (M≈N i) (✓M i)
  FinmapRA .✓-rem ✓M∙N i =  Ra .✓-rem (✓M∙N i)
  FinmapRA .✓-ε i =  Ra .✓-ε
  FinmapRA .⌞⌟-cong M≈N i =  Ra .⌞⌟-cong (M≈N i)
  FinmapRA .⌞⌟-add {M} {N} =  ⌞⌟ᶠᵐ-add M N
  FinmapRA .⌞⌟-unitˡ i =  Ra .⌞⌟-unitˡ
  FinmapRA .⌞⌟-idem i =  Ra .⌞⌟-idem

open RA FinmapRA using (_≈_; ✓_; _∙_; ⌞_⌟; ε; _↝_; _↝ˢ_; refl˜; _◇˜_; ✓-ε; ∙-unitˡ;
  ⌞⌟-ε)

-- injᶠᵐ/injaᶠᵐ: Injecting an element at an index

injᶠᵐ :  ℕ → A → Finmap
injᶠᵐ i a =  updᶠᵐ i a ε

injaᶠᵐ :  ℕ → A → Finmap
injaᶠᵐ i a =  updaᶠᵐ i a ε

module _ {i : ℕ} where abstract

  ------------------------------------------------------------------------------
  -- On updaᶠᵐ

  -- updaᶠᵐ preserves ≈/✓/∙/⌞⌟/↝

  updaᶠᵐ-cong :  a ≈' b →  M ≈ N →  updaᶠᵐ i a M ≈ updaᶠᵐ i b N
  updaᶠᵐ-cong a≈b M≈N j  rewrite updaᶠᵐ-eq  with i ≡ᵇ j
  ... | tt =  a≈b
  ... | ff =  M≈N j

  updaᶠᵐ-✓ :  ✓' a →  ✓ M →  ✓ updaᶠᵐ i a M
  updaᶠᵐ-✓ ✓a ✓M j  rewrite updaᶠᵐ-eq  with i ≡ᵇ j
  ... | tt =  ✓a
  ... | ff =  ✓M j

  updaᶠᵐ-∙ :  updaᶠᵐ i a M ∙ updaᶠᵐ i b N  ≈  updaᶠᵐ i (a ∙' b) (M ∙ N)
  updaᶠᵐ-∙ j  rewrite updaᶠᵐ-eq  with i ≡ᵇ j
  ... | tt =  refl'
  ... | ff =  refl'

  updaᶠᵐ-⌞⌟ :  ⌞ updaᶠᵐ i a M ⌟  ≈  updaᶠᵐ i ⌞ a ⌟' ⌞ M ⌟
  updaᶠᵐ-⌞⌟ j  rewrite updaᶠᵐ-eq  with i ≡ᵇ j
  ... | tt =  refl'
  ... | ff =  refl'

  updaᶠᵐ-↝ :  a ↝' b →  updaᶠᵐ i a M ↝ updaᶠᵐ i b M
  updaᶠᵐ-↝ a↝b N ✓N∙iaM j  rewrite updaᶠᵐ-eq  with i ≡ᵇ j | ✓N∙iaM j
  ... | tt | ✓Ni∙a =  a↝b (N .mapfin j) ✓Ni∙a
  ... | ff | ✓Nj∙Mj =  ✓Nj∙Mj

  -- Double update

  updaᶠᵐ-2 :  updaᶠᵐ i a (updaᶠᵐ i b M) ≈ updaᶠᵐ i a M
  updaᶠᵐ-2 j  rewrite updaᶠᵐ-eq  with i ≡ᵇ j | ≡⇒ᵇ {i} {j}
  ... | tt | _ =  refl'
  ... | ff | i≢j  with i ≡ᵇ j | ᵇ⇒≡ {i} {j}
    -- We need with i ≡ᵇ j to simplify updaᶠᵐ i b M j
  ...   | tt | ⇒i≡j =  absurd $ i≢j $ ⇒i≡j _
  ...   | ff | _ =  refl'

  ------------------------------------------------------------------------------
  -- On injaᶠᵐ

  -- injaᶠᵐ preserves ≈/✓/∙/ε/⌞⌟/↝

  injaᶠᵐ-cong :  a ≈' b →  injaᶠᵐ i a  ≈  injaᶠᵐ i b
  injaᶠᵐ-cong a≈b =  updaᶠᵐ-cong a≈b $ refl˜ {a = ε}

  injaᶠᵐ-✓ :  ✓' a →  ✓ injaᶠᵐ i a
  injaᶠᵐ-✓ ✓a =  updaᶠᵐ-✓ ✓a ✓-ε

  injaᶠᵐ-∙ :  injaᶠᵐ i a ∙ injaᶠᵐ i b  ≈  injaᶠᵐ i (a ∙' b)
  injaᶠᵐ-∙ =  _◇˜_ {injaᶠᵐ i _ ∙ injaᶠᵐ i _} {updaᶠᵐ i _ _} {injaᶠᵐ i _}
    updaᶠᵐ-∙ $ updaᶠᵐ-cong refl' (∙-unitˡ {a = ε})

  injaᶠᵐ-ε :  injaᶠᵐ i ε' ≈ ε
  injaᶠᵐ-ε j  rewrite updaᶠᵐ-eq  with i ≡ᵇ j
  ... | tt =  refl'
  ... | ff =  refl'

  injaᶠᵐ-⌞⌟ :  ⌞ injaᶠᵐ i a ⌟  ≈  injaᶠᵐ i ⌞ a ⌟'
  injaᶠᵐ-⌞⌟ =  _◇˜_ {⌞ injaᶠᵐ i _ ⌟} {updaᶠᵐ i ⌞ _ ⌟' ⌞ _ ⌟} {injaᶠᵐ i ⌞ _ ⌟'}
    updaᶠᵐ-⌞⌟ $ updaᶠᵐ-cong refl' ⌞⌟-ε

  injaᶠᵐ-↝ :  a ↝' b →  injaᶠᵐ i a ↝ injaᶠᵐ i b
  injaᶠᵐ-↝ =  updaᶠᵐ-↝

  -- Allocate at a fresh index

  allocᶠᵐ :  ✓' a →  ε ↝ˢ λ M → ∑ i , M ≡ injaᶠᵐ i a
  allocᶠᵐ {a} ✓a N@(finmap f n monu) ✓N∙ε =  injaᶠᵐ n a , (_ , refl) , proof
   where
    proof :  ✓ N ∙ injaᶠᵐ n a
    proof i  rewrite updaᶠᵐ-eq  with n ≡ᵇ i | ᵇ⇒≡ {n} {i}
    ... | ff | _ =  ✓N∙ε i
    ... | tt | ⇒n≡i with ⇒n≡i _
    ...   | refl =  flip ✓'-resp ✓a $ ◠'_ $ ∙'-congˡ (monu ≤-refl) ◇' ∙'-unitˡ
