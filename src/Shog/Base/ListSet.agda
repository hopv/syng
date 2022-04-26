----------------------------------------------------------------------
-- Agreement resource algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)
module Shog.Base.ListSet {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) where
open Setoid S renaming (Carrier to Car)

open import Level using (_⊔_; 0ℓ)
open import Data.List.Base using (List; _++_)
open import Data.List.Membership.Setoid S using (_∈_)
open import Data.List.Membership.Setoid.Properties using ()
  renaming (∈-++⁺ˡ to ∈-++⁺ˡ'; ∈-++⁺ʳ to ∈-++⁺ʳ'; ∈-++⁻ to ∈-++⁻')
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (id; _∘_; _$_)
open import Relation.Binary using (IsEquivalence)
open import Shog.Base.Algebra using (Congruentˡ; make-IsCommutativeMonoid)

private variable
  as bs cs : List Car
  a : Car

----------------------------------------------------------------------
-- Lemmas on ∈

∈-++⁺ˡ : a ∈ as → a ∈ as ++ bs
∈-++⁺ˡ = ∈-++⁺ˡ' S

∈-++⁺ʳ : a ∈ bs → a ∈ as ++ bs
∈-++⁺ʳ {as = as} = ∈-++⁺ʳ' S as

∈-++⁻ : a ∈ as ++ bs → a ∈ as ⊎ a ∈ bs
∈-++⁻ {as = as} = ∈-++⁻' S as

----------------------------------------------------------------------
-- ⊆: Inclusion between lists as sets

infix 4 _⊆_
_⊆_ : List Car → List Car → Set (ℓ ⊔ ℓ≈)
as ⊆ bs = ∀{a} → a ∈ as → a ∈ bs

----------------------------------------------------------------------
-- On ⊆ and ++

++-⊆⁻ˡ : as ++ bs ⊆ cs → as ⊆ cs
++-⊆⁻ˡ as++bs⊆cs a∈as = as++bs⊆cs $ ∈-++⁺ˡ a∈as

++-⊆⁻ʳ : as ++ bs ⊆ cs → bs ⊆ cs
++-⊆⁻ʳ as++bs⊆cs a∈bs = as++bs⊆cs $ ∈-++⁺ʳ a∈bs

++-⊆⁺ : as ⊆ cs → bs ⊆ cs → as ++ bs ⊆ cs
++-⊆⁺ as⊆cs bs⊆cs a∈as++bs with ∈-++⁻ a∈as++bs
... | inj₁ a∈as = as⊆cs a∈as
... | inj₂ a∈bs = bs⊆cs a∈bs

⊆-++⁺ˡ : as ⊆ bs → as ⊆ bs ++ cs
⊆-++⁺ˡ as⊆bs a∈as = ∈-++⁺ˡ $ as⊆bs a∈as

⊆-++⁺ʳ : as ⊆ cs → as ⊆ bs ++ cs
⊆-++⁺ʳ as⊆cs a∈as = ∈-++⁺ʳ $ as⊆cs a∈as

++-⊆-monoˡ : Congruentˡ _⊆_ _++_
++-⊆-monoˡ as⊆bs a∈as++cs with ∈-++⁻ a∈as++cs
... | inj₁ a∈as = ∈-++⁺ˡ $ as⊆bs a∈as
... | inj₂ a∈cs = ∈-++⁺ʳ a∈cs

----------------------------------------------------------------------
-- ≈ˢ: Equivalece of lists as sets

infix 4 _≈ˢ_
_≈ˢ_ : List Car → List Car → Set (ℓ ⊔ ℓ≈)
as ≈ˢ bs = as ⊆ bs × bs ⊆ as

module _ where
  open IsEquivalence
  ≈ˢ-equiv : IsEquivalence _≈ˢ_
  ≈ˢ-equiv .refl = id , id
  ≈ˢ-equiv .sym (as⊆bs , bs⊆as) = bs⊆as , as⊆bs
  ≈ˢ-equiv .trans (as⊆bs , bs⊆as) (bs⊆cs , cs⊆bs) =
    bs⊆cs ∘ as⊆bs , bs⊆as ∘ cs⊆bs

++-≈ˢ-congˡ : Congruentˡ _≈ˢ_ _++_
++-≈ˢ-congˡ (as⊆bs , bs⊆as) = ++-⊆-monoˡ as⊆bs , ++-⊆-monoˡ bs⊆as
