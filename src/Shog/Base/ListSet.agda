----------------------------------------------------------------------
-- Agreement resource algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)
module Shog.Base.ListSet {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) where
open Setoid S renaming (Carrier to Car)

open import Level using (_⊔_; 0ℓ)
open import Data.List.Base using (List; _∷_; _++_; [])
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Setoid S using (_∈_)
open import Data.List.Membership.Setoid.Properties using ()
  renaming (∈-++⁺ˡ to ∈-++⁺ˡ'; ∈-++⁺ʳ to ∈-++⁺ʳ'; ∈-++⁻ to ∈-++⁻')
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (id; _∘_; _$_)
open import Relation.Binary using (IsEquivalence)
open import Algebra using (IsCommutativeMonoid)
open import Shog.Base.Algebra using (make-IsCommutativeMonoid)

private variable
  as bs cs : List Car
  a b : Car

----------------------------------------------------------------------
-- On ∈ and ++

∈-++⁺ˡ : a ∈ as → a ∈ as ++ bs
∈-++⁺ˡ = ∈-++⁺ˡ' S

∈-++⁺ʳ : ∀ {a as bs} → a ∈ bs → a ∈ as ++ bs
∈-++⁺ʳ {as = as} = ∈-++⁺ʳ' S as

∈-++⁻ : a ∈ as ++ bs → a ∈ as ⊎ a ∈ bs
∈-++⁻ {as = as} = ∈-++⁻' S as

----------------------------------------------------------------------
-- ⊆: Inclusion between lists as sets

infix 4 _⊆_
_⊆_ : List Car → List Car → Set (ℓ ⊔ ℓ≈)
as ⊆ bs  =  ∀{a} →  a ∈ as  →  a ∈ bs

----------------------------------------------------------------------
-- ⊆ is a preorder

⊆-refl : as ⊆ as
⊆-refl = id

⊆-trans :  as ⊆ bs  →  bs ⊆ cs  →  as ⊆ cs
⊆-trans as⊆bs bs⊆cs = bs⊆cs ∘ as⊆bs

----------------------------------------------------------------------
-- ++ is the lub w.r.t. ⊆

++-⊆-elim :  ∀ {as bs cs} →  as ⊆ cs  →  bs ⊆ cs  →  as ++ bs  ⊆  cs
++-⊆-elim as⊆cs bs⊆cs a∈as++bs with ∈-++⁻ a∈as++bs
... | inj₁ a∈as = as⊆cs a∈as
... | inj₂ a∈bs = bs⊆cs a∈bs

++-⊆-introˡ :  as  ⊆  as ++ bs
++-⊆-introˡ = ∈-++⁺ˡ

++-⊆-introʳ :  as  ⊆  bs ++ as
++-⊆-introʳ = ∈-++⁺ʳ

-- More on ++ and  ⊆

++-⊆-monoˡ :  as ⊆ bs  →  as ++ cs  ⊆  bs ++ cs
++-⊆-monoˡ as⊆bs = ++-⊆-elim (⊆-trans as⊆bs ++-⊆-introˡ) ++-⊆-introʳ

++-⊆-comm :  ∀ as bs →  as ++ bs  ⊆  bs ++ as
++-⊆-comm as bs = ++-⊆-elim {as} {bs} {bs ++ as} ++-⊆-introʳ ++-⊆-introˡ

----------------------------------------------------------------------
-- ≈ˢ: Equivalece of lists as sets

infix 4 _≈ˢ_
_≈ˢ_ : List Car → List Car → Set (ℓ ⊔ ℓ≈)
as ≈ˢ bs  =  as ⊆ bs  ×  bs ⊆ as

----------------------------------------------------------------------
-- ≈ˢ is an equivalence relation

≈ˢ-refl : as ≈ˢ as
≈ˢ-refl = ⊆-refl , ⊆-refl

≈ˢ-sym :  as ≈ˢ bs  →  bs ≈ˢ as
≈ˢ-sym (as⊆bs , bs⊆as) = bs⊆as , as⊆bs

≈ˢ-trans :  as ≈ˢ bs  →  bs ≈ˢ cs  →  as ≈ˢ cs
≈ˢ-trans (as⊆bs , bs⊆as) (bs⊆cs , cs⊆bs) =
  ⊆-trans as⊆bs bs⊆cs , ⊆-trans cs⊆bs bs⊆as

module _ where
  open IsEquivalence
  ≈ˢ-equiv : IsEquivalence _≈ˢ_
  ≈ˢ-equiv .refl = ≈ˢ-refl
  ≈ˢ-equiv .sym = ≈ˢ-sym
  ≈ˢ-equiv .trans = ≈ˢ-trans

----------------------------------------------------------------------
-- On ++ and ≈ˢ

++-≈ˢ-congˡ :  as ≈ˢ bs  →  as ++ cs  ≈ˢ  bs ++ cs
++-≈ˢ-congˡ (as⊆bs , bs⊆as)  =  ++-⊆-monoˡ as⊆bs , ++-⊆-monoˡ bs⊆as

++-≈ˢ-comm :  ∀ as bs →  as ++ bs  ≈ˢ  bs ++ as
++-≈ˢ-comm as bs  =  ++-⊆-comm as bs , ++-⊆-comm bs as

++-≈ˢ-assoc :  ∀ as bs cs →  (as ++ bs) ++ cs  ≈ˢ  as ++ (bs ++ cs)
++-≈ˢ-assoc as bs cs rewrite (++-assoc as bs cs)  =  ≈ˢ-refl

++-≈ˢ-isCommutativeMonoid : IsCommutativeMonoid _≈ˢ_ _++_ []
++-≈ˢ-isCommutativeMonoid  =  make-IsCommutativeMonoid ≈ˢ-equiv
  ++-≈ˢ-congˡ (λ _ → ≈ˢ-refl) ++-≈ˢ-comm ++-≈ˢ-assoc

++-≈ˢ-idem :  as ++ as  ≈ˢ  as
++-≈ˢ-idem  =  ++-⊆-elim ⊆-refl ⊆-refl , ++-⊆-introˡ

----------------------------------------------------------------------
-- homo: the list is homogeneous as a set

homo : List Car → Set (ℓ ⊔ ℓ≈)
homo as  =  ∀ {a b} →  a ∈ as  →  b ∈ as  →  a ≈ b

----------------------------------------------------------------------
-- On homo

homo-[] : homo []
homo-[] ()

homo-⊆-resp :  as ⊆ bs  →  homo bs  →  homo as
homo-⊆-resp as⊆bs homo'bs a∈as b∈as  =  homo'bs (as⊆bs a∈as) (as⊆bs b∈as)

homo-≈ˢ-resp :  as ≈ˢ bs  →  homo as  →  homo bs
homo-≈ˢ-resp (_ , bs⊆as)  =  homo-⊆-resp bs⊆as

homo-heads2-≈ :  homo (a ∷ b ∷ cs)  →  a ≈ b
homo-heads2-≈ homo'abcs =  homo'abcs (here refl) (there $ here refl)
