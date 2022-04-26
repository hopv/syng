----------------------------------------------------------------------
-- Agreement resource algebra
----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)
module Shog.Base.ListSet {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) where
open Setoid S renaming (Carrier to Car)

open import Level using (_⊔_; 0ℓ)
open import Data.List.Base using (List; _++_; []) public
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Setoid S using (_∈_) public
open import Data.List.Membership.Setoid.Properties using ()
  renaming (∈-++⁺ˡ to ∈-++⁺ˡ'; ∈-++⁺ʳ to ∈-++⁺ʳ'; ∈-++⁻ to ∈-++⁻')
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (id; _∘_; _$_)
open import Relation.Binary using (Reflexive; Symmetric; Transitive;
  IsEquivalence)
open import Algebra using (Commutative; Associative; Idempotent;
  IsCommutativeMonoid)
open import Shog.Base.Algebra using (Congruentˡ; Unitˡ;
  make-IsCommutativeMonoid)

private variable
  as bs cs : List Car
  a : Car

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
as ⊆ bs = ∀{a} → a ∈ as → a ∈ bs

----------------------------------------------------------------------
-- ⊆ is a preorder

⊆-refl : Reflexive _⊆_
⊆-refl = id

⊆-trans : Transitive _⊆_
⊆-trans as⊆bs bs⊆cs = bs⊆cs ∘ as⊆bs

----------------------------------------------------------------------
-- ++ is the lub w.r.t. ⊆

++-⊆-elim : ∀ {as bs cs} → as ⊆ cs → bs ⊆ cs → as ++ bs ⊆ cs
++-⊆-elim as⊆cs bs⊆cs a∈as++bs with ∈-++⁻ a∈as++bs
... | inj₁ a∈as = as⊆cs a∈as
... | inj₂ a∈bs = bs⊆cs a∈bs

++-⊆-introˡ : as ⊆ as ++ bs
++-⊆-introˡ = ∈-++⁺ˡ

++-⊆-introʳ : as ⊆ bs ++ as
++-⊆-introʳ = ∈-++⁺ʳ

-- More on ++ and  ⊆

++-⊆-monoˡ : Congruentˡ _⊆_ _++_
++-⊆-monoˡ as⊆bs = ++-⊆-elim (⊆-trans as⊆bs ++-⊆-introˡ) ++-⊆-introʳ

++-⊆-comm : Commutative _⊆_ _++_
++-⊆-comm as bs = ++-⊆-elim {as} {bs} {bs ++ as} ++-⊆-introʳ ++-⊆-introˡ

----------------------------------------------------------------------
-- ≈ˢ: Equivalece of lists as sets

infix 4 _≈ˢ_
_≈ˢ_ : List Car → List Car → Set (ℓ ⊔ ℓ≈)
as ≈ˢ bs = as ⊆ bs × bs ⊆ as

----------------------------------------------------------------------
-- ≈ˢ is an equivalence relation

≈ˢ-refl : Reflexive _≈ˢ_
≈ˢ-refl = ⊆-refl , ⊆-refl

≈ˢ-sym : Symmetric _≈ˢ_
≈ˢ-sym (as⊆bs , bs⊆as) = bs⊆as , as⊆bs

≈ˢ-trans : Transitive _≈ˢ_
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

++-≈ˢ-congˡ : Congruentˡ _≈ˢ_ _++_
++-≈ˢ-congˡ (as⊆bs , bs⊆as) = ++-⊆-monoˡ as⊆bs , ++-⊆-monoˡ bs⊆as

++-≈ˢ-unitˡ : Unitˡ _≈ˢ_ [] _++_
++-≈ˢ-unitˡ _ = ≈ˢ-refl

++-≈ˢ-comm : Commutative _≈ˢ_ _++_
++-≈ˢ-comm as bs = ++-⊆-comm as bs , ++-⊆-comm bs as

++-≈ˢ-assoc : Associative _≈ˢ_ _++_
++-≈ˢ-assoc as bs cs rewrite ++-assoc as bs cs = ≈ˢ-refl

++-≈ˢ-isCommutativeMonoid : IsCommutativeMonoid _≈ˢ_ _++_ []
++-≈ˢ-isCommutativeMonoid = make-IsCommutativeMonoid ≈ˢ-equiv
  ++-≈ˢ-congˡ ++-≈ˢ-unitˡ ++-≈ˢ-comm ++-≈ˢ-assoc

++-≈ˢ-idem : Idempotent _≈ˢ_ _++_
++-≈ˢ-idem _ = ++-⊆-elim ⊆-refl ⊆-refl , ++-⊆-introˡ

----------------------------------------------------------------------
-- homo: the list is homogeneous as a set

homo : List Car → Set (ℓ ⊔ ℓ≈)
homo as = ∀ {a b} → a ∈ as → b ∈ as → a ≈ b

----------------------------------------------------------------------
-- On homo

homo-⊆-resp : as ⊆ bs → homo bs → homo as
homo-⊆-resp as⊆bs homobs a∈as b∈as = homobs (as⊆bs a∈as) (as⊆bs b∈as)

homo-≈ˢ-resp : as ≈ˢ bs → homo as → homo bs
homo-≈ˢ-resp (_ , bs⊆as) = homo-⊆-resp bs⊆as
