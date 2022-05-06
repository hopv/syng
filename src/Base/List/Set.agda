--------------------------------------------------------------------------------
-- Lists viewed as sets
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)
module Base.List.Set {ℓ ℓ≈} (S : Setoid ℓ ℓ≈) where
open Setoid S renaming (Carrier to A)

open import Base.Level using (_⊔ˡ_; 0ˡ)
open import Base.List using (List; _∷_; []; _++_; ++-assoc)
open import Base.List.Any using (Any; by-hd; by-tl; Any-++-inj₀; Any-++-inj₁;
  Any-++-case)
open import Base.Prod using (_×_; _,_)
open import Base.Sum using (_⊎_; inj₀; inj₁)
open import Base.Func using (id; _∘_; _$_)
open import Relation.Binary using (IsEquivalence)
open import Algebra using (IsCommutativeMonoid)
open import Base.Algebra using (make-IsCommutativeMonoid)

private variable
  as bs cs : List A
  a b : A

--------------------------------------------------------------------------------
-- ∈ˡ: Containment in a list

infix 4 _∈ˡ_
_∈ˡ_ : A → List A → Set (ℓ ⊔ˡ ℓ≈)
a ∈ˡ as = Any (a ≈_) as

abstract

  ------------------------------------------------------------------------------
  -- On ∈ˡ and ++

  ∈ˡ-++-inj₀ : a ∈ˡ as → a ∈ˡ as ++ bs
  ∈ˡ-++-inj₀ = Any-++-inj₀

  ∈ˡ-++-inj₁ : a ∈ˡ bs → a ∈ˡ as ++ bs
  ∈ˡ-++-inj₁ = Any-++-inj₁

  ∈ˡ-++-case : a ∈ˡ as ++ bs → a ∈ˡ as ⊎ a ∈ˡ bs
  ∈ˡ-++-case = Any-++-case

--------------------------------------------------------------------------------
-- ⊆ˡ: Inclusion between lists as sets

infix 4 _⊆ˡ_
_⊆ˡ_ : List A → List A → Set (ℓ ⊔ˡ ℓ≈)
as ⊆ˡ bs  =  ∀{a} →  a ∈ˡ as  →  a ∈ˡ bs

abstract

  -- ⊆ˡ is reflexive and transitive

  ⊆ˡ-refl : as ⊆ˡ as
  ⊆ˡ-refl = id

  ⊆ˡ-trans :  as ⊆ˡ bs  →  bs ⊆ˡ cs  →  as ⊆ˡ cs
  ⊆ˡ-trans as⊆bs bs⊆cs = bs⊆cs ∘ as⊆bs

  -- ++ is the lub w.r.t. ⊆ˡ

  ++-⊆ˡ-elim :  ∀ {as bs cs} →  as ⊆ˡ cs  →  bs ⊆ˡ cs  →  as ++ bs  ⊆ˡ  cs
  ++-⊆ˡ-elim as⊆cs bs⊆cs a∈as++bs with ∈ˡ-++-case a∈as++bs
  ... | inj₀ a∈as = as⊆cs a∈as
  ... | inj₁ a∈bs = bs⊆cs a∈bs

  ++-⊆ˡ-introˡ :  as  ⊆ˡ  as ++ bs
  ++-⊆ˡ-introˡ = ∈ˡ-++-inj₀

  ++-⊆ˡ-introʳ :  as  ⊆ˡ  bs ++ as
  ++-⊆ˡ-introʳ = ∈ˡ-++-inj₁

  -- More on ++ and  ⊆ˡ

  ++-⊆ˡ-monoˡ :  as ⊆ˡ bs  →  as ++ cs  ⊆ˡ  bs ++ cs
  ++-⊆ˡ-monoˡ as⊆bs = ++-⊆ˡ-elim (⊆ˡ-trans as⊆bs ++-⊆ˡ-introˡ) ++-⊆ˡ-introʳ

  ++-⊆ˡ-comm :  ∀ as bs →  as ++ bs  ⊆ˡ  bs ++ as
  ++-⊆ˡ-comm as bs = ++-⊆ˡ-elim {as} {bs} {bs ++ as} ++-⊆ˡ-introʳ ++-⊆ˡ-introˡ

--------------------------------------------------------------------------------
-- ≈ˡ: Equivalece of lists as sets

infix 4 _≈ˡ_
_≈ˡ_ : List A → List A → Set (ℓ ⊔ˡ ℓ≈)
as ≈ˡ bs  =  as ⊆ˡ bs  ×  bs ⊆ˡ as

abstract

  -- ≈ˡ is an equivalence relation

  ≈ˡ-refl : as ≈ˡ as
  ≈ˡ-refl = ⊆ˡ-refl , ⊆ˡ-refl

  ≈ˡ-sym :  as ≈ˡ bs  →  bs ≈ˡ as
  ≈ˡ-sym (as⊆bs , bs⊆as) = bs⊆as , as⊆bs

  ≈ˡ-trans :  as ≈ˡ bs  →  bs ≈ˡ cs  →  as ≈ˡ cs
  ≈ˡ-trans (as⊆bs , bs⊆as) (bs⊆cs , cs⊆bs) =
    ⊆ˡ-trans as⊆bs bs⊆cs , ⊆ˡ-trans cs⊆bs bs⊆as

  module _ where
    open IsEquivalence
    ≈ˡ-equiv : IsEquivalence _≈ˡ_
    ≈ˡ-equiv .refl = ≈ˡ-refl
    ≈ˡ-equiv .sym = ≈ˡ-sym
    ≈ˡ-equiv .trans = ≈ˡ-trans

abstract

  -- On ++ and ≈ˡ

  ++-≈ˡ-congˡ :  as ≈ˡ bs  →  as ++ cs  ≈ˡ  bs ++ cs
  ++-≈ˡ-congˡ (as⊆bs , bs⊆as)  =  ++-⊆ˡ-monoˡ as⊆bs , ++-⊆ˡ-monoˡ bs⊆as

  ++-≈ˡ-comm :  ∀ as bs →  as ++ bs  ≈ˡ  bs ++ as
  ++-≈ˡ-comm as bs  =  ++-⊆ˡ-comm as bs , ++-⊆ˡ-comm bs as

  ++-≈ˡ-assoc :  ∀ as bs cs →  (as ++ bs) ++ cs  ≈ˡ  as ++ (bs ++ cs)
  ++-≈ˡ-assoc as bs cs rewrite (++-assoc as bs cs)  =  ≈ˡ-refl

  ++-≈ˡ-isCommutativeMonoid : IsCommutativeMonoid _≈ˡ_ _++_ []
  ++-≈ˡ-isCommutativeMonoid  =  make-IsCommutativeMonoid ≈ˡ-equiv
    ++-≈ˡ-congˡ (λ _ → ≈ˡ-refl) ++-≈ˡ-comm ++-≈ˡ-assoc

  ++-≈ˡ-idem :  as ++ as  ≈ˡ  as
  ++-≈ˡ-idem  =  ++-⊆ˡ-elim ⊆ˡ-refl ⊆ˡ-refl , ++-⊆ˡ-introˡ

--------------------------------------------------------------------------------
-- homo: the list is homogeneous as a set

homo : List A → Set (ℓ ⊔ˡ ℓ≈)
homo as  =  ∀ {a b} →  a ∈ˡ as  →  b ∈ˡ as  →  a ≈ b

abstract

  homo-[] : homo []
  homo-[] ()

  homo-⊆ˡ-resp :  as ⊆ˡ bs  →  homo bs  →  homo as
  homo-⊆ˡ-resp as⊆bs homo'bs a∈as b∈as  =  homo'bs (as⊆bs a∈as) (as⊆bs b∈as)

  homo-≈ˡ-resp :  as ≈ˡ bs  →  homo as  →  homo bs
  homo-≈ˡ-resp (_ , bs⊆as)  =  homo-⊆ˡ-resp bs⊆as

  homo-heads2-≈ :  homo (a ∷ b ∷ cs)  →  a ≈ b
  homo-heads2-≈ homo'abcs =  homo'abcs (by-hd refl) (by-tl $ by-hd refl)
