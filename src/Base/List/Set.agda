--------------------------------------------------------------------------------
-- Lists viewed as sets
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.List.Set where

open import Base.Level using (Level)
open import Base.Eq using (_≡_; refl; _≢_; _◇_; ◠_)
open import Base.List using (List; _∷_; []; [_]; _++_)
open import Base.List.Any using (Any; by-hd; by-tl;
  Any-++-inj₀; Any-++-inj₁; Any-++-case;
  ¬Any-[]; ¬Any-∷-intro; ¬Any-∷-elim₀; ¬Any-∷-elim₁;
  ¬Any-++-intro; ¬Any-++-elim₀; ¬Any-++-elim₁)
open import Base.Prod using (_×_; _,_)
open import Base.Sum using (_⊎_; inj₀; inj₁)
open import Base.Few using (¬_)
open import Base.Func using (id; _∘_; _$_)

private variable
  ℓ :  Level
  A :  Set ℓ
  as bs cs :  List A
  a b :  A

--------------------------------------------------------------------------------
-- ∈ᴸ :  Containment in a list

infix 4 _∈ᴸ_
_∈ᴸ_ :  ∀{A : Set ℓ} →  A →  List A →  Set ℓ
a ∈ᴸ as =  Any (a ≡_) as

abstract

  -- ∈ᴸ and [ ]

  ∈ᴸ-[?] :  a ∈ᴸ  [ b ] →  a ≡ b
  ∈ᴸ-[?] (by-hd a≡b) =  a≡b

  -- ∈ᴸ and ++

  ∈ᴸ-++-inj₀ :  a ∈ᴸ as →  a ∈ᴸ as ++ bs
  ∈ᴸ-++-inj₀ =  Any-++-inj₀

  ∈ᴸ-++-inj₁ :  a ∈ᴸ bs →  a ∈ᴸ as ++ bs
  ∈ᴸ-++-inj₁ =  Any-++-inj₁

  ∈ᴸ-++-case :  a ∈ᴸ as ++ bs →  a ∈ᴸ as ⊎ a ∈ᴸ bs
  ∈ᴸ-++-case =  Any-++-case

--------------------------------------------------------------------------------
-- ∉ᴸ :  Non-containment in a list

infix 4 _∉ᴸ_
_∉ᴸ_ :  A →  List A →  Set _
a ∉ᴸ as =  ¬ a ∈ᴸ as

abstract

  ∉ᴸ-[] :  a ∉ᴸ []
  ∉ᴸ-[] =  ¬Any-[]

  -- ∉ᴸ and ∷

  ∉ᴸ-∷-intro :  a ≢ b →  a ∉ᴸ bs →  a ∉ᴸ b ∷ bs
  ∉ᴸ-∷-intro =  ¬Any-∷-intro

  ∉ᴸ-∷-elim₀ :  a ∉ᴸ b ∷ bs →  a ≢ b
  ∉ᴸ-∷-elim₀ =  ¬Any-∷-elim₀

  ∉ᴸ-∷-elim₁ :  a ∉ᴸ b ∷ bs →  a ∉ᴸ bs
  ∉ᴸ-∷-elim₁ =  ¬Any-∷-elim₁

  -- ∉ᴸ and ++

  ∉ᴸ-++-intro :  a ∉ᴸ bs →  a ∉ᴸ cs →  a ∉ᴸ bs ++ cs
  ∉ᴸ-++-intro =  ¬Any-++-intro

  ∉ᴸ-++-elim₀ :  a ∉ᴸ bs ++ cs →  a ∉ᴸ bs
  ∉ᴸ-++-elim₀ =  ¬Any-++-elim₀

  ∉ᴸ-++-elim₁ :  a ∉ᴸ bs ++ cs →  a ∉ᴸ cs
  ∉ᴸ-++-elim₁ =  ¬Any-++-elim₁

--------------------------------------------------------------------------------
-- ⊆ᴸ :  Inclusion between lists as sets

infix 4 _⊆ᴸ_
_⊆ᴸ_ :  ∀{A : Set ℓ} →  List A →  List A →  Set ℓ
as ⊆ᴸ bs =  ∀ {a} →  a ∈ᴸ as →  a ∈ᴸ bs

abstract

  -- ⊆ᴸ is reflexive and transitive

  ⊆ᴸ-refl :  as ⊆ᴸ as
  ⊆ᴸ-refl =  id

  ⊆ᴸ-trans :  as ⊆ᴸ bs →  bs ⊆ᴸ cs →  as ⊆ᴸ cs
  ⊆ᴸ-trans as⊆bs bs⊆cs =  bs⊆cs ∘ as⊆bs

  -- ++ is the lub w.r.t. ⊆ᴸ

  ++-⊆ᴸ-elim :  ∀ {cs} →  as ⊆ᴸ cs →  bs ⊆ᴸ cs →  as ++ bs  ⊆ᴸ  cs
  ++-⊆ᴸ-elim as⊆cs bs⊆cs a∈as++bs with ∈ᴸ-++-case a∈as++bs
  ... | inj₀ a∈as =  as⊆cs a∈as
  ... | inj₁ a∈bs =  bs⊆cs a∈bs

  ++-⊆ᴸ-introˡ :  as  ⊆ᴸ  as ++ bs
  ++-⊆ᴸ-introˡ =  ∈ᴸ-++-inj₀

  ++-⊆ᴸ-introʳ :  as  ⊆ᴸ  bs ++ as
  ++-⊆ᴸ-introʳ =  ∈ᴸ-++-inj₁

  -- More on ++ and ⊆ᴸ

  ++-monoˡ :  as ⊆ᴸ bs →  as ++ cs  ⊆ᴸ  bs ++ cs
  ++-monoˡ as⊆bs =  ++-⊆ᴸ-elim (⊆ᴸ-trans as⊆bs ++-⊆ᴸ-introˡ) ++-⊆ᴸ-introʳ

  ++-⊆ᴸ-comm :  as ++ bs  ⊆ᴸ  bs ++ as
  ++-⊆ᴸ-comm {as = as} {bs}  =
    ++-⊆ᴸ-elim {as = as} {bs} {bs ++ as} ++-⊆ᴸ-introʳ ++-⊆ᴸ-introˡ

--------------------------------------------------------------------------------
-- ≈ᴸ :  Equivalece of lists as sets

infix 4 _≈ᴸ_
_≈ᴸ_ :  ∀{A : Set ℓ} →  List A → List A → Set ℓ
as ≈ᴸ bs =  as ⊆ᴸ bs  ×  bs ⊆ᴸ as

abstract

  -- ≈ᴸ is reflexive, symmetric and transitive

  ≈ᴸ-refl :  as ≈ᴸ as
  ≈ᴸ-refl =  ⊆ᴸ-refl , ⊆ᴸ-refl

  ≡⇒≈ᴸ :  as ≡ bs →  as ≈ᴸ bs
  ≡⇒≈ᴸ refl =  ≈ᴸ-refl

  ≈ᴸ-sym :  as ≈ᴸ bs →  bs ≈ᴸ as
  ≈ᴸ-sym (as⊆bs , bs⊆as) =  bs⊆as , as⊆bs

  ≈ᴸ-trans :  as ≈ᴸ bs →  bs ≈ᴸ cs →  as ≈ᴸ cs
  ≈ᴸ-trans (as⊆bs , bs⊆as) (bs⊆cs , cs⊆bs) =
    ⊆ᴸ-trans as⊆bs bs⊆cs , ⊆ᴸ-trans cs⊆bs bs⊆as

  -- ++ is congruent, commutative and idempotent w.r.t. ≈ᴸ

  ++-congˡ :  as ≈ᴸ bs →  as ++ cs  ≈ᴸ  bs ++ cs
  ++-congˡ (as⊆bs , bs⊆as) =  ++-monoˡ as⊆bs , ++-monoˡ bs⊆as

  ++-comm :  as ++ bs  ≈ᴸ  bs ++ as
  ++-comm {as = as} {bs} =
    ++-⊆ᴸ-comm {as = as} {bs} , ++-⊆ᴸ-comm {as = bs} {as}

  ++-idem :  as ++ as  ≈ᴸ  as
  ++-idem =  ++-⊆ᴸ-elim ⊆ᴸ-refl ⊆ᴸ-refl , ++-⊆ᴸ-introˡ

--------------------------------------------------------------------------------
-- homo :  the list is homogeneous as a set

homo :  ∀{A : Set ℓ} →  List A →  Set ℓ
homo as =  ∀ {a b} →  a ∈ᴸ as →  b ∈ᴸ as →  a ≡ b

abstract

  homo-[] :  homo ([] {A = A})
  homo-[] ()

  homo-[?] :  homo [ a ]
  homo-[?] a'∈[a] b'∈[a] =  ∈ᴸ-[?] a'∈[a] ◇ ◠ ∈ᴸ-[?] b'∈[a]

  homo-mono :  as ⊆ᴸ bs →  homo bs →  homo as
  homo-mono as⊆bs homo'bs a∈as b∈as =  homo'bs (as⊆bs a∈as) (as⊆bs b∈as)

  homo-resp :  as ≈ᴸ bs →  homo as →  homo bs
  homo-resp (_ , bs⊆as) =  homo-mono bs⊆as

  homo-agree :  homo (a ∷ b ∷ []) →  a ≡ b
  homo-agree homo'abcs =  homo'abcs (by-hd refl) (by-tl $ by-hd refl)
