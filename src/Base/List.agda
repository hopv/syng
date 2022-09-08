--------------------------------------------------------------------------------
-- Lists
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.List where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.Func using (_$_; _∘_; id)
open import Base.Few using (¬_; absurd)
open import Base.Eq using (_≡_; _≢_; refl; cong)
open import Base.Prod using (_×_; _,_)
open import Base.Sum using (_⊎_; ĩ₀_; ĩ₁_)

--------------------------------------------------------------------------------
-- List

open import Agda.Builtin.List public using (List; []; _∷_)

private variable
  ł ł' ł'' :  Level
  A B :  Set ł
  F :  A → Set ł
  a b :  A
  as bs cs :  List A

--------------------------------------------------------------------------------
-- Singleton list

[_] :  A →  List A
[ a ] =  a ∷ []

--------------------------------------------------------------------------------
-- Map

infixr -1 _$ᴸ_
_$ᴸ_ :  (A → B) →  List A →  List B
_ $ᴸ [] =  []
f $ᴸ a ∷ as =  f a ∷ (f $ᴸ as)

--------------------------------------------------------------------------------
-- Append

infixr 5 _⧺_
_⧺_ :  List A →  List A →  List A
[] ⧺ bs =  bs
(a ∷ as) ⧺ bs =  a ∷ (as ⧺ bs)

abstract

  -- ⧺ is associative

  ⧺-assocˡ :  (as ⧺ bs) ⧺ cs ≡ as ⧺ (bs ⧺ cs)
  ⧺-assocˡ {as = []} =  refl
  ⧺-assocˡ {as = _ ∷ as} =  cong (_ ∷_) (⧺-assocˡ {as = as})

  -- ⧺ and []

  ⧺-[] :  as ⧺ [] ≡ as
  ⧺-[] {as = []} =  refl
  ⧺-[] {as = _ ∷ as}  rewrite ⧺-[] {as = as} =  refl

  ⧺-≡[] :  as ⧺ bs ≡ [] →  as ≡ [] × bs ≡ []
  ⧺-≡[] {as = []} {bs = []} _ =  refl , refl

--------------------------------------------------------------------------------
-- All² :  Conjunction over pairs of two lists

infixr 5 _∷ᴬ²_
data  All² {A : Set ł} {B : Set ł'} (F : A → B → Set ł'') :
  List A →  List B →  Set (ł ⊔ᴸ ł' ⊔ᴸ ł'')  where
  []ᴬ² :  All² F [] []
  _∷ᴬ²_ :  ∀{a b as bs} →  F a b →  All² F as bs →  All² F (a ∷ as) (b ∷ bs)
open All² public

--------------------------------------------------------------------------------
-- Any :  Disjunction over list elements

data  Any {A : Set ł} (F : A → Set ł') :  List A → Set (ł ⊔ᴸ ł')  where
  by-hd :  ∀{a as} →  F a →  Any F (a ∷ as)
  by-tl :  ∀{a as} →  Any F as →  Any F (a ∷ as)
open Any public

abstract

  -- Any and ⧺

  Any-⧺-ĩ₀ :  Any F as →  Any F (as ⧺ bs)
  Any-⧺-ĩ₀ (by-hd Fa) =  by-hd Fa
  Any-⧺-ĩ₀ (by-tl Fas) =  by-tl $ Any-⧺-ĩ₀ Fas

  Any-⧺-ĩ₁ :  Any F bs →  Any F (as ⧺ bs)
  Any-⧺-ĩ₁ {as = []} Fbs =  Fbs
  Any-⧺-ĩ₁ {as = _ ∷ _} Fbs =  by-tl $ Any-⧺-ĩ₁ Fbs

  Any-⧺-case :  Any F (as ⧺ bs) →  Any F as ⊎ Any F bs
  Any-⧺-case {as = []} Fbs =  ĩ₁ Fbs
  Any-⧺-case {as = _ ∷ _} (by-hd Fa) =  ĩ₀ (by-hd Fa)
  Any-⧺-case {as = _ ∷ _} (by-tl Fas'⧺bs) with Any-⧺-case Fas'⧺bs
  … | ĩ₀ Fas' =  ĩ₀ by-tl Fas'
  … | ĩ₁ Fbs =  ĩ₁ Fbs

  -- ¬Any

  ¬Any-[] :  ¬ Any F []
  ¬Any-[] ()

  -- ¬Any and ∷

  ¬Any-∷-intro :  ¬ F a →  ¬ Any F as →  ¬ Any F (a ∷ as)
  ¬Any-∷-intro ¬Fa _ (by-hd Fa) =  ¬Fa Fa
  ¬Any-∷-intro _ ¬Fas (by-tl Fas) =  ¬Fas Fas

  ¬Any-∷-elim₀ :  ¬ Any F (a ∷ as) →  ¬ F a
  ¬Any-∷-elim₀ ¬Fa∷as Fa =  ¬Fa∷as (by-hd Fa)

  ¬Any-∷-elim₁ :  ¬ Any F (a ∷ as) →  ¬ Any F as
  ¬Any-∷-elim₁ ¬Fa∷as Fas =  ¬Fa∷as (by-tl Fas)

  -- ¬Any and ⧺

  ¬Any-⧺-intro :  ¬ Any F as →  ¬ Any F bs →  ¬ Any F (as ⧺ bs)
  ¬Any-⧺-intro ¬Fas ¬Fbs Fas⧺bs with Any-⧺-case Fas⧺bs
  … | ĩ₀ Fas =  ¬Fas Fas
  … | ĩ₁ Fbs =  ¬Fbs Fbs

  ¬Any-⧺-elim₀ :  ¬ Any F (as ⧺ bs) →  ¬ Any F as
  ¬Any-⧺-elim₀ ¬Fas⧺bs Fas =  ¬Fas⧺bs $ Any-⧺-ĩ₀ Fas

  ¬Any-⧺-elim₁ :  ¬ Any F (as ⧺ bs) →  ¬ Any F bs
  ¬Any-⧺-elim₁ ¬Fas⧺bs Fbs =  ¬Fas⧺bs $ Any-⧺-ĩ₁ Fbs

--------------------------------------------------------------------------------
-- ∈ᴸ :  Containment in a list

infix 4 _∈ᴸ_
_∈ᴸ_ :  ∀{A : Set ł} →  A →  List A →  Set ł
a ∈ᴸ as =  Any (a ≡_) as

abstract

  -- ∈ᴸ and [ ]

  ∈ᴸ-[?] :  a ∈ᴸ [ a ]
  ∈ᴸ-[?] =  by-hd refl

  ∈ᴸ-[?]-inv :  a ∈ᴸ [ b ] →  a ≡ b
  ∈ᴸ-[?]-inv (by-hd a≡b) =  a≡b

  -- ∈ᴸ and ⧺

  ∈ᴸ-⧺-ĩ₀ :  a ∈ᴸ as →  a ∈ᴸ as ⧺ bs
  ∈ᴸ-⧺-ĩ₀ =  Any-⧺-ĩ₀

  ∈ᴸ-⧺-ĩ₁ :  a ∈ᴸ bs →  a ∈ᴸ as ⧺ bs
  ∈ᴸ-⧺-ĩ₁ =  Any-⧺-ĩ₁

  ∈ᴸ-⧺-case :  a ∈ᴸ as ⧺ bs →  a ∈ᴸ as ⊎ a ∈ᴸ bs
  ∈ᴸ-⧺-case =  Any-⧺-case

--------------------------------------------------------------------------------
-- ∉ᴸ :  Non-containment in a list

infix 4 _∉ᴸ_
_∉ᴸ_ :  ∀{A : Set ł} →  A →  List A →  Set ł
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

  -- ∉ᴸ and ⧺

  ∉ᴸ-⧺-intro :  a ∉ᴸ bs →  a ∉ᴸ cs →  a ∉ᴸ bs ⧺ cs
  ∉ᴸ-⧺-intro =  ¬Any-⧺-intro

  ∉ᴸ-⧺-elim₀ :  a ∉ᴸ bs ⧺ cs →  a ∉ᴸ bs
  ∉ᴸ-⧺-elim₀ =  ¬Any-⧺-elim₀

  ∉ᴸ-⧺-elim₁ :  a ∉ᴸ bs ⧺ cs →  a ∉ᴸ cs
  ∉ᴸ-⧺-elim₁ =  ¬Any-⧺-elim₁

--------------------------------------------------------------------------------
-- ⊆ᴸ :  Inclusion between lists as sets

infix 4 _⊆ᴸ_
_⊆ᴸ_ :  ∀{A : Set ł} →  List A →  List A →  Set ł
as ⊆ᴸ bs =  ∀{a} →  a ∈ᴸ as →  a ∈ᴸ bs

abstract

  -- ⊆ᴸ and []

  []-⊆ᴸ :  [] ⊆ᴸ as
  []-⊆ᴸ ()

  ⊆ᴸ-[] :  as ⊆ᴸ [] →  as ≡ []
  ⊆ᴸ-[] {as = []} _ =  refl
  ⊆ᴸ-[] {as = _ ∷ _} as⊆[] =  absurd $ ∉ᴸ-[] $ as⊆[] $ by-hd refl

  -- ⊆ᴸ is reflexive and transitive

  ⊆ᴸ-refl :  as ⊆ᴸ as
  ⊆ᴸ-refl =  id

  ⊆ᴸ-trans :  as ⊆ᴸ bs →  bs ⊆ᴸ cs →  as ⊆ᴸ cs
  ⊆ᴸ-trans as⊆bs bs⊆cs =  bs⊆cs ∘ as⊆bs

  -- ⧺ is the lowest upper bound with respect to ⊆ᴸ

  ⧺-⊆ᴸ-elim :  ∀{cs} →  as ⊆ᴸ cs →  bs ⊆ᴸ cs →  as ⧺ bs  ⊆ᴸ  cs
  ⧺-⊆ᴸ-elim as⊆cs bs⊆cs a∈as⧺bs with ∈ᴸ-⧺-case a∈as⧺bs
  … | ĩ₀ a∈as =  as⊆cs a∈as
  … | ĩ₁ a∈bs =  bs⊆cs a∈bs

  ⧺-⊆ᴸ-introˡ :  as  ⊆ᴸ  as ⧺ bs
  ⧺-⊆ᴸ-introˡ =  ∈ᴸ-⧺-ĩ₀

  ⧺-⊆ᴸ-introʳ :  as  ⊆ᴸ  bs ⧺ as
  ⧺-⊆ᴸ-introʳ =  ∈ᴸ-⧺-ĩ₁

  -- More on ⧺ and ⊆ᴸ

  ⧺-monoˡ :  as ⊆ᴸ bs →  as ⧺ cs  ⊆ᴸ  bs ⧺ cs
  ⧺-monoˡ as⊆bs =  ⧺-⊆ᴸ-elim (⊆ᴸ-trans as⊆bs ⧺-⊆ᴸ-introˡ) ⧺-⊆ᴸ-introʳ

  ⧺-⊆ᴸ-comm :  as ⧺ bs  ⊆ᴸ  bs ⧺ as
  ⧺-⊆ᴸ-comm {as = as} {bs}  =
    ⧺-⊆ᴸ-elim {as = as} {bs} {bs ⧺ as} ⧺-⊆ᴸ-introʳ ⧺-⊆ᴸ-introˡ

--------------------------------------------------------------------------------
-- ≈ᴸ :  Equivalece of lists as sets

infix 4 _≈ᴸ_
_≈ᴸ_ :  ∀{A : Set ł} →  List A → List A → Set ł
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

  -- ≈ᴸ and []

  ≈ᴸ-[] :  as ≈ᴸ [] →  as ≡ []
  ≈ᴸ-[] (as⊆[] , _) =  ⊆ᴸ-[] as⊆[]

  -- ⧺ preserves ≈ᴿ⁺ and is commutative and idempotent with respect to ≈ᴸ

  ⧺-congˡ :  as ≈ᴸ bs →  as ⧺ cs  ≈ᴸ  bs ⧺ cs
  ⧺-congˡ (as⊆bs , bs⊆as) =  ⧺-monoˡ as⊆bs , ⧺-monoˡ bs⊆as

  ⧺-comm :  as ⧺ bs  ≈ᴸ  bs ⧺ as
  ⧺-comm {as = as} {bs} =
    ⧺-⊆ᴸ-comm {as = as} {bs} , ⧺-⊆ᴸ-comm {as = bs} {as}

  ⧺-idem :  as ⧺ as  ≈ᴸ  as
  ⧺-idem =  ⧺-⊆ᴸ-elim ⊆ᴸ-refl ⊆ᴸ-refl , ⧺-⊆ᴸ-introˡ
