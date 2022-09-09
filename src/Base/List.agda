--------------------------------------------------------------------------------
-- Lists
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.List where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.Func using (_$_; _∘_; id)
open import Base.Few using (¬_; absurd)
open import Base.Eq using (_≡_; _≢_; refl; cong)
open import Base.Option using (¿_; š_; ň)
open import Base.Prod using (∑-syntax; _×_; _,_)
open import Base.Sum using (_⊎_; ĩ₀_; ĩ₁_)
open import Base.Nat using (ℕ; ṡ_; _<_)

--------------------------------------------------------------------------------
-- List

-- Import and re-export
open import Agda.Builtin.List public using (
  -- List :  Set ł →  Set ł
  List;
  -- [] :  List A
  [];
  -- infixr 5 _∷_
  -- _∷_ :  A →  List A →  List A
  _∷_)

private variable
  ł ł' ł'' :  Level
  A B :  Set ł
  F :  A → Set ł
  a b :  A
  as bs cs :  List A
  i j :  ℕ

--------------------------------------------------------------------------------
-- Singleton list

[_] :  A →  List A
[ a ] =  a ∷ []

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
-- Length

len :  List A →  ℕ
len [] =  0
len (_ ∷ as) =  ṡ len as

--------------------------------------------------------------------------------
-- Map

-- $ⁱᴸ :  Map

infixr -1 _$ᴸ_
_$ᴸ_ :  (A → B) →  List A →  List B
_ $ᴸ [] =  []
f $ᴸ a ∷ as =  f a ∷ (f $ᴸ as)

-- $ⁱᴸ :  Map with an index

infixr -1 _$ⁱᴸ⟨_⟩_ _$ⁱᴸ_

_$ⁱᴸ⟨_⟩_ :  (ℕ → A → B) →  ℕ →  List A →  List B
_ $ⁱᴸ⟨ _ ⟩ [] =  []
f $ⁱᴸ⟨ i ⟩ a ∷ as =  f i a ∷ (f $ⁱᴸ⟨ ṡ i ⟩ as)

_$ⁱᴸ_ :  (ℕ → A → B) →  List A →  List B
f $ⁱᴸ as =  f $ⁱᴸ⟨ 0 ⟩ as

--------------------------------------------------------------------------------
-- Index access

-- ‼ :  Partial index read

infix 5 _‼_
_‼_ :  List A →  ℕ →  ¿ A
[] ‼ _ =  ň
(a ∷ _) ‼ 0 =  š a
(_ ∷ as) ‼ ṡ i =  as ‼ i

-- upd :  Index update

upd :  ℕ →  A →  List A →  List A
upd _ _ [] =  []
upd 0 b (_ ∷ as) =  b ∷ as
upd (ṡ i) b (a ∷ as) =  a ∷ upd i b as

abstract

  upd-‼-in :  (∑ a , as ‼ i ≡ š a) →  upd i b as ‼ i  ≡  š b
  upd-‼-in {as = _ ∷ _} {0} as‼i≡ša =  refl
  upd-‼-in {as = _ ∷ as'} {ṡ i'} as'‼i'≡ša =  upd-‼-in {as = as'} as'‼i'≡ša

  upd-‼-out :  i ≢ j →  upd i b as ‼ j ≡ as ‼ j
  upd-‼-out {as = []} _ =  refl
  upd-‼-out {0} {0} i≢j =  absurd $ i≢j refl
  upd-‼-out {ṡ _} {0} {as = _ ∷ _} _ =  refl
  upd-‼-out {0} {ṡ _} {as = _ ∷ _} _ =  refl
  upd-‼-out {ṡ _} {ṡ _} {as = _ ∷ as'} i≢j =
    upd-‼-out {as = as'} λ{ refl → i≢j refl }

--------------------------------------------------------------------------------
-- rep :  Repeat

rep :  ℕ →  A →  List A
rep 0 _ =  []
rep (ṡ n) a =  a ∷ rep n a

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
  ⊆ᴸ-[] {as = _ ∷ _} as⊆[]  with as⊆[] $ by-hd refl
  … | ()

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

--------------------------------------------------------------------------------
-- Positive-length (i.e., non-empty) list

infixr 5 _∷⁺_
data  List⁺ (A : Set ł) :  Set ł  where
  [_]⁺ :  A →  List⁺ A
  _∷⁺_ :  A →  List⁺ A →  List⁺ A

-- Conversion between List⁺ and List

List⁺⇒List :  List⁺ A →  List A
List⁺⇒List [ a ]⁺ =  [ a ]
List⁺⇒List (a ∷⁺ as) =  a ∷ List⁺⇒List as

List⇒List⁺ :  A →  List A →  List⁺ A
List⇒List⁺ a [] =  [ a ]⁺
List⇒List⁺ a (b ∷ bs) =  a ∷⁺ List⇒List⁺ b bs
