--------------------------------------------------------------------------------
-- List
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.List where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.Func using (_$_; _∘_; id)
open import Base.Few using (¬_; absurd)
open import Base.Eq using (_≡_; _≢_; refl; cong)
open import Base.Acc using (Acc; acc; acc-sub)
open import Base.Option using (¿_; š_; ň)
open import Base.Prod using (∑-syntax; _×_; _,_; _,-; -,_; uncurry)
open import Base.Sum using (_⨿_; ĩ₀_; ĩ₁_)
open import Base.Dec using (Dec; yes; no; ≡Dec; ≡dec; _≟_; ≟-refl)
open import Base.Nat using (ℕ; ṡ_; _<_; ṡ-inj)

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
  i j n :  ℕ
  _≺_ :  A → A → Set ł

instance

  -- List A is inhabited

  List-Dec :  Dec $ List A
  List-Dec =  yes []

--------------------------------------------------------------------------------
-- Equality decision for List A

instance

  List-≡Dec :  {{≡Dec A}} →  ≡Dec $ List A
  List-≡Dec {A = A} =  ≡dec _≟'_
   where
    infix 4 _≟'_
    _≟'_ :  ∀(as bs : List A) →  Dec $ as ≡ bs
    [] ≟' [] =  yes refl
    [] ≟' _ ∷ _ =  no λ ()
    _ ∷ _ ≟' [] =  no λ ()
    a ∷ as' ≟' b ∷ bs'  with a ≟ b | as' ≟' bs'
    … | yes refl | yes refl =  yes refl
    … | no a≢b | _ =  no λ{ refl → a≢b refl }
    … | _ | no as'≢bs' =  no λ{ refl → as'≢bs' refl }

--------------------------------------------------------------------------------
-- [  ] :  Singleton list

[_] :  A →  List A
[ a ] =  a ∷ []

--------------------------------------------------------------------------------
-- ⧺ :  Concatenate lists

infixr 5 _⧺_
_⧺_ :  List A →  List A →  List A
[] ⧺ bs =  bs
(a ∷ as) ⧺ bs =  a ∷ (as ⧺ bs)

abstract

  -- ⧺ is associative

  ⧺-assocˡ :  (as ⧺ bs) ⧺ cs  ≡  as ⧺ (bs ⧺ cs)
  ⧺-assocˡ {as = []} =  refl
  ⧺-assocˡ {as = _ ∷ as} =  cong (_ ∷_) (⧺-assocˡ {as = as})

  -- ⧺ and []

  ⧺-[] :  as ⧺ []  ≡  as
  ⧺-[] {as = []} =  refl
  ⧺-[] {as = _ ∷ as}  rewrite ⧺-[] {as = as} =  refl

  ⧺-≡[] :  as ⧺ bs ≡ [] →  as ≡ []  ×  bs ≡ []
  ⧺-≡[] {as = []} {bs = []} _ =  refl , refl

--------------------------------------------------------------------------------
-- len :  Length of a list

len :  List A →  ℕ
len [] =  0
len (_ ∷ as) =  ṡ len as

--------------------------------------------------------------------------------
-- Map

-- $ᴸ :  Map

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

  -- ‼ has the same partiality on lists of the same length

  ‼-len≡-š :  len as ≡ len bs →  ∑ a , as ‼ i ≡ š a →  ∑ b , bs ‼ i ≡ š b
  ‼-len≡-š {as = _ ∷ _} {bs = _ ∷ _} {0} _ _ =  -, refl
  ‼-len≡-š {as = _ ∷ _} {bs = _ ∷ _} {ṡ _} lenas'≡lenbs' as'‼i'≡š =
    ‼-len≡-š (ṡ-inj lenas'≡lenbs') as'‼i'≡š

  ‼-len≡-ň :  len as ≡ len bs →  as ‼ i ≡ ň →  bs ‼ i ≡ ň
  ‼-len≡-ň {as = []} {bs = []} _ _ =  refl
  ‼-len≡-ň {as = _ ∷ _} {bs = _ ∷ _} {ṡ _} lenas'≡lenbs' as'‼i'≡ň =
    ‼-len≡-ň (ṡ-inj lenas'≡lenbs') as'‼i'≡ň

  -- upd preserves the length

  upd-len :  len (upd i b as)  ≡  len as
  upd-len {as = []} =  refl
  upd-len {0} {as = _ ∷ _} =  refl
  upd-len {ṡ _} {as = _ ∷ as'} =  cong ṡ_ (upd-len {as = as'})

  -- ‼ i on upd i

  upd-‼-in :  ∑ a , as ‼ i ≡ š a →  upd i b as ‼ i  ≡  š b
  upd-‼-in {as = _ ∷ _} {0} as‼i≡š =  refl
  upd-‼-in {as = _ ∷ as'} {ṡ i'} as'‼i'≡š =  upd-‼-in {as = as'} as'‼i'≡š

  -- ‼ j on upd i for j distinct from i

  upd-‼-out :  j ≢ i →  upd i b as ‼ j  ≡  as ‼ j
  upd-‼-out {as = []} _ =  refl
  upd-‼-out {0} {0} j≢i =  absurd $ j≢i refl
  upd-‼-out {ṡ _} {0} {as = _ ∷ _} _ =  refl
  upd-‼-out {0} {ṡ _} {as = _ ∷ _} _ =  refl
  upd-‼-out {ṡ _} {ṡ _} {as = _ ∷ as'} j≢i =
    upd-‼-out {as = as'} λ{ refl → j≢i refl }

--------------------------------------------------------------------------------
-- rep :  List made by repeating an element n times

rep :  ℕ →  A →  List A
rep 0 _ =  []
rep (ṡ n) a =  a ∷ rep n a

abstract

  -- rep n has the length n

  rep-len :  len (rep n a)  ≡  n
  rep-len {0} =  refl
  rep-len {ṡ n} =  cong ṡ_ (rep-len {n})

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

infix 8 ĩʰᵈ_ ĩᵗˡ_
data  Any {A : Set ł} (F : A → Set ł') :  List A → Set (ł ⊔ᴸ ł')  where
  ĩʰᵈ_ :  ∀{a as} →  F a →  Any F (a ∷ as)
  ĩᵗˡ_ :  ∀{a as} →  Any F as →  Any F (a ∷ as)
open Any public

abstract

  -- Any and ⧺

  Any-⧺-ĩ₀ :  Any F as →  Any F (as ⧺ bs)
  Any-⧺-ĩ₀ (ĩʰᵈ Fa) =  ĩʰᵈ Fa
  Any-⧺-ĩ₀ (ĩᵗˡ Fas) =  ĩᵗˡ Any-⧺-ĩ₀ Fas

  Any-⧺-ĩ₁ :  Any F bs →  Any F (as ⧺ bs)
  Any-⧺-ĩ₁ {as = []} Fbs =  Fbs
  Any-⧺-ĩ₁ {as = _ ∷ _} Fbs =  ĩᵗˡ Any-⧺-ĩ₁ Fbs

  Any-⧺-case :  Any F (as ⧺ bs) →  Any F as ⨿ Any F bs
  Any-⧺-case {as = []} Fbs =  ĩ₁ Fbs
  Any-⧺-case {as = _ ∷ _} (ĩʰᵈ Fa) =  ĩ₀ ĩʰᵈ Fa
  Any-⧺-case {as = _ ∷ _} (ĩᵗˡ Fas'⧺bs) with Any-⧺-case Fas'⧺bs
  … | ĩ₀ Fas' =  ĩ₀ ĩᵗˡ Fas'
  … | ĩ₁ Fbs =  ĩ₁ Fbs

--------------------------------------------------------------------------------
-- ∈ᴸ :  Containment in a list

infix 4 _∈ᴸ_
_∈ᴸ_ :  ∀{A : Set ł} →  A →  List A →  Set ł
a ∈ᴸ as =  Any (a ≡_) as

infix 8 ∈ᵗˡ_
pattern ∈ʰᵈ =  ĩʰᵈ refl
pattern ∈ᵗˡ_ a∈as =  ĩᵗˡ a∈as

abstract

  -- ∈ᴸ and [ ]

  ∈ᴸ-[?]-inv :  a ∈ᴸ [ b ] →  a ≡ b
  ∈ᴸ-[?]-inv ∈ʰᵈ =  refl

  -- ∈ᴸ and ⧺

  ∈ᴸ-⧺-ĩ₀ :  a ∈ᴸ as →  a ∈ᴸ as ⧺ bs
  ∈ᴸ-⧺-ĩ₀ =  Any-⧺-ĩ₀

  ∈ᴸ-⧺-ĩ₁ :  a ∈ᴸ bs →  a ∈ᴸ as ⧺ bs
  ∈ᴸ-⧺-ĩ₁ =  Any-⧺-ĩ₁

  ∈ᴸ-⧺-case :  a ∈ᴸ as ⧺ bs →  a ∈ᴸ as ⨿ a ∈ᴸ bs
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
  ⊆ᴸ-[] {as = _ ∷ _} as⊆[]  with as⊆[] ∈ʰᵈ
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
  ≈ᴸ-[] (as⊆[] ,-) =  ⊆ᴸ-[] as⊆[]

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
  -- Singleton
  [_]⁺ :  A →  List⁺ A
  -- Cons
  _∷⁺_ :  A →  List⁺ A →  List⁺ A

-- Conversion between List⁺ A and A × List A

List⁺⇒×List :  List⁺ A →  A × List A
List⁺⇒×List [ a ]⁺ =  a , []
List⁺⇒×List (a ∷⁺ as) =  a , uncurry _∷_ $ List⁺⇒×List as

⇒List⇒List⁺ :  A →  List A →  List⁺ A
⇒List⇒List⁺ a [] =  [ a ]⁺
⇒List⇒List⁺ a (b ∷ bs) =  a ∷⁺ ⇒List⇒List⁺ b bs

-- hd⁺, tl⁺ :  Head and tail of List⁺

hd⁺ :  List⁺ A →  A
hd⁺ [ a ]⁺ =  a
hd⁺ (a ∷⁺ _) =  a

tl⁺ :  List⁺ A →  List A
tl⁺ [ _ ]⁺ =  []
tl⁺ (_ ∷⁺ as) =  uncurry _∷_ $ List⁺⇒×List as

instance

  -- Decide List⁺ A

  List⁺-Dec :  {{Dec A}} →  Dec $ List⁺ A
  List⁺-Dec {{yes a}} =  yes [ a ]⁺
  List⁺-Dec {{no ¬a}} =  no λ{ as → ¬a $ hd⁺ as }

--------------------------------------------------------------------------------
-- ≺ᴰᴹ⟨ ⟩ :  Dershowitz–Manna relation on List A

-- Aug F as bs :  bs is obtained by adding to as elements satisfying F

data  Aug {A : Set ł} (F : A → Set ł') :  List A →  List A →  Set (ł ⊔ᴸ ł')
  where
  aug-refl :  Aug F as as
  aug-∷ :  F a →  Aug F as bs →  Aug F as (a ∷ bs)

-- ≺ᴰᴹ⟨ ⟩ :  Dershowitz–Manna relation on List A
--           Its transitive closure, with the order of elements of lists
--           ignored, is the standard Dershowitz–Manna ordering on multisets

-- ≺ᴰᴹ⟨ ⟩ with the relation argument coming first
data  DM {A : Set ł} (_≺_ : A → A → Set ł') :  List A →  List A →  Set (ł ⊔ᴸ ł')

infix 4 _≺ᴰᴹ⟨_⟩_
_≺ᴰᴹ⟨_⟩_ :  {A : Set ł} →  List A →  (A → A → Set ł') →  List A →  Set (ł ⊔ᴸ ł')
as ≺ᴰᴹ⟨ _≺_ ⟩ bs =  DM _≺_ as bs

data  DM _≺_  where

  -- Add elements less than the head to the tail
  ≺ᴰᴹ-hd :  Aug (_≺ a) as bs →  bs ≺ᴰᴹ⟨ _≺_ ⟩ a ∷ as

  -- Keep the head and continue to the tail
  ≺ᴰᴹ-tl :  bs ≺ᴰᴹ⟨ _≺_ ⟩ as →  a ∷ bs ≺ᴰᴹ⟨ _≺_ ⟩ a ∷ as

abstract

  -- The proof here is based on "An inductive proof of the well-foundedness of
  -- the multiset order" by Tobias Nipkow (due to Wilfried Buchholz), 1998

  -- If a is accessible w.r.t. ≺ and as is accessible w.r.t. ≺ᴰᴹ⟨ _≺_ ⟩,
  -- then a ∷ as is accessible w.r.t. ≺ᴰᴹ⟨ _≺_ ⟩

  ≺ᴰᴹ-∷-acc :  Acc _≺_ a →  Acc _≺ᴰᴹ⟨ _≺_ ⟩_ as →  Acc _≺ᴰᴹ⟨ _≺_ ⟩_ (a ∷ as)
  ≺ᴰᴹ-∷-acc {_≺_ = _≺_} (acc ≺a⇒acc) =  go (λ b≺a → ≺ᴰᴹ-∷-acc (≺a⇒acc b≺a))
   where
    fo :  (∀{b bs} →  b ≺ a →
            Acc _≺ᴰᴹ⟨ _≺_ ⟩_ bs →  Acc _≺ᴰᴹ⟨ _≺_ ⟩_ (b ∷ bs)) →
          Acc _≺ᴰᴹ⟨ _≺_ ⟩_ as →
          (∀{bs} →  bs ≺ᴰᴹ⟨ _≺_ ⟩ as →  Acc _≺ᴰᴹ⟨ _≺_ ⟩_ (a ∷ bs)) →
          Acc _≺ᴰᴹ⟨ _≺_ ⟩_ (a ∷ as)
    fo {a = a} {as} big accas <as⇒acca∷ =  acc
      λ{ (≺ᴰᴹ-tl bs'<as) → <as⇒acca∷ bs'<as; (≺ᴰᴹ-hd augbs) → eo augbs }
     where
      eo :  Aug (_≺ a) as bs →  Acc _≺ᴰᴹ⟨ _≺_ ⟩_ bs
      eo aug-refl =  accas
      eo (aug-∷ b≺a augbs') =  big b≺a (eo augbs')
    go :  (∀{b bs} →  b ≺ a →
            Acc _≺ᴰᴹ⟨ _≺_ ⟩_ bs →  Acc _≺ᴰᴹ⟨ _≺_ ⟩_ (b ∷ bs)) →
          Acc _≺ᴰᴹ⟨ _≺_ ⟩_ as →  Acc _≺ᴰᴹ⟨ _≺_ ⟩_ (a ∷ as)
    go big accas@(acc <as⇒acc) =  fo big accas λ bs<as → go big (<as⇒acc bs<as)

  -- If every element of as is accessible w.r.t. ≺,
  -- then as is accessible w.r.t. ≺ᴰᴹ⟨ _≺_ ⟩

  ≺ᴰᴹ-acc :  (∀{a} →  a ∈ᴸ as →  Acc _≺_ a) →  Acc _≺ᴰᴹ⟨ _≺_ ⟩_ as
  ≺ᴰᴹ-acc {as = []} _ =  acc λ ()
  ≺ᴰᴹ-acc {as = _ ∷ _} ∈as⇒acc =
    ≺ᴰᴹ-∷-acc (∈as⇒acc ∈ʰᵈ) $ ≺ᴰᴹ-acc (∈as⇒acc ∘ ∈ᵗˡ_)

  -- If ≺ is well-founded, then ≺ᴰᴹ⟨ _≺_ ⟩ is well-founded

  ≺ᴰᴹ-wf :  (∀{a} → Acc _≺_ a) →  Acc _≺ᴰᴹ⟨ _≺_ ⟩_ as
  ≺ᴰᴹ-wf wf =  ≺ᴰᴹ-acc λ _ → wf

  -- Converse of ≺ᴰᴹ-acc :  If as is accessible w.r.t. ≺ᴰᴹ⟨ _≺_ ⟩,
  -- then every element of as is accessible w.r.t. ≺

  ≺ᴰᴹ-acc-inv :  Acc _≺ᴰᴹ⟨ _≺_ ⟩_ as →  a ∈ᴸ as →  Acc _≺_ a
  ≺ᴰᴹ-acc-inv accas ∈ʰᵈ =  acc-sub (λ a≺b → ≺ᴰᴹ-hd $ aug-∷ a≺b aug-refl) accas
  ≺ᴰᴹ-acc-inv (acc ≺as⇒acc) (∈ᵗˡ a∈as') =
    ≺ᴰᴹ-acc-inv (≺as⇒acc $ ≺ᴰᴹ-hd aug-refl) a∈as'
