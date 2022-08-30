--------------------------------------------------------------------------------
-- Lists
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.List where

open import Base.Level using (Level)
open import Base.Eq using (_≡_; refl; cong)
open import Base.Prod using (_×_; _,_)

--------------------------------------------------------------------------------
-- List

open import Agda.Builtin.List public using (List; []; _∷_)

private variable
  ł :  Level
  A B :  Set ł
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
