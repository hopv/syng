--------------------------------------------------------------------------------
-- Disjunction over list elements
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.List.Any where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.List using (List; _∷_; []; _⧺_)
open import Base.Sum using (_⊎_; ĩ₀_; ĩ₁_)
open import Base.Func using (_$_)
open import Base.Few using (¬_)

private variable
  ł ł' :  Level
  A :  Set ł
  F :  A → Set ł
  a :  A
  as bs cs :  List A

--------------------------------------------------------------------------------
-- Disjunction over list elements
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
