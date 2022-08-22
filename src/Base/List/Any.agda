--------------------------------------------------------------------------------
-- Disjunction over list elements
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.List.Any where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.List using (List; _∷_; []; _++_)
open import Base.Sum using (_⊎_; inj₀; inj₁)
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

  -- Any and ++

  Any-++-inj₀ :  Any F as →  Any F (as ++ bs)
  Any-++-inj₀ (by-hd Fa) =  by-hd Fa
  Any-++-inj₀ (by-tl Fas) =  by-tl $ Any-++-inj₀ Fas

  Any-++-inj₁ :  Any F bs →  Any F (as ++ bs)
  Any-++-inj₁ {as = []} Fbs =  Fbs
  Any-++-inj₁ {as = _ ∷ _} Fbs =  by-tl $ Any-++-inj₁ Fbs

  Any-++-case :  Any F (as ++ bs) →  Any F as ⊎ Any F bs
  Any-++-case {as = []} Fbs =  inj₁ Fbs
  Any-++-case {as = _ ∷ _} (by-hd Fa) =  inj₀ (by-hd Fa)
  Any-++-case {as = _ ∷ _} (by-tl Fas'++bs) with Any-++-case Fas'++bs
  ... | inj₀ Fas' =  inj₀ $ by-tl Fas'
  ... | inj₁ Fbs =  inj₁ Fbs

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

  -- ¬Any and ++

  ¬Any-++-intro :  ¬ Any F as →  ¬ Any F bs →  ¬ Any F (as ++ bs)
  ¬Any-++-intro ¬Fas ¬Fbs Fas++bs with Any-++-case Fas++bs
  ... | inj₀ Fas =  ¬Fas Fas
  ... | inj₁ Fbs =  ¬Fbs Fbs

  ¬Any-++-elim₀ :  ¬ Any F (as ++ bs) →  ¬ Any F as
  ¬Any-++-elim₀ ¬Fas++bs Fas =  ¬Fas++bs $ Any-++-inj₀ Fas

  ¬Any-++-elim₁ :  ¬ Any F (as ++ bs) →  ¬ Any F bs
  ¬Any-++-elim₁ ¬Fas++bs Fbs =  ¬Fas++bs $ Any-++-inj₁ Fbs
