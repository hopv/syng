--------------------------------------------------------------------------------
-- Disjunction over list elements
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.List.Any where

open import Base.Level using (Level; _⊔ˡ_)
open import Base.List using (List; _∷_; []; _++_)
open import Base.Sum using (_⊎_; inj₀; inj₁)
open import Base.Func using (_$_)

private variable
  ℓA ℓF : Level
  A : Set ℓA
  F : A → Set ℓF
  as bs cs : List A

--------------------------------------------------------------------------------
-- Disjunction over list elements
data Any {A : Set ℓA} (F : A → Set ℓF) : List A → Set (ℓA ⊔ˡ ℓF) where
  by-hd : ∀ {a as} → F a → Any F (a ∷ as)
  by-tl : ∀ {a as} → Any F as → Any F (a ∷ as)
open Any public

abstract
  -- ++ and Any

  Any-++-inj₀ : Any F as → Any F (as ++ bs)
  Any-++-inj₀ (by-hd Fa) = by-hd Fa
  Any-++-inj₀ (by-tl AnyFas) = by-tl $ Any-++-inj₀ AnyFas

  Any-++-inj₁ : Any F bs → Any F (as ++ bs)
  Any-++-inj₁ {as = []} AnyFbs = AnyFbs
  Any-++-inj₁ {as = _ ∷ _} AnyFbs = by-tl $ Any-++-inj₁ AnyFbs

  Any-++-case : Any F (as ++ bs) → Any F as ⊎ Any F bs
  Any-++-case {as = []} AnyFbs = inj₁ AnyFbs
  Any-++-case {as = _ ∷ _} (by-hd Fa) = inj₀ (by-hd Fa)
  Any-++-case {as = _ ∷ _} (by-tl AnyFasbs) with Any-++-case AnyFasbs
  ... | inj₀ AnyFas = inj₀ $ by-tl AnyFas
  ... | inj₁ AnyFbs = inj₁ AnyFbs
