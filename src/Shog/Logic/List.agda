--------------------------------------------------------------------------------
-- Shog definitions and lemams for lists
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Logic.List where

open import Base.Level using (Level)
open import Base.Size using (Size; ∞)
open import Base.Func using (_$_; _∘_; it)
open import Base.List using (List; []; _∷_; _++_)
open import Base.List.All2 using (All²; []ᴬ²; _∷ᴬ²_)

open import Shog.Logic.Prop using ([∗]; _∗_)
open import Shog.Logic.Core

private variable
  ℓ ℓ' : Level
  ι : Size
  A : Set ℓ'
  Ps Qs : List (Prop' ∞)

abstract
  ------------------------------------------------------------------------------
  -- On [∗]

  -- [∗] is monotone

  [∗]-mono : All² _⊢[ ι ]_ Ps Qs → [∗] Ps ⊢[ ι ] [∗] Qs
  [∗]-mono []ᴬ² = refl
  [∗]-mono (P⊢Q ∷ᴬ² Ps⊢Qs) = ∗-mono P⊢Q ([∗]-mono Ps⊢Qs)

  -- ++ can get inside and outside [∗]

  [∗]-++-in : [∗] Ps ∗ [∗] Qs ⊢[ ι ] [∗] (Ps ++ Qs)
  [∗]-++-in {Ps = []} = ∗-elimʳ
  [∗]-++-in {Ps = _ ∷ Ps} = ∗-assocˡ » ∗-monoʳ ([∗]-++-in {Ps = Ps})

  [∗]-++-out : [∗] (Ps ++ Qs) ⊢[ ι ] [∗] Ps ∗ [∗] Qs
  [∗]-++-out {Ps = []} = ⊤∗-intro
  [∗]-++-out {Ps = _ ∷ Ps} = ∗-monoʳ ([∗]-++-out {Ps = Ps}) » ∗-assocʳ
