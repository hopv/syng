--------------------------------------------------------------------------------
-- Level for universe levels
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Level where

open import Agda.Primitive public using (Level)
  renaming (lzero to 0ˡ; lsuc to sucˡ; _⊔_ to _⊔ˡ_)

record  Upˡ {ℓ : Level} (A : Set ℓ) {ℓ' : Level} :  Set (ℓ ⊔ˡ ℓ')  where
  constructor upˡ
  field  downˡ :  A
