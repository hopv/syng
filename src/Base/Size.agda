--------------------------------------------------------------------------------
-- Size for sized types
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Base.Size where

open import Agda.Builtin.Size public
  using (SizeUniv; Size; _⊔ˢ_; ∞) renaming (Size<_ to Size<; ↑_ to sucˢ)
