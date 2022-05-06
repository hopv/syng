--------------------------------------------------------------------------------
-- Level for universe levels
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Level where

open import Agda.Primitive public using (Level)
  renaming (lzero to 0ˡ; lsuc to sucˡ; _⊔_ to _⊔ˡ_)
