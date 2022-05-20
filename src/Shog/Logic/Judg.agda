--------------------------------------------------------------------------------
-- Judgment in Shog, not exporting rules
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Logic.Judg (ℓ : Level) where

open import Shog.Logic.Judg.All ℓ public using (JudgRes; pure; |=>>_;
  Judg; _⊢[_]*_; _⊢[_]_; _⊢[<_]_; _⊢[_]=>>_; Pers; Pers-⇒□)
