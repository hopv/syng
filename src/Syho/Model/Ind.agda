--------------------------------------------------------------------------------
-- Interpreting the indirection modality ○
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Ind where

open import Base.Size using (∞)
open import Base.Prod using (∑-syntax; _×_)
open import Base.Sum using (_⊎_)
open import Syho.Logic.Prop using (Prop'; _∗_; Basic)
open import Syho.Logic.Judg using (_⊢[_]_)
open import Syho.Model.ERA using (ERA)
open import Syho.Model.ERA.Ind using (line-indˣ; line-ind□)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ; indˣ; ind□; injᴳ)
open import Syho.Model.Prop using (Propᵒ; _∗ᵒ_)
open import Syho.Model.Basic using (⸨_⸩ᴮ)

open ERA Globᴱᴿᴬ using (_⊑_)

--------------------------------------------------------------------------------
-- ind :  Interpret the indirection modality without the monotonicity patch

ind :  Prop' ∞ →  Propᵒ
ind P a =  ∑ i ,
  a ⊑ injᴳ indˣ (line-indˣ i P)  ⊎  a ⊑ injᴳ ind□ (line-ind□ i P)

--------------------------------------------------------------------------------
-- ○ᵒ :  Interpret the indirection modality ○

infix 8 ○ᵒ_
○ᵒ_ :  Prop' ∞ →  Propᵒ
(○ᵒ P) a =  ∑ Q , ∑ R , ∑ BasicR ,
  R ∗ Q ⊢[ ∞ ] P  ×  (⸨ R ⸩ᴮ {{BasicR}} ∗ᵒ ind Q) a
