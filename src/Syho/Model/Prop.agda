--------------------------------------------------------------------------------
-- Semantic proposition
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop where

open import Syho.Model.ERA using (ERA)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ)

open ERA Globᴱᴿᴬ renaming (Res to Glob) using (_⊑_; _✓_)

--------------------------------------------------------------------------------
-- Propᵒ :  Semantic proposition

Propᵒ :  Set₃
Propᵒ =  Glob → Set₂

-- Monoᵒ Pᵒ :  Pᵒ is monotone over the resource

Monoᵒ :  Propᵒ →  Set₂
Monoᵒ Pᵒ =  ∀ {a b} →  a ⊑ b →  Pᵒ a →  Pᵒ b

--------------------------------------------------------------------------------
-- ⊨, ⊨' :  Entailment, with or without a validity input

infix 1 _⊨_ _⊨'_
_⊨_ _⊨'_ :  Propᵒ →  Propᵒ →  Set₂
Pᵒ ⊨ Qᵒ =  ∀ {E a} →  E ✓ a →  Pᵒ a →  Qᵒ a
Pᵒ ⊨' Qᵒ =  ∀ {a} →  Pᵒ a →  Qᵒ a
