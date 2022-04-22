------------------------------------------------------------------------
-- Shog proof rules on the save token
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Logic.Save where

open import Level using (Level; suc)
open import Size using (Size; ∞)
open import Codata.Thunk using (force)
open import Data.Bool.Base using (Bool; _≤_; f≤t; b≤b)
open import Data.List.Base using ([_])

open import Shog.Logic.Prop
open import Shog.Logic.Core
open import Shog.Logic.Supd
open import Shog.Logic.Judg public using (
  save-mono₁; save-□⇒x; save□-□; savex-alloc; save□-alloc-rec)

private variable
  ℓ : Level
  i : Size
  Pᶺ Qᶺ : Propˢ< ℓ ∞
  R : Propˢ ℓ ∞
  b b' : Bool

instance
  -- save□ Pᶺ is persistent
  save□-Pers : Pers (save□ Pᶺ)
  save□-Pers .pers = save□-□

-- save is monotone

save-mono₀ : b' ≤ b → save b Pᶺ ⊢[ i ] save b' Pᶺ
save-mono₀ f≤t = save-□⇒x
save-mono₀ b≤b = idˢ

save-mono : {{Basic R}} → b' ≤ b →
  R ∗ Pᶺ .force ⊢[< i ] Qᶺ .force → R ∗ save b Pᶺ ⊢[ i ] save b' Qᶺ
save-mono H₀ H₁ = ∗-mono₁ (save-mono₀ H₀) » save-mono₁ H₁

-- Allocating save□, without recursion

save□-alloc : □ (Pᶺ .force) ⊢[ i ]=>> save□ Pᶺ
save□-alloc {Pᶺ = Pᶺ} = ∗⊤-intro » -∗-const »
  save□-alloc-rec {Pᶺs = [ Pᶺ ]} ᵘ» ∗-elim₀
