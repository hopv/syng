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
open import Shog.Logic.Basic
open import Shog.Logic.Supd
open import Shog.Logic.Judg public using (
  save-mono₁; save-□⇒x; save□-□; savex-alloc; save□-alloc-rec)

private variable
  ℓ : Level
  i : Size
  Pᵗ Qᵗ : Propᵗ ℓ ∞
  R : Propˢ ℓ ∞
  b b' : Bool

instance
  save□-Pers : Pers (save□ Pᵗ)
  save□-Pers .pers = save□-□

save-mono₀ : b' ≤ b → save b Pᵗ ⊢[ i ] save b' Pᵗ
save-mono₀ f≤t = save-□⇒x
save-mono₀ b≤b = idˢ

save-mono : {{Basic R}} → b' ≤ b →
  R ∗ Pᵗ .force ⊢[< i ] Qᵗ .force → save b Pᵗ ⊢[ i ] save b' Qᵗ
save-mono H₀ H₁ = save-mono₀ H₀ » save-mono₁ H₁

save□-alloc : □ (Pᵗ .force) ⊢[ i ]=>> save□ Pᵗ
save□-alloc {Pᵗ = Pᵗ} = ∗⊤-intro » -∗-const »
  save□-alloc-rec {Pᵗs = [ Pᵗ ]} ᵘ» ∗-elim₀
