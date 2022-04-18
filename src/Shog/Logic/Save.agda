------------------------------------------------------------------------
-- Shog proof rules on the save token
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Logic.Save where

open import Level using (Level; suc)
open import Size using (Size; ∞)
open import Codata.Sized.Thunk using (force)
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
  Pt Qt : PropTh ℓ ∞
  b b' : Bool

instance
  save□-Pers : Pers (save□ Pt)
  save□-Pers .pers = save□-□

save-mono₀ : b' ≤ b → save b Pt ⊢[ i ] save b' Pt
save-mono₀ f≤t = save-□⇒x
save-mono₀ b≤b = idₛ

save-mono : b' ≤ b → Pt .force ⊢[< i ] Qt .force → save b Pt ⊢[ i ] save b' Qt
save-mono H₀ H₁ = save-mono₀ H₀ » save-mono₁ H₁

save□-alloc : □ (Pt .force) ⊢[ i ]=>> save□ Pt
save□-alloc {Pt = Pt} = ∗⊤-intro » -∗-const »
  save□-alloc-rec {Pts = [ Pt ]} [=>>]» ∗-elim₀
