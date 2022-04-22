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
  save-monoʳ; save-□⇒x; save□-□; savex-alloc; save□-alloc-rec)

private variable
  ℓ : Level
  ι : Size
  P^ Q^ : Prop< ℓ ∞
  R : Prop' ℓ ∞
  b b' : Bool

instance
  -- save□ P^ is persistent
  save□-Pers : Pers (save□ P^)
  save□-Pers .pers = save□-□

-- save is monotone

save-monoˡ : b' ≤ b → save b P^ ⊢[ ι ] save b' P^
save-monoˡ f≤t = save-□⇒x
save-monoˡ b≤b = refl

save-mono : {{Basic R}} → b' ≤ b →
  R ∗ P^ .force ⊢[< ι ] Q^ .force → R ∗ save b P^ ⊢[ ι ] save b' Q^
save-mono b'≤b R∗P⊢Q = ∗-monoʳ (save-monoˡ b'≤b) » save-monoʳ R∗P⊢Q

-- Allocating save□, without recursion

save□-alloc : □ (P^ .force) ⊢[ ι ]=>> save□ P^
save□-alloc {P^ = P^} = ∗⊤-intro » -∗-const »
  save□-alloc-rec {P^s = [ P^ ]} ᵘ» ∗-elimˡ
