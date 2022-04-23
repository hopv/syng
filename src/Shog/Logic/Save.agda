------------------------------------------------------------------------
-- Shog proof rules on the save token
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Level using (Level)
module Shog.Logic.Save (ℓ : Level) where

open import Size using (Size; ∞)
open import Codata.Thunk using (force)
open import Data.Bool.Base using (Bool; _≤_; f≤t; b≤b)
open import Data.List.Base using ([_])

open import Shog.Logic.Prop ℓ using (save; savex; save□) public
open import Shog.Logic.Prop ℓ using (Prop'; Prop<; □; _∗_; Basic)
open import Shog.Logic.Judg ℓ public using (
  save-monoʳ; save-□⇒x; save□-□; savex-alloc; save□-alloc-rec)
open import Shog.Logic.Judg ℓ using (_⊢[_]_; _⊢[<_]_; _⊢[_]=>>_)
open import Shog.Logic.Core ℓ using (Pers; pers;
  refl; _»_; ∗-monoʳ; ∗-elimˡ; ∗⊤-intro; -∗-const)
open import Shog.Logic.Supd ℓ using (_ᵘ»_)

private variable
  ι : Size
  P^ Q^ : Prop< ∞
  R : Prop' ∞
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
