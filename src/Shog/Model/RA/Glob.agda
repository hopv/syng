--------------------------------------------------------------------------------
-- Global resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Model.RA.Glob (ℓ : Level) where

open import Base.Level using (^_)
open import Base.Size using (∞)
open import Base.Setoid using (Setoid; ≡-setoid)
open import Base.Nat using (ℕ; _≡?_)
open import Shog.Logic.Prop ℓ using (Prop')
open import Shog.Model.RA using (RA)
open import Shog.Model.RA.Top using (⊤RA)

import Shog.Model.RA.Exc
import Shog.Model.RA.Ag
import Shog.Model.RA.Fin
import Shog.Model.RA.All
import Shog.Model.RA.All.Index

Prop-setoid :  Setoid (^ ℓ) (^ ℓ)
Prop-setoid =  ≡-setoid (Prop' ∞)

--------------------------------------------------------------------------------
-- ExcᴾRA, AgᴾRA: Exclusive / agreement RA on Prop' ∞

module ModExcᴾ =  Shog.Model.RA.Exc Prop-setoid {^ ℓ}
open ModExcᴾ public using () renaming (ExcRA to ExcᴾRA; Exc to Excᴾ)

module ModAgᴾ =  Shog.Model.RA.Ag Prop-setoid
open ModAgᴾ public using () renaming (AgRA to AgᴾRA)

--------------------------------------------------------------------------------
-- SaveˣRA, Save□RA: Exclusive/persistent save token RA

module ModSaveˣ =  Shog.Model.RA.Fin ExcᴾRA
open ModSaveˣ public using () renaming (FinRA to SaveˣRA; Fin to Saveˣ)

module ModSave□ =  Shog.Model.RA.Fin AgᴾRA
open ModSave□ public using () renaming (FinRA to Save□RA; Fin to Save□)

--------------------------------------------------------------------------------
-- GlobRA: Global RA

pattern [saveˣ] = 0
pattern [save□] = 1

GlobRA˙ :  ℕ →  RA (^ ℓ) (^ ℓ) (^ ℓ)
GlobRA˙ [saveˣ] =  SaveˣRA
GlobRA˙ [save□] =  Save□RA
GlobRA˙ _ =  ⊤RA

module ModGlob =  Shog.Model.RA.All GlobRA˙
open ModGlob public using () renaming (AllRA to GlobRA)
open RA GlobRA public using () renaming (Car to Glob)
module ModGlobI =  Shog.Model.RA.All.Index GlobRA˙ _≡?_
