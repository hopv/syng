--------------------------------------------------------------------------------
-- Global resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Model.RA.Glob where

open import Base.Level using (2ᴸ)
open import Base.Size using (∞)
open import Base.Setoid using (Setoid; ≡-setoid)
open import Base.Nat using (ℕ; _≡?_)
open import Shog.Logic.Prop using (Prop')
open import Shog.Model.RA using (RA)
open import Shog.Model.RA.Top using (⊤RA)

import Shog.Model.RA.Exc
import Shog.Model.RA.Ag
import Shog.Model.RA.Finmap
import Shog.Model.RA.All
import Shog.Model.RA.All.Index

Prop-setoid :  Setoid 2ᴸ 2ᴸ
Prop-setoid =  ≡-setoid (Prop' ∞)

--------------------------------------------------------------------------------
-- ExcᴾRA, AgᴾRA: Exclusive / agreement RA on Prop' ∞

module ModExcᴾ =  Shog.Model.RA.Exc Prop-setoid {2ᴸ}
open ModExcᴾ public using () renaming (ExcRA to ExcᴾRA; Exc to Excᴾ)

module ModAgᴾ =  Shog.Model.RA.Ag Prop-setoid
open ModAgᴾ public using () renaming (AgRA to AgᴾRA)

--------------------------------------------------------------------------------
-- SaveˣRA, Save□RA: Exclusive/persistent save token RA

module ModSaveˣ =  Shog.Model.RA.Finmap ExcᴾRA
open ModSaveˣ public using () renaming (FinmapRA to SaveˣRA; Finmap to Saveˣ)

module ModSave□ =  Shog.Model.RA.Finmap AgᴾRA
open ModSave□ public using () renaming (FinmapRA to Save□RA; Finmap to Save□)

--------------------------------------------------------------------------------
-- GlobRA: Global RA

pattern [Saveˣ] = 0
pattern [Save□] = 1

GlobRA˙ :  ℕ →  RA 2ᴸ 2ᴸ 2ᴸ
GlobRA˙ [Saveˣ] =  SaveˣRA
GlobRA˙ [Save□] =  Save□RA
GlobRA˙ _ =  ⊤RA

module ModGlob =  Shog.Model.RA.All GlobRA˙
open ModGlob public using () renaming (AllRA to GlobRA)
open RA GlobRA public using () renaming (Car to Glob)
module ModGlobI =  Shog.Model.RA.All.Index GlobRA˙ _≡?_
