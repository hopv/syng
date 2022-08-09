--------------------------------------------------------------------------------
-- Global resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.RA.Glob where

open import Base.Level using (2ᴸ)
open import Base.Size using (∞)
open import Base.Setoid using (Setoid; ≡-setoid)
open import Base.Nat using (ℕ; _≡?_)
open import Syho.Logic.Prop using (Prop')
open import Syho.Model.RA using (RA)
open import Syho.Model.RA.Top using (⊤RA)

import Syho.Model.RA.Exc
import Syho.Model.RA.Ag
import Syho.Model.RA.Finmap
import Syho.Model.RA.All
import Syho.Model.RA.All.Index

Prop-setoid :  Setoid 2ᴸ 2ᴸ
Prop-setoid =  ≡-setoid (Prop' ∞)

--------------------------------------------------------------------------------
-- ExcᴾRA, AgᴾRA: Exclusive / agreement RA on Prop' ∞

module ModExcᴾ =  Syho.Model.RA.Exc Prop-setoid {2ᴸ}
open ModExcᴾ public using () renaming (ExcRA to ExcᴾRA; Exc to Excᴾ)

module ModAgᴾ =  Syho.Model.RA.Ag Prop-setoid
open ModAgᴾ public using () renaming (AgRA to AgᴾRA)

--------------------------------------------------------------------------------
-- SaveˣRA, Save□RA: Exclusive/persistent save token RA

module ModSaveˣ =  Syho.Model.RA.Finmap ExcᴾRA
open ModSaveˣ public using () renaming (FinmapRA to SaveˣRA; Finmap to Saveˣ)

module ModSave□ =  Syho.Model.RA.Finmap AgᴾRA
open ModSave□ public using () renaming (FinmapRA to Save□RA; Finmap to Save□)

--------------------------------------------------------------------------------
-- GlobRA: Global RA

pattern [Saveˣ] = 0
pattern [Save□] = 1

GlobRA˙ :  ℕ →  RA 2ᴸ 2ᴸ 2ᴸ
GlobRA˙ [Saveˣ] =  SaveˣRA
GlobRA˙ [Save□] =  Save□RA
GlobRA˙ _ =  ⊤RA

module ModGlob =  Syho.Model.RA.All GlobRA˙
open ModGlob public using () renaming (AllRA to GlobRA)
open RA GlobRA public using () renaming (Car to Glob)
module ModGlobI =  Syho.Model.RA.All.Index GlobRA˙ _≡?_
