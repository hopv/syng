--------------------------------------------------------------------------------
-- Global resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Glob where

open import Base.Level using (2ᴸ)
open import Base.Size using (∞)
open import Base.Setoid using (Setoid; ≡-setoid)
open import Base.Nat using (ℕ; _≡?_)
open import Syho.Logic.Prop using (Prop')
open import Syho.Model.ERA using (ERA)
open import Syho.Model.ERA.Top using (⊤ERA)

import Syho.Model.ERA.Exc
import Syho.Model.ERA.Ag
import Syho.Model.ERA.Finmap
import Syho.Model.ERA.All
import Syho.Model.ERA.All.Index

Prop-setoid :  Setoid 2ᴸ 2ᴸ
Prop-setoid =  ≡-setoid (Prop' ∞)

--------------------------------------------------------------------------------
-- ExcᴾRA, AgᴾRA :  Exclusive / agreement ERA on Prop' ∞

module ModExcᴾ =  Syho.Model.ERA.Exc Prop-setoid {2ᴸ}
open ModExcᴾ public using () renaming (ExcRA to ExcᴾRA; Exc to Excᴾ)

module ModAgᴾ =  Syho.Model.ERA.Ag Prop-setoid
open ModAgᴾ public using () renaming (AgRA to AgᴾRA)

--------------------------------------------------------------------------------
-- SaveˣRA, Save□ERA :  Exclusive/persistent save token ERA

module ModSaveˣ =  Syho.Model.ERA.Finmap ExcᴾRA
open ModSaveˣ public using () renaming (FinmapRA to SaveˣRA; Finmap to Saveˣ)

module ModSave□ =  Syho.Model.ERA.Finmap AgᴾRA
open ModSave□ public using () renaming (FinmapRA to Save□ERA; Finmap to Save□)

--------------------------------------------------------------------------------
-- GlobRA :  Global ERA

pattern [Saveˣ] = 0
pattern [Save□] = 1

GlobRA˙ :  ℕ →  ERA 2ᴸ 2ᴸ 2ᴸ
GlobRA˙ [Saveˣ] =  SaveˣRA
GlobRA˙ [Save□] =  Save□ERA
GlobRA˙ _ =  ⊤ERA

module ModGlob =  Syho.Model.ERA.All GlobRA˙
open ModGlob public using () renaming (AllRA to GlobRA)
open ERA GlobRA public using () renaming (Car to Glob)
module ModGlobI =  Syho.Model.ERA.All.Index GlobRA˙ _≡?_
