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
open import Shog.Model.RA.Top using (⊤ᴿᴬ)

import Shog.Model.RA.Exc
import Shog.Model.RA.Ag
import Shog.Model.RA.Fin
import Shog.Model.RA.All
import Shog.Model.RA.All.Index

Prop-setoid :  Setoid (^ ℓ) (^ ℓ)
Prop-setoid =  ≡-setoid (Prop' ∞)

--------------------------------------------------------------------------------
-- Excᴾᴿᴬ, Agᴾᴿᴬ: Exclusive / agreement RA on Prop' ∞

module ModExcᴾ =  Shog.Model.RA.Exc Prop-setoid {^ ℓ}
open ModExcᴾ public using () renaming (Excᴿᴬ to Excᴾᴿᴬ; Exc to Excᴾ)

module ModAgᴾ =  Shog.Model.RA.Ag Prop-setoid
open ModAgᴾ public using () renaming (Agᴿᴬ to Agᴾᴿᴬ)

--------------------------------------------------------------------------------
-- Saveˣᴿᴬ, Save□ᴿᴬ: Exclusive/persistent save token RA

module ModSaveˣ =  Shog.Model.RA.Fin Excᴾᴿᴬ
open ModSaveˣ public using () renaming (Finᴿᴬ to Saveˣᴿᴬ; Fin to Saveˣ)

module ModSave□ =  Shog.Model.RA.Fin Agᴾᴿᴬ
open ModSave□ public using () renaming (Finᴿᴬ to Save□ᴿᴬ; Fin to Save□)

--------------------------------------------------------------------------------
-- Globᴿᴬ: Global RA

Globᴿᴬ˙ :  ℕ →  RA (^ ℓ) (^ ℓ) (^ ℓ)
Globᴿᴬ˙ 0 =  Saveˣᴿᴬ
Globᴿᴬ˙ 1 =  Save□ᴿᴬ
Globᴿᴬ˙ _ =  ⊤ᴿᴬ

module ModGlob =  Shog.Model.RA.All Globᴿᴬ˙
open ModGlob public using () renaming (Allᴿᴬ to Globᴿᴬ)
open RA Globᴿᴬ public using () renaming (Car to Glob)
module ModGlobI =  Shog.Model.RA.All.Index Globᴿᴬ˙ _≡?_
