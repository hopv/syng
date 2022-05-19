--------------------------------------------------------------------------------
-- Global resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Model.RA.Glob (ℓ : Level) where

open import Base.Level using (sucˡ)
open import Base.Size using (∞)
open import Base.Setoid using (Setoid; ≡-setoid)
open import Shog.Logic.Prop ℓ using (Prop')
open import Shog.Model.RA using (RA)

Prop-setoid :  Setoid (sucˡ ℓ) (sucˡ ℓ)
Prop-setoid =  ≡-setoid (Prop' ∞)

--------------------------------------------------------------------------------
-- PropExcᴿᴬ, PropAgᴿᴬ: Exclusive / agreement RA on Prop' ∞

open import Shog.Model.RA.Exc Prop-setoid public using ()
  renaming (Excᴿᴬ to PropExcᴿᴬ)

open import Shog.Model.RA.Ag Prop-setoid public using ()
  renaming (Agᴿᴬ to PropAgᴿᴬ)

--------------------------------------------------------------------------------
-- Saveˣᴿᴬ, Save□ᴿᴬ: Exclusive and persistent save token RA

open import Shog.Model.RA.Fin PropExcᴿᴬ public using ()
  renaming (Finᴿᴬ to Saveˣᴿᴬ)
open RA Saveˣᴿᴬ public using () renaming (Car to Saveˣ)

open import Shog.Model.RA.Fin PropAgᴿᴬ public using ()
  renaming (Finᴿᴬ to Save□ᴿᴬ)
open RA Save□ᴿᴬ public using () renaming (Car to Save□)

--------------------------------------------------------------------------------
-- Globᴿᴬ: Global RA

open import Shog.Model.RA.Prod Saveˣᴿᴬ Save□ᴿᴬ public using ()
  renaming (Prodᴿᴬ to Globᴿᴬ; ×-injˡ to inj-Saveˣ; ×-injʳ to inj-Save□)
open RA Globᴿᴬ public using () renaming (Car to Glob)
