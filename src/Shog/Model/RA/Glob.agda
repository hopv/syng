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
-- Excᴾᴿᴬ, Agᴾᴿᴬ: Exclusive / agreement RA on Prop' ∞

open import Shog.Model.RA.Exc Prop-setoid {sucˡ ℓ} public using ()
  renaming (Excᴿᴬ to Excᴾᴿᴬ; #ˣ_ to #ˣᴾ_; #ˣ-↝ to #ˣᴾ-↝)

open import Shog.Model.RA.Ag Prop-setoid public using ()
  renaming (Agᴿᴬ to Agᴾᴿᴬ; ag to agᴾ; ✓-ag to ✓-agᴾ; agree to agreeᴾ)

--------------------------------------------------------------------------------
-- Saveˣᴿᴬ, Save□ᴿᴬ: Exclusive and persistent save token RA

open import Shog.Model.RA.Fin Excᴾᴿᴬ public using () renaming (Finᴿᴬ to Saveˣᴿᴬ;
  injᶠ to injᶠˢˣ; allocᶠ to allocᶠˢˣ)
open RA Saveˣᴿᴬ public using () renaming (Car to Saveˣ)

open import Shog.Model.RA.Fin Agᴾᴿᴬ public using () renaming (Finᴿᴬ to Save□ᴿᴬ;
  injᶠ to injᶠˢ□; allocᶠ to allocᶠˢ□)
open RA Save□ᴿᴬ public using () renaming (Car to Save□)

--------------------------------------------------------------------------------
-- Globᴿᴬ: Global RA

open import Shog.Model.RA.Prod Saveˣᴿᴬ Save□ᴿᴬ public using ()
  renaming (Prodᴿᴬ to Globᴿᴬ; ×-injˡ to injˢˣ; ×-injʳ to injˢ□)
open RA Globᴿᴬ public using () renaming (Car to Glob)
