--------------------------------------------------------------------------------
-- Global resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Model.RA.Glob (ℓ : Level) where

open import Base.Level using (^ˡ_)
open import Base.Size using (∞)
open import Base.Setoid using (Setoid; ≡-setoid)
open import Base.Nat using (ℕ; _≡?_)
open import Shog.Logic.Prop ℓ using (Prop')
open import Shog.Model.RA using (RA)
open import Shog.Model.RA.Top using (⊤ᴿᴬ)

Prop-setoid :  Setoid (^ˡ ℓ) (^ˡ ℓ)
Prop-setoid =  ≡-setoid (Prop' ∞)

--------------------------------------------------------------------------------
-- Excᴾᴿᴬ, Agᴾᴿᴬ: Exclusive / agreement RA on Prop' ∞

open import Shog.Model.RA.Exc Prop-setoid {^ˡ ℓ} public using ()
  renaming (Excᴿᴬ to Excᴾᴿᴬ; #ˣ_ to #ˣᴾ_; #ˣ-↝ to #ˣᴾ-↝)

open import Shog.Model.RA.Ag Prop-setoid public using ()
  renaming (Agᴿᴬ to Agᴾᴿᴬ; ag to agᴾ; ✓-ag to ✓-agᴾ; agree to agreeᴾ)

--------------------------------------------------------------------------------
-- Saveˣᴿᴬ, Save□ᴿᴬ: Exclusive and persistent save token RA

open import Shog.Model.RA.Fin Excᴾᴿᴬ public using () renaming (Finᴿᴬ to Saveˣᴿᴬ;
  injᶠ to injᶠˢˣ; allocᶠ to allocᶠˢˣ)
open RA Saveˣᴿᴬ public using () renaming (Car to Saveˣ)

open import Shog.Model.RA.Fin Agᴾᴿᴬ public using () renaming (Finᴿᴬ to Save□ᴿᴬ;
  injᶠ to injᶠˢ□; injᶠ-⌞⌟ to injᶠˢ□-⌞⌟; allocᶠ to allocᶠˢ□)
open RA Save□ᴿᴬ public using () renaming (Car to Save□)

--------------------------------------------------------------------------------
-- Globᴿᴬ: Global RA

Globᴿᴬ˙ :  ℕ →  RA (^ˡ ℓ) (^ˡ ℓ) (^ˡ ℓ)
Globᴿᴬ˙ 0 =  Saveˣᴿᴬ
Globᴿᴬ˙ 1 =  Save□ᴿᴬ
Globᴿᴬ˙ _ =  ⊤ᴿᴬ

open import Shog.Model.RA.All Globᴿᴬ˙ public using () renaming (Allᴿᴬ to Globᴿᴬ)
open RA Globᴿᴬ public using () renaming (Car to Glob)
open import Shog.Model.RA.All.Index Globᴿᴬ˙ _≡?_ public using () renaming (
  injᴬ to injᴳ; injᴬ-cong to injᴳ-cong; injᴬ-✓ to injᴳ-✓; injᴬ-∙ to injᴳ-∙;
  injᴬ-ε to injᴳ-ε; injᴬ-⌞⌟ to injᴳ-⌞⌟; injᴬ-↝ to injᴳ-↝)
