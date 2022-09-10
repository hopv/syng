--------------------------------------------------------------------------------
-- Level-up ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Level using (Level)
open import Syho.Model.ERA.Base using (ERA)
module Syho.Model.ERA.Up {łᴱ łᴿ ł≈ ł✓ : Level} (Era : ERA łᴱ łᴿ ł≈ ł✓)
  {łᴱ' łᴿ' ł≈' ł✓' : Level} where

open import Base.Level using (_⊔ᴸ_; Up; ↑_; ↓)
open import Base.Prod using (_×_; π₀; π₁; _,_; -,_)

open ERA using (Env; Res; _≈_; _✓_; _∙_; ε; ⌞_⌟; refl˜; ◠˜_; _◇˜_; ⊑-refl;
  ∙-congˡ; ∙-unitˡ; ∙-comm; ∙-assocˡ; ✓-resp; ✓-rem; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ;
  ⌞⌟-idem; ⌞⌟-ε)

--------------------------------------------------------------------------------
-- Upᴱᴿᴬ :  Level-up ERA

Upᴱᴿᴬ :  ERA (łᴱ ⊔ᴸ łᴱ') (łᴿ ⊔ᴸ łᴿ') (ł≈ ⊔ᴸ ł≈') (ł✓ ⊔ᴸ ł✓')
Upᴱᴿᴬ .Env =  Up (Era .Env) {łᴱ'}
Upᴱᴿᴬ .Res =  Up (Era .Res) {łᴿ'}
Upᴱᴿᴬ ._≈_ (↑ a) (↑ b) =  Up (Era ._≈_ a b) {ł≈'}
Upᴱᴿᴬ ._✓_ (↑ E) (↑ a) =  Up (Era ._✓_ E a) {ł✓'}
Upᴱᴿᴬ ._∙_ (↑ a) (↑ b) .↓ =  Era ._∙_ a b
Upᴱᴿᴬ .ε .↓ =  Era .ε
Upᴱᴿᴬ .⌞_⌟ (↑ a) .↓ =  Era .⌞_⌟ a
Upᴱᴿᴬ .refl˜ .↓ =  Era .refl˜
Upᴱᴿᴬ .◠˜_ (↑ a≈b) .↓ =  Era .◠˜_ a≈b
Upᴱᴿᴬ ._◇˜_ (↑ a≈b) (↑ b≈c) .↓ =  Era ._◇˜_ a≈b b≈c
Upᴱᴿᴬ .∙-congˡ (↑ a≈b) .↓ =  Era .∙-congˡ a≈b
Upᴱᴿᴬ .∙-unitˡ .↓ =  Era .∙-unitˡ
Upᴱᴿᴬ .∙-comm .↓ =  Era .∙-comm
Upᴱᴿᴬ .∙-assocˡ .↓ =  Era .∙-assocˡ
Upᴱᴿᴬ .✓-resp (↑ a≈b) (↑ E✓a) .↓ =  Era .✓-resp a≈b E✓a
Upᴱᴿᴬ .✓-rem (↑ E✓a∙b) .↓ =  Era .✓-rem E✓a∙b
Upᴱᴿᴬ .⌞⌟-cong (↑ a≈b) .↓ =  Era .⌞⌟-cong a≈b
Upᴱᴿᴬ .⌞⌟-add .π₀ .↓ =  Era .⌞⌟-add .π₀
Upᴱᴿᴬ .⌞⌟-add .π₁ .↓ =  Era .⌞⌟-add .π₁
Upᴱᴿᴬ .⌞⌟-unitˡ .↓ =  Era .⌞⌟-unitˡ
Upᴱᴿᴬ .⌞⌟-idem .↓ =  Era .⌞⌟-idem