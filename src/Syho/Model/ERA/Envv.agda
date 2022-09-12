--------------------------------------------------------------------------------
-- Environment validity ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Level using (Level)
open import Syho.Model.ERA.Base using (ERA)
open ERA using (Env)
module Syho.Model.ERA.Envv {łᴱ łᴿ ł≈ ł✓ : Level} (Era : ERA łᴱ łᴿ ł≈ ł✓)
  {ł✓' : Level} (✓'_ : Era .Env → Set ł✓') where

open import Base.Level using (_⊔ᴸ_)
open import Base.Prod using (_×_; _,_)

open ERA using (Res; _≈_; _✓_; _∙_; ε; ⌞_⌟; refl˜; ◠˜_; _◇˜_; ⊑-refl; ∙-congˡ;
  ∙-unitˡ; ∙-comm; ∙-assocˡ; ✓-resp; ✓-rem; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem;
  ⌞⌟-ε)

--------------------------------------------------------------------------------
-- Envvᴱᴿᴬ :  Environment validity ERA

Envvᴱᴿᴬ :  ERA łᴱ łᴿ ł≈ (ł✓ ⊔ᴸ ł✓')
Envvᴱᴿᴬ .Env =  Era .Env
Envvᴱᴿᴬ .Res =  Era .Res
Envvᴱᴿᴬ ._≈_ =  Era ._≈_
Envvᴱᴿᴬ ._✓_ E a =   ✓' E  ×  Era ._✓_ E a
Envvᴱᴿᴬ ._∙_ =  Era ._∙_
Envvᴱᴿᴬ .ε =  Era .ε
Envvᴱᴿᴬ .⌞_⌟ =  Era .⌞_⌟
Envvᴱᴿᴬ .refl˜ =  Era .refl˜
Envvᴱᴿᴬ .◠˜_ =  Era .◠˜_
Envvᴱᴿᴬ ._◇˜_ =  Era ._◇˜_
Envvᴱᴿᴬ .∙-congˡ =  Era .∙-congˡ
Envvᴱᴿᴬ .∙-unitˡ =  Era .∙-unitˡ
Envvᴱᴿᴬ .∙-comm =  Era .∙-comm
Envvᴱᴿᴬ .∙-assocˡ =  Era .∙-assocˡ
Envvᴱᴿᴬ .✓-resp a≈b (✓E , E✓a) =  ✓E  ,  Era .✓-resp a≈b E✓a
Envvᴱᴿᴬ .✓-rem (✓E , E✓a∙b) =  ✓E  ,  Era .✓-rem E✓a∙b
Envvᴱᴿᴬ .⌞⌟-cong =  Era .⌞⌟-cong
Envvᴱᴿᴬ .⌞⌟-add =  Era .⌞⌟-add
Envvᴱᴿᴬ .⌞⌟-unitˡ =  Era .⌞⌟-unitˡ
Envvᴱᴿᴬ .⌞⌟-idem =  Era .⌞⌟-idem
