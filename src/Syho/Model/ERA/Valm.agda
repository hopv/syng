--------------------------------------------------------------------------------
-- Validity modification ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.Prod using (_×_; _,_)
open import Syho.Model.ERA.Base using (ERA)
open ERA using (Res; _≈_; _∙_; Env)
module Syho.Model.ERA.Valm {łᴿ ł≈ łᴱ ł✓ ł✓' : Level} (Era : ERA łᴿ ł≈ łᴱ ł✓)
  (_✓'_ :  Era .Env → Era .Res → Set ł✓')
  (✓'-resp :  ∀{E a b} →  Era ._≈_ a b →  E ✓' a →  E ✓' b)
  (✓'-rem :  ∀{E a b} →  E ✓' Era ._∙_ a b →  E ✓' b) where

open ERA using (ε; ⌞_⌟; _✓_; refl˜; ◠˜_; _◇˜_; ∙-congˡ; ∙-unitˡ; ∙-comm;
  ∙-assocˡ; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem; ✓-resp; ✓-rem)

--------------------------------------------------------------------------------
-- Valmᴱᴿᴬ :  Validity modification ERA

Valmᴱᴿᴬ :  ERA łᴿ ł≈ łᴱ (ł✓' ⊔ᴸ ł✓)
Valmᴱᴿᴬ .Res =  Era .Res
Valmᴱᴿᴬ ._≈_ =  Era ._≈_
Valmᴱᴿᴬ ._∙_ =  Era ._∙_
Valmᴱᴿᴬ .ε =  Era .ε
Valmᴱᴿᴬ .⌞_⌟ =  Era .⌞_⌟
Valmᴱᴿᴬ .Env =  Era .Env
Valmᴱᴿᴬ ._✓_ E a =  E ✓' a  ×  Era ._✓_ E a
Valmᴱᴿᴬ .refl˜ =  Era .refl˜
Valmᴱᴿᴬ .◠˜_ =  Era .◠˜_
Valmᴱᴿᴬ ._◇˜_ =  Era ._◇˜_
Valmᴱᴿᴬ .∙-congˡ =  Era .∙-congˡ
Valmᴱᴿᴬ .∙-unitˡ =  Era .∙-unitˡ
Valmᴱᴿᴬ .∙-comm =  Era .∙-comm
Valmᴱᴿᴬ .∙-assocˡ =  Era .∙-assocˡ
Valmᴱᴿᴬ .⌞⌟-cong =  Era .⌞⌟-cong
Valmᴱᴿᴬ .⌞⌟-add =  Era .⌞⌟-add
Valmᴱᴿᴬ .⌞⌟-unitˡ =  Era .⌞⌟-unitˡ
Valmᴱᴿᴬ .⌞⌟-idem =  Era .⌞⌟-idem
Valmᴱᴿᴬ .✓-resp a≈b (E✓'a , E✓a) =  ✓'-resp a≈b E✓'a , Era .✓-resp a≈b E✓a
Valmᴱᴿᴬ .✓-rem (E✓'a∙b , E✓a∙b) =  ✓'-rem E✓'a∙b , Era .✓-rem E✓a∙b
