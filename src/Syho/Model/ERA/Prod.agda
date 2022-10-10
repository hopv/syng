--------------------------------------------------------------------------------
-- Product ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Level using (Level)
open import Syho.Model.ERA.Base using (ERA)
module Syho.Model.ERA.Prod {łᴿ ł≈ łᴱ ł✓ łᴿ' ł≈' łᴱ' ł✓' : Level}
  (Era : ERA łᴿ ł≈ łᴱ ł✓) (Era' : ERA łᴿ' ł≈' łᴱ' ł✓') where

open import Base.Level using (_⊔ᴸ_)
open import Base.Prod using (_×_; π₀; π₁; _,_; -,_)

open ERA using (Res; _≈_; _∙_; ε; ⌞_⌟; Env; _✓_; refl˜; ◠˜_; _◇˜_; ∙-congˡ;
  ∙-unitˡ; ∙-comm; ∙-assocˡ; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem; ✓-resp; ✓-rem)

--------------------------------------------------------------------------------
-- ×ᴱᴿᴬ :  Product ERA

×ᴱᴿᴬ :  ERA (łᴿ ⊔ᴸ łᴿ') (ł≈ ⊔ᴸ ł≈') (łᴱ ⊔ᴸ łᴱ') (ł✓ ⊔ᴸ ł✓')
×ᴱᴿᴬ .Res =  Era .Res  ×  Era' .Res
×ᴱᴿᴬ ._≈_ (a , a') (b , b') =  Era ._≈_ a b  ×  Era' ._≈_ a' b'
×ᴱᴿᴬ ._∙_ (a , a') (b , b') =  Era ._∙_ a b  ,  Era' ._∙_ a' b'
×ᴱᴿᴬ .ε =  Era .ε  ,  Era' .ε
×ᴱᴿᴬ .⌞_⌟ (a , a') =  Era .⌞_⌟ a  ,  Era' .⌞_⌟ a'
×ᴱᴿᴬ .Env =  Era .Env  ×  Era' .Env
×ᴱᴿᴬ ._✓_ (E , E') (a , a') =  Era ._✓_ E a  ×  Era' ._✓_ E' a'
×ᴱᴿᴬ .refl˜ =  Era .refl˜  ,  Era' .refl˜
×ᴱᴿᴬ .◠˜_ (a≈b , a'≈b') =  Era .◠˜_ a≈b  ,  Era' .◠˜_ a'≈b'
×ᴱᴿᴬ ._◇˜_ (a≈b , a'≈b') (b≈c , b'≈c') =
  Era ._◇˜_ a≈b b≈c  ,  Era' ._◇˜_ a'≈b' b'≈c'
×ᴱᴿᴬ .∙-congˡ (a≈b , a'≈b') =  Era .∙-congˡ a≈b  ,  Era' .∙-congˡ a'≈b'
×ᴱᴿᴬ .∙-unitˡ =  Era .∙-unitˡ  ,  Era' .∙-unitˡ
×ᴱᴿᴬ .∙-comm =  Era .∙-comm  ,  Era' .∙-comm
×ᴱᴿᴬ .∙-assocˡ =  Era .∙-assocˡ  ,  Era' .∙-assocˡ
×ᴱᴿᴬ .⌞⌟-cong (a≈b , a'≈b') =  Era .⌞⌟-cong a≈b  ,  Era' .⌞⌟-cong a'≈b'
×ᴱᴿᴬ .⌞⌟-add .π₀ =  Era .⌞⌟-add .π₀  ,  Era' .⌞⌟-add .π₀
×ᴱᴿᴬ .⌞⌟-add .π₁ =  Era .⌞⌟-add .π₁  ,  Era' .⌞⌟-add .π₁
×ᴱᴿᴬ .⌞⌟-unitˡ =  Era .⌞⌟-unitˡ  ,  Era' .⌞⌟-unitˡ
×ᴱᴿᴬ .⌞⌟-idem =  Era .⌞⌟-idem  ,  Era' .⌞⌟-idem
×ᴱᴿᴬ .✓-resp (a≈b , a'≈b') (E✓a , E'✓a') =
  Era .✓-resp a≈b E✓a  ,  Era' .✓-resp a'≈b' E'✓a'
×ᴱᴿᴬ .✓-rem (E✓a , E'✓a') =  Era .✓-rem E✓a  ,  Era' .✓-rem E'✓a'
