--------------------------------------------------------------------------------
-- Product ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Level using (Level)
open import Syho.Model.ERA.Base using (ERA)
module Syho.Model.ERA.Prod {łᴱ łᴿ ł≈ ł✓ łᴱ' łᴿ' ł≈' ł✓' : Level}
  (Era : ERA łᴱ łᴿ ł≈ ł✓) (Era' : ERA łᴱ' łᴿ' ł≈' ł✓') where

open import Base.Level using (_⊔ᴸ_)
open import Base.Prod using (_×_; π₀; π₁; _,_; -,_)

open ERA using (Env; Res; _≈_; _✓_; _∙_; ε; ⌞_⌟; refl˜; ◠˜_; _◇˜_; ⊑-refl;
  ∙-congˡ; ∙-unitˡ; ∙-comm; ∙-assocˡ; ✓-resp; ✓-rem; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ;
  ⌞⌟-idem; ⌞⌟-ε)

--------------------------------------------------------------------------------
-- ×ᴱᴿᴬ :  Product ERA

×ᴱᴿᴬ :  ERA (łᴱ ⊔ᴸ łᴱ') (łᴿ ⊔ᴸ łᴿ') (ł≈ ⊔ᴸ ł≈') (ł✓ ⊔ᴸ ł✓')
×ᴱᴿᴬ .Env =  Era .Env  ×  Era' .Env
×ᴱᴿᴬ .Res =  Era .Res  ×  Era' .Res
×ᴱᴿᴬ ._≈_ (a , a') (b , b') =  Era ._≈_ a b  ×  Era' ._≈_ a' b'
×ᴱᴿᴬ ._✓_ (E , E') (a , a') =  Era ._✓_ E a  ×  Era' ._✓_ E' a'
×ᴱᴿᴬ ._∙_ (a , a') (b , b') =  Era ._∙_ a b  ,  Era' ._∙_ a' b'
×ᴱᴿᴬ .ε =  Era .ε  ,  Era' .ε
×ᴱᴿᴬ .⌞_⌟ (a , a') =  Era .⌞_⌟ a  ,  Era' .⌞_⌟ a'
×ᴱᴿᴬ .refl˜ =  Era .refl˜  ,  Era' .refl˜
×ᴱᴿᴬ .◠˜_ (a≈b , a'≈b') =  Era .◠˜_ a≈b  ,  Era' .◠˜_ a'≈b'
×ᴱᴿᴬ ._◇˜_ (a≈b , a'≈b') (b≈c , b'≈c') =
  Era ._◇˜_ a≈b b≈c  ,  Era' ._◇˜_ a'≈b' b'≈c'
×ᴱᴿᴬ .∙-congˡ (a≈b , a'≈b') =  Era .∙-congˡ a≈b  ,  Era' .∙-congˡ a'≈b'
×ᴱᴿᴬ .∙-unitˡ =  Era .∙-unitˡ  ,  Era' .∙-unitˡ
×ᴱᴿᴬ .∙-comm =  Era .∙-comm  ,  Era' .∙-comm
×ᴱᴿᴬ .∙-assocˡ =  Era .∙-assocˡ  ,  Era' .∙-assocˡ
×ᴱᴿᴬ .✓-resp (a≈b , a'≈b') (E✓a , E'✓a') =
  Era .✓-resp a≈b E✓a  ,  Era' .✓-resp a'≈b' E'✓a'
×ᴱᴿᴬ .✓-rem (E✓a , E'✓a') =  Era .✓-rem E✓a  ,  Era' .✓-rem E'✓a'
×ᴱᴿᴬ .⌞⌟-cong (a≈b , a'≈b') =  Era .⌞⌟-cong a≈b  ,  Era' .⌞⌟-cong a'≈b'
×ᴱᴿᴬ .⌞⌟-add .π₀ =  Era .⌞⌟-add .π₀  ,  Era' .⌞⌟-add .π₀
×ᴱᴿᴬ .⌞⌟-add .π₁ =  Era .⌞⌟-add .π₁  ,  Era' .⌞⌟-add .π₁
×ᴱᴿᴬ .⌞⌟-unitˡ =  Era .⌞⌟-unitˡ  ,  Era' .⌞⌟-unitˡ
×ᴱᴿᴬ .⌞⌟-idem =  Era .⌞⌟-idem  ,  Era' .⌞⌟-idem

-- inj₀, inj₁ :  Inject a resource of a component ERA

inj₀ :  Era .Res →  ×ᴱᴿᴬ .Res
inj₀ a =  a  ,  Era' .ε

inj₁ :  Era' .Res →  ×ᴱᴿᴬ .Res
inj₁ a' =  Era .ε  ,  a'
