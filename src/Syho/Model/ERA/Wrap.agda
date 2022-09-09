--------------------------------------------------------------------------------
-- Wrap ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Level using (Level)
open import Syho.Model.ERA.Base using (ERA)
open ERA using (Env)
module Syho.Model.ERA.Wrap {łᴱ łᴿ ł≈ ł✓ : Level} (Era : ERA łᴱ łᴿ ł≈ ł✓)
  {łᴱ' ł✓' : Level} {Env' : Set łᴱ'} (H : Env' → Era .Env)
  (✓'_ : Env' → Set ł✓') where

open import Base.Level using (_⊔ᴸ_)
open import Base.Prod using (_×_; _,_)

open ERA using (Res; _≈_; _✓_; _∙_; ε; ⌞_⌟; refl˜; ◠˜_; _◇˜_; ⊑-refl; ∙-congˡ;
  ∙-unitˡ; ∙-comm; ∙-assocˡ; ✓-resp; ✓-rem; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem;
  ⌞⌟-ε)

--------------------------------------------------------------------------------
-- Wrapᴱᴿᴬ :  Wrap ERA, modifying the environment and the validity predicate of
--            the base ERA

Wrapᴱᴿᴬ :  ERA łᴱ' łᴿ ł≈ (ł✓ ⊔ᴸ ł✓')
Wrapᴱᴿᴬ .Env =  Env'
Wrapᴱᴿᴬ .Res =  Era .Res
Wrapᴱᴿᴬ ._≈_ =  Era ._≈_
Wrapᴱᴿᴬ ._✓_ E a =   ✓' E  ×  Era ._✓_ (H E) a
Wrapᴱᴿᴬ ._∙_ =  Era ._∙_
Wrapᴱᴿᴬ .ε =  Era .ε
Wrapᴱᴿᴬ .⌞_⌟ =  Era .⌞_⌟
Wrapᴱᴿᴬ .refl˜ =  Era .refl˜
Wrapᴱᴿᴬ .◠˜_ =  Era .◠˜_
Wrapᴱᴿᴬ ._◇˜_ =  Era ._◇˜_
Wrapᴱᴿᴬ .∙-congˡ =  Era .∙-congˡ
Wrapᴱᴿᴬ .∙-unitˡ =  Era .∙-unitˡ
Wrapᴱᴿᴬ .∙-comm =  Era .∙-comm
Wrapᴱᴿᴬ .∙-assocˡ =  Era .∙-assocˡ
Wrapᴱᴿᴬ .✓-resp a≈b (✓E , HE✓a) =  ✓E , Era .✓-resp a≈b HE✓a
Wrapᴱᴿᴬ .✓-rem (✓E , HE✓a∙b) =  ✓E , Era .✓-rem HE✓a∙b
Wrapᴱᴿᴬ .⌞⌟-cong =  Era .⌞⌟-cong
Wrapᴱᴿᴬ .⌞⌟-add =  Era .⌞⌟-add
Wrapᴱᴿᴬ .⌞⌟-unitˡ =  Era .⌞⌟-unitˡ
Wrapᴱᴿᴬ .⌞⌟-idem =  Era .⌞⌟-idem
