--------------------------------------------------------------------------------
-- Environment modification ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Level using (Level)
open import Syho.Model.ERA.Base using (ERA)
open ERA using (Env)
module Syho.Model.ERA.Envm {łᴱ łᴿ ł≈ ł✓ : Level} (Era : ERA łᴱ łᴿ ł≈ ł✓)
  {łᴱ' : Level} (Env' : Set łᴱ') (H : Env' → Era .Env) where

open ERA using (Res; _≈_; _✓_; _∙_; ε; ⌞_⌟; refl˜; ◠˜_; _◇˜_; ⊑-refl; ∙-congˡ;
  ∙-unitˡ; ∙-comm; ∙-assocˡ; ✓-resp; ✓-rem; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem;
  ⌞⌟-ε)

--------------------------------------------------------------------------------
-- Envmᴱᴿᴬ :  Environment modification ERA

Envmᴱᴿᴬ :  ERA łᴱ' łᴿ ł≈ ł✓
Envmᴱᴿᴬ .Env =  Env'
Envmᴱᴿᴬ .Res =  Era .Res
Envmᴱᴿᴬ ._≈_ =  Era ._≈_
Envmᴱᴿᴬ ._✓_ E =   Era ._✓_ (H E)
Envmᴱᴿᴬ ._∙_ =  Era ._∙_
Envmᴱᴿᴬ .ε =  Era .ε
Envmᴱᴿᴬ .⌞_⌟ =  Era .⌞_⌟
Envmᴱᴿᴬ .refl˜ =  Era .refl˜
Envmᴱᴿᴬ .◠˜_ =  Era .◠˜_
Envmᴱᴿᴬ ._◇˜_ =  Era ._◇˜_
Envmᴱᴿᴬ .∙-congˡ =  Era .∙-congˡ
Envmᴱᴿᴬ .∙-unitˡ =  Era .∙-unitˡ
Envmᴱᴿᴬ .∙-comm =  Era .∙-comm
Envmᴱᴿᴬ .∙-assocˡ =  Era .∙-assocˡ
Envmᴱᴿᴬ .✓-resp a≈b HE✓a =  Era .✓-resp a≈b HE✓a
Envmᴱᴿᴬ .✓-rem HE✓a∙b =  Era .✓-rem HE✓a∙b
Envmᴱᴿᴬ .⌞⌟-cong =  Era .⌞⌟-cong
Envmᴱᴿᴬ .⌞⌟-add =  Era .⌞⌟-add
Envmᴱᴿᴬ .⌞⌟-unitˡ =  Era .⌞⌟-unitˡ
Envmᴱᴿᴬ .⌞⌟-idem =  Era .⌞⌟-idem
