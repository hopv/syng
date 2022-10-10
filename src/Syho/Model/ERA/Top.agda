--------------------------------------------------------------------------------
-- Trivial ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Syho.Model.ERA.Top where

open import Base.Level using (Level)
open import Base.Few using (⊤)
open import Syho.Model.ERA.Base using (ERA)

open ERA using (Res; _≈_; _∙_; ε; ⌞_⌟; Env; _✓_; refl˜; ◠˜_; _◇˜_; ∙-congˡ;
  ∙-unitˡ; ∙-comm; ∙-assocˡ; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem; ✓-resp; ✓-rem)

private variable
  ł ł≈ łᴱ ł✓ :  Level

--------------------------------------------------------------------------------
-- ⊤ᴱᴿᴬ : Trivial ERA

⊤ᴱᴿᴬ :  ERA ł ł≈ łᴱ ł✓
⊤ᴱᴿᴬ .Res =  ⊤
⊤ᴱᴿᴬ ._≈_ _ _ =  ⊤
⊤ᴱᴿᴬ ._∙_ =  _
⊤ᴱᴿᴬ .ε =  _
⊤ᴱᴿᴬ .⌞_⌟ =  _
⊤ᴱᴿᴬ .Env =  ⊤
⊤ᴱᴿᴬ ._✓_ _ _ =  ⊤
⊤ᴱᴿᴬ .refl˜ =  _
⊤ᴱᴿᴬ .◠˜_ =  _
⊤ᴱᴿᴬ ._◇˜_ =  _
⊤ᴱᴿᴬ .∙-congˡ =  _
⊤ᴱᴿᴬ .∙-unitˡ =  _
⊤ᴱᴿᴬ .∙-comm =  _
⊤ᴱᴿᴬ .∙-assocˡ =  _
⊤ᴱᴿᴬ .⌞⌟-cong =  _
⊤ᴱᴿᴬ .⌞⌟-add =  _
⊤ᴱᴿᴬ .⌞⌟-unitˡ =  _
⊤ᴱᴿᴬ .⌞⌟-idem =  _
⊤ᴱᴿᴬ .✓-resp =  _
⊤ᴱᴿᴬ .✓-rem =  _
