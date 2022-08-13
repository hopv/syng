--------------------------------------------------------------------------------
-- Trivial ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Syho.Model.ERA.Top where

open import Base.Level using (Level)
open import Base.Few using (⊤)
open import Syho.Model.ERA using (ERA)

open ERA using (Car; Env; _≈_; _✓_; _∙_; ε; ⌞_⌟; refl˜; ◠˜_; _◇˜_; ∙-congˡ;
  ∙-unitˡ; ∙-comm; ∙-assocˡ; ✓-resp; ✓-rem; ✓-ε; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ;
  ⌞⌟-idem)

private variable
  ℓ ℓᴱ ℓ≈ ℓ✓ :  Level

--------------------------------------------------------------------------------
-- ⊤ᴱᴿᴬ : Trivial ERA

⊤ᴱᴿᴬ :  ERA ℓ ℓᴱ ℓ≈ ℓ✓
⊤ᴱᴿᴬ .Car =  ⊤
⊤ᴱᴿᴬ .Env =  ⊤
⊤ᴱᴿᴬ ._≈_ _ _ =  ⊤
⊤ᴱᴿᴬ ._✓_ _ _ =  ⊤
⊤ᴱᴿᴬ ._∙_ =  _
⊤ᴱᴿᴬ .ε =  _
⊤ᴱᴿᴬ .⌞_⌟ =  _
⊤ᴱᴿᴬ .refl˜ =  _
⊤ᴱᴿᴬ .◠˜_ =  _
⊤ᴱᴿᴬ ._◇˜_ =  _
⊤ᴱᴿᴬ .∙-congˡ =  _
⊤ᴱᴿᴬ .∙-unitˡ =  _
⊤ᴱᴿᴬ .∙-comm =  _
⊤ᴱᴿᴬ .∙-assocˡ =  _
⊤ᴱᴿᴬ .✓-resp =  _
⊤ᴱᴿᴬ .✓-rem =  _
⊤ᴱᴿᴬ .✓-ε =  _
⊤ᴱᴿᴬ .⌞⌟-cong =  _
⊤ᴱᴿᴬ .⌞⌟-add =  _
⊤ᴱᴿᴬ .⌞⌟-unitˡ =  _
⊤ᴱᴿᴬ .⌞⌟-idem =  _
