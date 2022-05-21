--------------------------------------------------------------------------------
-- Trivial resource algebra
--------------------------------------------------------------------------------

open import Base.Level using (Level)
module Shog.Model.RA.Top {ℓ ℓ≈ ℓ✓ : Level} where

open import Base.Few using (⊤)
open import Shog.Model.RA using (RA)

--------------------------------------------------------------------------------
-- ⊤ᴿᴬ : Trivial resource algebra

open RA
⊤ᴿᴬ :  RA ℓ ℓ≈ ℓ✓
⊤ᴿᴬ .Car =  ⊤
⊤ᴿᴬ ._≈_ _ _ =  ⊤
⊤ᴿᴬ .✓_ _ =  ⊤
⊤ᴿᴬ ._∙_ =  _
⊤ᴿᴬ .ε =  _
⊤ᴿᴬ .⌞_⌟ =  _
⊤ᴿᴬ .refl˜ =  _
⊤ᴿᴬ .sym˜ =  _
⊤ᴿᴬ ._»˜_ =  _
⊤ᴿᴬ .∙-congˡ =  _
⊤ᴿᴬ .∙-unitˡ =  _
⊤ᴿᴬ .∙-comm =  _
⊤ᴿᴬ .∙-assocˡ =  _
⊤ᴿᴬ .✓-resp =  _
⊤ᴿᴬ .✓-rem =  _
⊤ᴿᴬ .✓-ε =  _
⊤ᴿᴬ .⌞⌟-cong =  _
⊤ᴿᴬ .⌞⌟-add =  _
⊤ᴿᴬ .⌞⌟-unitˡ =  _
⊤ᴿᴬ .⌞⌟-idem =  _
