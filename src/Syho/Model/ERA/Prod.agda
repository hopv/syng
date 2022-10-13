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
