--------------------------------------------------------------------------------
-- Zoi ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Syng.Model.ERA.Zoi where

open import Base.Level using (0ᴸ)
open import Base.Func using (id)
open import Base.Few using (⊤)
open import Base.Eq using (_≡_; refl; ◠_; _◇_)
open import Base.Zoi using (Zoi; ✓ᶻ_; 0ᶻ; _+ᶻ_; +ᶻ-comm; +ᶻ-assocʳ; ✓ᶻ-rem)
open import Base.Prod using (_,_)
open import Syng.Model.ERA.Base using (ERA)

open ERA using (Res; _≈_; _∙_; ε; ⌞_⌟; Env; _✓_; refl˜; ◠˜_; _◇˜_; ∙-congˡ;
  ∙-unitˡ; ∙-comm; ∙-assocʳ; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem; ✓-resp; ✓-rem)

--------------------------------------------------------------------------------
-- Zoiᴱᴿᴬ :  Zoi ERA

Zoiᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
Zoiᴱᴿᴬ .Res =  Zoi
Zoiᴱᴿᴬ ._≈_ =  _≡_
Zoiᴱᴿᴬ ._∙_ =  _+ᶻ_
Zoiᴱᴿᴬ .ε =  0ᶻ
Zoiᴱᴿᴬ .⌞_⌟ _ =  0ᶻ
Zoiᴱᴿᴬ .Env =  ⊤
Zoiᴱᴿᴬ ._✓_ _ =  ✓ᶻ_
Zoiᴱᴿᴬ .refl˜ =  refl
Zoiᴱᴿᴬ .◠˜_ =  ◠_
Zoiᴱᴿᴬ ._◇˜_ =  _◇_
Zoiᴱᴿᴬ .∙-congˡ refl =  refl
Zoiᴱᴿᴬ .∙-unitˡ =  refl
Zoiᴱᴿᴬ .∙-comm {a = n} =  +ᶻ-comm {n}
Zoiᴱᴿᴬ .∙-assocʳ {a = n} =  +ᶻ-assocʳ {n}
Zoiᴱᴿᴬ .⌞⌟-cong _ =  refl
Zoiᴱᴿᴬ .⌞⌟-add =  0ᶻ , refl
Zoiᴱᴿᴬ .⌞⌟-unitˡ =  refl
Zoiᴱᴿᴬ .⌞⌟-idem =  refl
Zoiᴱᴿᴬ .✓-resp refl =  id
Zoiᴱᴿᴬ .✓-rem {a = n} =  ✓ᶻ-rem {n}
