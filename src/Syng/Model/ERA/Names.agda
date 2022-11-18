--------------------------------------------------------------------------------
-- Name set ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syng.Model.ERA.Names where

open import Base.Level using (1ᴸ; ↑_; ↓)
open import Base.Eq using (_≡˙_)
open import Base.Zoi using (Zoi; ✔ᶻ_; ⊤ᶻ; _⊎ᶻ_)
open import Base.Sum using ()
open import Base.Nat using ()
open import Base.List using ()
open import Base.Str using ()
open import Syng.Logic.Prop using (Name)
open import Syng.Model.ERA.Base using (ERA; Upᴱᴿᴬ)
open import Syng.Model.ERA.Zoi using (Zoiᴱᴿᴬ)
import Syng.Model.ERA.All

private variable
  Nm Nm' :  Name → Zoi

--------------------------------------------------------------------------------
-- Namesᴱᴿᴬ :  Name set ERA

module AllNames =  Syng.Model.ERA.All Name (λ _ → Zoiᴱᴿᴬ)
open AllNames public using () renaming (
  --  Names'ᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
  ∀ᴱᴿᴬ to Names'ᴱᴿᴬ)

Namesᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
Namesᴱᴿᴬ =  Upᴱᴿᴬ Names'ᴱᴿᴬ

open ERA Namesᴱᴿᴬ public using () renaming (Res to Resᴺᵃᵐᵉˢ; _≈_ to _≈ᴺᵃᵐᵉˢ_;
  _✓_ to _✓ᴺᵃᵐᵉˢ_)

-- Own a name set

[_]ᴺʳ :  (Name → Zoi) →  Resᴺᵃᵐᵉˢ
[ Nm ]ᴺʳ .↓ =  Nm

-- Own the universal name set

[⊤]ᴺʳ :  Resᴺᵃᵐᵉˢ
[⊤]ᴺʳ =  [ ⊤ᶻ ]ᴺʳ

abstract

  -- [⊤]ᴺʳ is valid

  ✓ᴺᵃᵐᵉˢ[⊤] :  _ ✓ᴺᵃᵐᵉˢ [⊤]ᴺʳ
  ✓ᴺᵃᵐᵉˢ[⊤] =  _

  -- Update the set part of [ ]ᴺʳ

  []ᴺʳ-cong :  Nm ≡˙ Nm' →  [ Nm ]ᴺʳ ≈ᴺᵃᵐᵉˢ [ Nm' ]ᴺʳ
  []ᴺʳ-cong Nm≡Nm' .↓ =  Nm≡Nm'

  -- The set of [ ]ᴺʳ is valid

  []ᴺʳ-✔ :  _ ✓ᴺᵃᵐᵉˢ [ Nm ]ᴺʳ →  ✔ᶻ Nm
  []ᴺʳ-✔ (↑ ✔Nm) =  ✔Nm
