--------------------------------------------------------------------------------
-- Global ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Glob where

open import Base.Level using (2ᴸ)
open import Base.Nat using (ℕ; ṡ_)
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Top using (⊤ᴱᴿᴬ)
open import Syho.Model.ERA.Mem using (Memᴱᴿᴬ)
open import Syho.Model.ERA.Ind using (Indˣᴱᴿᴬ; Indᵖᴱᴿᴬ)

--------------------------------------------------------------------------------
-- Global ERA

-- Ids of ERAs

pattern mem =  0
pattern indˣ =  1
pattern indᵖ =  2
pattern elseᴳ =  ṡ ṡ ṡ _

-- Map of ERAs

Globᴱᴿᴬ˙ :  ℕ →  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ
Globᴱᴿᴬ˙ mem =  Memᴱᴿᴬ
Globᴱᴿᴬ˙ indˣ =  Indˣᴱᴿᴬ
Globᴱᴿᴬ˙ indᵖ =  Indᵖᴱᴿᴬ
Globᴱᴿᴬ˙ elseᴳ =  ⊤ᴱᴿᴬ

-- Globᴱᴿᴬ :  Global ERA, defined as ∀ᴱᴿᴬ Globᴱᴿᴬ˙

import Syho.Model.ERA.All
module AllGlob =  Syho.Model.ERA.All Globᴱᴿᴬ˙

-- Re-export AllGlob
open AllGlob public

-- Aliases
open AllGlob public using () renaming (
  -- Globᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ
  ∀ᴱᴿᴬ to Globᴱᴿᴬ;
  -- Envᴳ :  Set 2ᴸ
  Env˙ to Envᴳ;
  -- Resᴳ :  Set 2ᴸ
  Res˙ to Resᴳ)
