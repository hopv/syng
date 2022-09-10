--------------------------------------------------------------------------------
-- Memory ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Mem where

open import Base.Level using (0ᴸ; 1ᴸ; 2ᴸ; ↓)
open import Base.Func using (_∘_)
open import Base.Few using (binary)
open import Base.Nat using (ℕ)
open import Base.Prod using (_,_)
open import Base.Option using (_$¿_)
open import Base.Dec using ()
open import Base.List using (len)
open import Syho.Lang.Expr using (Addr; TyVal)
open import Syho.Lang.Reduce using (Mem; _‼ᴹ_; ✓ᴹ_)
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Exc using (Excᴱᴿᴬ)
open import Syho.Model.ERA.Frac using (Fracᴱᴿᴬ)
import Syho.Model.ERA.All
import Syho.Model.ERA.Prod
import Syho.Model.ERA.Wrap
import Syho.Model.ERA.Up

--------------------------------------------------------------------------------
-- Memᴱᴿᴬ :  Memory ERA

-- For the points-to token

module AllPnts =  Syho.Model.ERA.All (λ (_ : Addr) → Fracᴱᴿᴬ TyVal)
open AllPnts public using () renaming (
  --  Pntsᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  ∀ᴱᴿᴬ to Pntsᴱᴿᴬ)

-- For the freeing token

module AllFree =  Syho.Model.ERA.All (λ (_ : ℕ) → Excᴱᴿᴬ ℕ)
open AllFree public using () renaming (
  --  Freeᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
  ∀ᴱᴿᴬ to Freeᴱᴿᴬ)

-- For both tokens

module ProdMem =  Syho.Model.ERA.Prod Pntsᴱᴿᴬ Freeᴱᴿᴬ
open ProdMem public using () renaming (
  --  ×Memᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  ×ᴱᴿᴬ to ×Memᴱᴿᴬ;
  --  injᴾⁿᵗˢ :  Pntsᴱᴿᴬ .Res → ×Memᴱᴿᴬ .Res
  inj₀ to injᴾⁿᵗˢ;
  --  injᶠʳᵉᵉ :  Freeᴱᴿᴬ .Res → ×Memᴱᴿᴬ .Res
  inj₁ to injᶠʳᵉᵉ)
module WrapMem =  Syho.Model.ERA.Wrap ×Memᴱᴿᴬ Mem
  (λ M →  M ‼ᴹ_ , (len $¿_) ∘ M) ✓ᴹ_
open WrapMem public using () renaming (
  --  WrapMemᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  Wrapᴱᴿᴬ to WrapMemᴱᴿᴬ)
module UpMem =  Syho.Model.ERA.Up WrapMemᴱᴿᴬ {2ᴸ} {2ᴸ} {2ᴸ} {2ᴸ}
open UpMem public using () renaming (
  --  Memᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ
  Upᴱᴿᴬ to Memᴱᴿᴬ)
