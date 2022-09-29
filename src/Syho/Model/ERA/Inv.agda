--------------------------------------------------------------------------------
-- Invariant ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Inv where

open import Base.Level using (1ᴸ)
open import Base.Eq using (_≡_; refl)
open import Base.Option using (¿_; ň)
open import Base.Prod using (_×_; _,_; _,-)
open import Base.Sum using ()
open import Base.Nat using (ℕ; ∀≥˙)
open import Base.List using ()
open import Base.Str using ()
open import Syho.Logic.Prop using (Name; Prop∞)
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Zoi using (Zoiᴱᴿᴬ)
open import Syho.Model.ERA.Ag using (Agᴱᴿᴬ; ✓ᴸ-[])
import Syho.Model.ERA.All
import Syho.Model.ERA.Prod
import Syho.Model.ERA.Envm
import Syho.Model.ERA.Envv
import Syho.Model.ERA.Up

--------------------------------------------------------------------------------
-- Invᴱᴿᴬ :  Invariant ERA

-- For the invariant token

module AllInvt =  Syho.Model.ERA.All ℕ (λ _ → Agᴱᴿᴬ Prop∞)
open AllInvt public using () renaming (
  --  Invtᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  ∀ᴱᴿᴬ to Invtᴱᴿᴬ)

-- For the name set token

module AllName =  Syho.Model.ERA.All Name (λ _ → Zoiᴱᴿᴬ)
open AllName public using () renaming (
  --  Nameᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
  ∀ᴱᴿᴬ to Nameᴱᴿᴬ)

-- For the invariant key

module AllInvk =  Syho.Model.ERA.All ℕ (λ _ → Zoiᴱᴿᴬ)
open AllInvk public using () renaming (
  --  Invkᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
  ∀ᴱᴿᴬ to Invkᴱᴿᴬ)

-- For the all

module ProdInv' =  Syho.Model.ERA.Prod Nameᴱᴿᴬ Invkᴱᴿᴬ
open ProdInv' public using () renaming (
  --  ×Inv'ᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
  ×ᴱᴿᴬ to ×Inv'ᴱᴿᴬ)
module ProdInv =  Syho.Model.ERA.Prod Invtᴱᴿᴬ ×Inv'ᴱᴿᴬ
open ProdInv public using () renaming (
  --  ×Invᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  ×ᴱᴿᴬ to ×Invᴱᴿᴬ)
module EnvmInv =  Syho.Model.ERA.Envm ×Invᴱᴿᴬ ((ℕ → ¿ Prop∞) × ℕ)
  (λ (Pˇ˙ ,-) → Pˇ˙ ,-)
open EnvmInv public using () renaming (
  --  EnvmInvᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  Envmᴱᴿᴬ to EnvmInvᴱᴿᴬ)
module EnvvInv =  Syho.Model.ERA.Envv EnvmInvᴱᴿᴬ
  (λ (Pˇ˙ , n) → ∀≥˙ n (λ _ → _≡ ň) Pˇ˙)
open EnvvInv public using () renaming (
  --  Invᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  Envvᴱᴿᴬ to Invᴱᴿᴬ)

open ERA Invᴱᴿᴬ public using () renaming (Env to Envᴵⁿᵛ; Res to Resᴵⁿᵛ;
  _✓_ to _✓ᴵⁿᵛ_; ε to εᴵⁿᵛ; _↝_ to _↝ᴵⁿᵛ_)

-- Empty environment of Invᴱᴿᴬ

empᴵⁿᵛ :  Envᴵⁿᵛ
empᴵⁿᵛ =  (λ _ → ň) , 0

abstract

  -- empᴵⁿᵛ is valid

  empᴵⁿᵛ-✓ :  empᴵⁿᵛ ✓ᴵⁿᵛ εᴵⁿᵛ
  empᴵⁿᵛ-✓ =  (λ _ _ → refl) , (λ _ → ✓ᴸ-[]) , _
