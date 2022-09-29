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
open import Syho.Model.ERA.Exc using (Excᴱᴿᴬ)
open import Syho.Model.ERA.Ag using (Agᴱᴿᴬ; ✓ᴸ-[])
import Syho.Model.ERA.All
import Syho.Model.ERA.Prod
import Syho.Model.ERA.Envm
import Syho.Model.ERA.Envv
import Syho.Model.ERA.Up

--------------------------------------------------------------------------------
-- Invᴱᴿᴬ :  Invariant ERA

-- For the invariant token and key

module ProdInvtk =  Syho.Model.ERA.Prod (Agᴱᴿᴬ Prop∞) (Excᴱᴿᴬ Prop∞)
open ProdInvtk public using () renaming (
  --  Invtkᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  ×ᴱᴿᴬ to ×Invtkᴱᴿᴬ)
module AllInvtk =  Syho.Model.ERA.All ℕ (λ _ → ×Invtkᴱᴿᴬ)
open AllInvtk public using () renaming (
  --  Invtkᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  ∀ᴱᴿᴬ to Invtkᴱᴿᴬ)

-- For the name set token

module AllNames =  Syho.Model.ERA.All Name (λ _ → Zoiᴱᴿᴬ)
open AllNames public using () renaming (
  --  Namesᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
  ∀ᴱᴿᴬ to Namesᴱᴿᴬ)

-- For the all

module ProdInv =  Syho.Model.ERA.Prod Invtkᴱᴿᴬ Namesᴱᴿᴬ
open ProdInv public using () renaming (
  --  ×Invᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  ×ᴱᴿᴬ to ×Invᴱᴿᴬ)
module EnvmInv =  Syho.Model.ERA.Envm ×Invᴱᴿᴬ ((ℕ → ¿ Prop∞) × ℕ)
  (λ (Pˇ˙ ,-) → (λ i → Pˇ˙ i , Pˇ˙ i) , _)
open EnvmInv public using () renaming (
  --  EnvmInvᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  Envmᴱᴿᴬ to EnvmInvᴱᴿᴬ)
-- The domain of Pˇ˙ consists of indices less than n
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
  empᴵⁿᵛ-✓ =  (λ _ _ → refl) , (λ _ → ✓ᴸ-[] , _) , _
