--------------------------------------------------------------------------------
-- Global ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Glob where

open import Base.Level using (2ᴸ; ↑_; ↓)
open import Base.Few using (⊤; ⊥; absurd)
open import Base.Func using (_$_)
open import Base.Eq using (refl; _≡˙_)
open import Base.Prod using (∑∈-syntax; π₀; _,-)
open import Base.Dec using (yes; no; ≡Dec; _≟_; ≟-refl; upd˙)
open import Base.Nat using (ℕ; ṡ_)
open import Syho.Lang.Reduce using (Mem; ✓ᴹ_)
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Top using (⊤ᴱᴿᴬ)
open import Syho.Model.ERA.Mem using (Memᴱᴿᴬ; ✓ᴹ⇒✓ᴹᵉᵐ)
open import Syho.Model.ERA.Ind using (Indˣᴱᴿᴬ; Indᵖᴱᴿᴬ; empᴵⁿᵈˣ; empᴵⁿᵈᵖ;
  empᴵⁿᵈˣ-✓; empᴵⁿᵈᵖ-✓)

open ERA using (Env)

--------------------------------------------------------------------------------
-- Global ERA

-- Ids of ERAs

pattern iᴹᵉᵐ =  0
pattern iᴵⁿᵈˣ =  1
pattern iᴵⁿᵈᵖ =  2
pattern elseᴳ =  ṡ ṡ ṡ _

-- Map of ERAs

Globᴱᴿᴬ˙ :  ℕ →  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ
Globᴱᴿᴬ˙ iᴹᵉᵐ =  Memᴱᴿᴬ
Globᴱᴿᴬ˙ iᴵⁿᵈˣ =  Indˣᴱᴿᴬ
Globᴱᴿᴬ˙ iᴵⁿᵈᵖ =  Indᵖᴱᴿᴬ
Globᴱᴿᴬ˙ elseᴳ =  ⊤ᴱᴿᴬ

-- Globᴱᴿᴬ :  Global ERA, defined as ∀ᴱᴿᴬ Globᴱᴿᴬ˙

import Syho.Model.ERA.All
module AllGlob =  Syho.Model.ERA.All ℕ Globᴱᴿᴬ˙

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

open ERA Globᴱᴿᴬ public using () renaming (ε to εᴳ; _✓_ to _✓ᴳ_)

--------------------------------------------------------------------------------
-- The inner part of Globᴱᴿᴬ

-- Convert an inner id into an usual id

pattern outᴳ i =  ṡ i

-- Inner ids of inner ERAs

pattern jᴵⁿᵈˣ =  0
pattern jᴵⁿᵈᵖ =  1
pattern elseᴵⁿᴳ =  ṡ ṡ _

-- The inner part of the environment

Envᴵⁿᴳ :  Set₂
Envᴵⁿᴳ =  ∀(j : ℕ) →  Globᴱᴿᴬ˙ (outᴳ j) .Env

-- Conversion between Envᴳ and a pair of Mem and Envᴵⁿᴳ

envᴳ :  Mem →  Envᴵⁿᴳ →  Envᴳ
envᴳ M _ iᴹᵉᵐ =  ↑ M
envᴳ _ Eᴵⁿ (outᴳ j) =  Eᴵⁿ j

memᴳ :  Envᴳ →  Mem
memᴳ E =  E iᴹᵉᵐ .↓

envᴵⁿᴳ :  Envᴳ →  Envᴵⁿᴳ
envᴵⁿᴳ E j =  E $ outᴳ j

-- Empty inner environment

empᴵⁿᴳ :  Envᴵⁿᴳ
empᴵⁿᴳ jᴵⁿᵈˣ =  empᴵⁿᵈˣ
empᴵⁿᴳ jᴵⁿᵈᵖ =  empᴵⁿᵈᵖ
empᴵⁿᴳ elseᴵⁿᴳ =  _

private variable
  Eᴵⁿ Fᴵⁿ :  Envᴵⁿᴳ
  M M' :  Mem
  j :  ℕ
  X :  Set₂
  Fʲ :  X

abstract

  -- envᴳ M empᴵⁿᴳ is valid for valid M

  empᴵⁿᴳ-✓ :  ✓ᴹ M →  envᴳ M empᴵⁿᴳ ✓ᴳ εᴳ
  empᴵⁿᴳ-✓ ✓M iᴹᵉᵐ =  ✓ᴹ⇒✓ᴹᵉᵐ ✓M
  empᴵⁿᴳ-✓ _ iᴵⁿᵈˣ =  empᴵⁿᵈˣ-✓
  empᴵⁿᴳ-✓ _ iᴵⁿᵈᵖ =  empᴵⁿᵈᵖ-✓
  empᴵⁿᴳ-✓ _ elseᴳ =  _

  -- ≡˙ is congruent with respect to envᴳ M

  envᴳ-cong :  Eᴵⁿ ≡˙ Fᴵⁿ →  envᴳ M Eᴵⁿ ≡˙ envᴳ M Fᴵⁿ
  envᴳ-cong _ iᴹᵉᵐ =  refl
  envᴳ-cong E≡F (outᴳ j) =  E≡F j

  -- upd˙ iᴹᵉᵐ on envᴳ is the same as just updating the memory

  upd˙-mem-envᴳ :  upd˙ iᴹᵉᵐ (↑ M') (envᴳ M Eᴵⁿ) ≡˙ envᴳ M' Eᴵⁿ
  upd˙-mem-envᴳ iᴹᵉᵐ =  refl
  upd˙-mem-envᴳ (outᴳ _) =  refl

  -- upd˙ (outᴳ j) on envᴳ is the same as upd˙ j on the inner environment

  upd˙-out-envᴳ :  upd˙ (outᴳ j) Fʲ (envᴳ M Eᴵⁿ)  ≡˙  envᴳ M (upd˙ j Fʲ Eᴵⁿ)
  upd˙-out-envᴳ iᴹᵉᵐ =  refl
  upd˙-out-envᴳ {j} (outᴳ k)  with k ≟ j
  … | yes refl =  refl
  … | no _ = refl
