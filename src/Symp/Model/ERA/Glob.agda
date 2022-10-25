--------------------------------------------------------------------------------
-- Global ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Symp.Model.ERA.Glob where

open import Base.Level using (1ᴸ; ↑_; ↓)
open import Base.Few using (⊤; ⊥; absurd)
open import Base.Func using (_$_; _∘_)
open import Base.Eq using (refl; _≡˙_)
open import Base.Dec using (yes; no; ≡Dec; _≟_; ≟-refl; upd˙)
open import Base.Prod using (∑∈-syntax; π₀; _,-)
open import Base.Nat using (ℕ; ṡ_)
open import Symp.Lang.Expr using (Mem; ✓ᴹ_)
open import Symp.Model.ERA.Base using (ERA; ⊤ᴱᴿᴬ)
open import Symp.Model.ERA.Mem using (Memᴱᴿᴬ; ✓ᴹ⇒✓ᴹᵉᵐ)
open import Symp.Model.ERA.Names using (Namesᴱᴿᴬ; ✓ᴺᵃᵐᵉˢ[⊤]; [⊤]ᴺʳ)
open import Symp.Model.ERA.Ind using (Indˣᴱᴿᴬ; Indᵖᴱᴿᴬ; ∅ᴵⁿᵈˣ; ∅ᴵⁿᵈᵖ; ∅ᴵⁿᵈˣ-✓ε;
  ∅ᴵⁿᵈᵖ-✓ε)
open import Symp.Model.ERA.Inv using (Invᴱᴿᴬ; ∅ᴵⁿᵛ; ∅ᴵⁿᵛ-✓ε)
open import Symp.Model.ERA.Lft using (Lftᴱᴿᴬ; ✓ᴸᶠᵗε)
open import Symp.Model.ERA.Bor using (Borᴱᴿᴬ; ∅ᴮᵒʳ; ∅ᴮᵒʳ-✓ε)
open import Symp.Model.ERA.Ub using (Ubᴱᴿᴬ; ✓ᵁᵇε)

open ERA using (Res; Env)

--------------------------------------------------------------------------------
-- Global ERA

-- Ids of ERAs

pattern iᴹᵉᵐ =  0
pattern iᴺᵃᵐᵉˢ =  1
pattern iᴵⁿᵈˣ =  2
pattern iᴵⁿᵈᵖ =  3
pattern iᴵⁿᵛ =  4
pattern iᴸᶠᵗ =  5
pattern iᴮᵒʳ =  6
pattern iᵁᵇ =  7
pattern elseᴳ =  ṡ ṡ ṡ ṡ ṡ ṡ ṡ ṡ _

-- Map of ERAs

Globᴱᴿᴬ˙ :  ℕ →  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
Globᴱᴿᴬ˙ iᴹᵉᵐ =  Memᴱᴿᴬ
Globᴱᴿᴬ˙ iᴺᵃᵐᵉˢ =  Namesᴱᴿᴬ
Globᴱᴿᴬ˙ iᴵⁿᵈˣ =  Indˣᴱᴿᴬ
Globᴱᴿᴬ˙ iᴵⁿᵈᵖ =  Indᵖᴱᴿᴬ
Globᴱᴿᴬ˙ iᴵⁿᵛ =  Invᴱᴿᴬ
Globᴱᴿᴬ˙ iᴸᶠᵗ =  Lftᴱᴿᴬ
Globᴱᴿᴬ˙ iᴮᵒʳ =  Borᴱᴿᴬ
Globᴱᴿᴬ˙ iᵁᵇ =  Ubᴱᴿᴬ
Globᴱᴿᴬ˙ elseᴳ =  ⊤ᴱᴿᴬ

-- Globᴱᴿᴬ :  Global ERA, defined as ∀ᴱᴿᴬ Globᴱᴿᴬ˙

import Symp.Model.ERA.All
module AllGlob =  Symp.Model.ERA.All ℕ Globᴱᴿᴬ˙

-- Re-export AllGlob
open AllGlob public

-- Aliases
open AllGlob public using () renaming (
  -- Globᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  ∀ᴱᴿᴬ to Globᴱᴿᴬ;
  -- Resᴳ :  Set 1ᴸ
  Res˙ to Resᴳ;
  -- Envᴳ :  Set 1ᴸ
  Env˙ to Envᴳ)

open ERA Globᴱᴿᴬ public using () renaming (ε to εᴳ; _✓_ to _✓ᴳ_)

-- Resource and environment of a component ERA

Resᴳ˙ Envᴳ˙ :  ℕ →  Set 1ᴸ
Resᴳ˙ i =  Globᴱᴿᴬ˙ i .Res
Envᴳ˙ i =  Globᴱᴿᴬ˙ i .Env

--------------------------------------------------------------------------------
-- The inner part of Globᴱᴿᴬ

-- Convert an inner id into an usual id

pattern outᴳ i =  ṡ i

-- Inner ids of inner ERAs

pattern jᴺᵃᵐᵉˢ =  0
pattern jᴵⁿᵈˣ =  1
pattern jᴵⁿᵈᵖ =  2
pattern jᴵⁿᵛ =  3
pattern jᴸᶠᵗ =  4
pattern jᴮᵒʳ =  5
pattern jᵁᵇ =  6
pattern elseᴵⁿᴳ =  ṡ ṡ ṡ ṡ ṡ ṡ ṡ _

-- Resource and environment of a component inner ERA

Resᴵⁿᴳ˙ Envᴵⁿᴳ˙ :  ℕ →  Set 1ᴸ
Resᴵⁿᴳ˙ =  Resᴳ˙ ∘ outᴳ
Envᴵⁿᴳ˙ =  Envᴳ˙ ∘ outᴳ

-- The inner part of the environment

Envᴵⁿᴳ :  Set₁
Envᴵⁿᴳ =  ∀ j →  Envᴵⁿᴳ˙ j

-- Conversion between Envᴳ and a pair of Mem and Envᴵⁿᴳ

envᴳ :  Mem →  Envᴵⁿᴳ →  Envᴳ
envᴳ M _ iᴹᵉᵐ =  ↑ M
envᴳ _ Eᴵⁿ (outᴳ j) =  Eᴵⁿ j

memᴳ :  Envᴳ →  Mem
memᴳ E =  E iᴹᵉᵐ .↓

envᴵⁿᴳ :  Envᴳ →  Envᴵⁿᴳ
envᴵⁿᴳ E j =  E $ outᴳ j

-- Empty inner environment

∅ᴵⁿᴳ :  Envᴵⁿᴳ
∅ᴵⁿᴳ jᴺᵃᵐᵉˢ =  _
∅ᴵⁿᴳ jᴵⁿᵈˣ =  ∅ᴵⁿᵈˣ
∅ᴵⁿᴳ jᴵⁿᵈᵖ =  ∅ᴵⁿᵈᵖ
∅ᴵⁿᴳ jᴵⁿᵛ =  ∅ᴵⁿᵛ
∅ᴵⁿᴳ jᴸᶠᵗ =  _
∅ᴵⁿᴳ jᴮᵒʳ =  ∅ᴮᵒʳ
∅ᴵⁿᴳ jᵁᵇ =  _
∅ᴵⁿᴳ elseᴵⁿᴳ =  _

private variable
  Eᴵⁿ Fᴵⁿ :  Envᴵⁿᴳ
  M M' :  Mem
  j :  ℕ
  X :  Set₁
  Fʲ :  X

abstract

  -- envᴳ M ∅ᴵⁿᴳ with inj˙ iᴵⁿᵛ [⊤]ᴺʳ is valid for valid M

  ∅ᴵⁿᴳ-✓[⊤] :  ✓ᴹ M →  envᴳ M ∅ᴵⁿᴳ ✓ᴳ inj˙ iᴺᵃᵐᵉˢ [⊤]ᴺʳ
  ∅ᴵⁿᴳ-✓[⊤] ✓M iᴹᵉᵐ =  ✓ᴹ⇒✓ᴹᵉᵐ ✓M
  ∅ᴵⁿᴳ-✓[⊤] _ iᴺᵃᵐᵉˢ =  ✓ᴺᵃᵐᵉˢ[⊤]
  ∅ᴵⁿᴳ-✓[⊤] _ iᴵⁿᵈˣ =  ∅ᴵⁿᵈˣ-✓ε
  ∅ᴵⁿᴳ-✓[⊤] _ iᴵⁿᵈᵖ =  ∅ᴵⁿᵈᵖ-✓ε
  ∅ᴵⁿᴳ-✓[⊤] _ iᴵⁿᵛ =  ∅ᴵⁿᵛ-✓ε
  ∅ᴵⁿᴳ-✓[⊤] _ iᴸᶠᵗ =  ✓ᴸᶠᵗε
  ∅ᴵⁿᴳ-✓[⊤] _ iᴮᵒʳ =  ∅ᴮᵒʳ-✓ε
  ∅ᴵⁿᴳ-✓[⊤] _ iᵁᵇ =  ✓ᵁᵇε
  ∅ᴵⁿᴳ-✓[⊤] _ elseᴳ =  _

  -- ≡˙ is congruent w.r.t. envᴳ M

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