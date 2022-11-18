--------------------------------------------------------------------------------
-- Global ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syng.Model.ERA.Glob where

open import Base.Level using (1ᴸ; ↑_; ↓)
open import Base.Few using (⊤; ⊥; absurd)
open import Base.Func using (_$_; _∘_)
open import Base.Eq using (refl; _≡˙_)
open import Base.Dec using (yes; no; ≡Dec; _≟_; ≟-refl; upd˙)
open import Base.Prod using (∑∈-syntax; π₀; _,-)
open import Base.Nat using (ℕ; ṡ_)
open import Syng.Lang.Expr using (Heap; ✓ᴴ_)
open import Syng.Model.ERA.Base using (ERA; ⊤ᴱᴿᴬ)
open import Syng.Model.ERA.Heap using (Heapᴱᴿᴬ; ✓ᴴ⇒✓ᴴᵉᵃᵖ)
open import Syng.Model.ERA.Names using (Namesᴱᴿᴬ; ✓ᴺᵃᵐᵉˢ[⊤]; [⊤]ᴺʳ)
open import Syng.Model.ERA.Ind using (Indˣᴱᴿᴬ; Indᵖᴱᴿᴬ; ∅ᴵⁿᵈˣ; ∅ᴵⁿᵈᵖ; ∅ᴵⁿᵈˣ-✓ε;
  ∅ᴵⁿᵈᵖ-✓ε)
open import Syng.Model.ERA.Inv using (Invᴱᴿᴬ; ∅ᴵⁿᵛ; ∅ᴵⁿᵛ-✓ε)
open import Syng.Model.ERA.Lft using (Lftᴱᴿᴬ; ✓ᴸᶠᵗε)
open import Syng.Model.ERA.Bor using (Borᴱᴿᴬ; ∅ᴮᵒʳ; ∅ᴮᵒʳ-✓ε)
open import Syng.Model.ERA.Ub using (Ubᴱᴿᴬ; ✓ᵁᵇε)

open ERA using (Res; Env)

--------------------------------------------------------------------------------
-- Global ERA

-- Ids of ERAs

pattern iᴴᵉᵃᵖ =  0
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
Globᴱᴿᴬ˙ iᴴᵉᵃᵖ =  Heapᴱᴿᴬ
Globᴱᴿᴬ˙ iᴺᵃᵐᵉˢ =  Namesᴱᴿᴬ
Globᴱᴿᴬ˙ iᴵⁿᵈˣ =  Indˣᴱᴿᴬ
Globᴱᴿᴬ˙ iᴵⁿᵈᵖ =  Indᵖᴱᴿᴬ
Globᴱᴿᴬ˙ iᴵⁿᵛ =  Invᴱᴿᴬ
Globᴱᴿᴬ˙ iᴸᶠᵗ =  Lftᴱᴿᴬ
Globᴱᴿᴬ˙ iᴮᵒʳ =  Borᴱᴿᴬ
Globᴱᴿᴬ˙ iᵁᵇ =  Ubᴱᴿᴬ
Globᴱᴿᴬ˙ elseᴳ =  ⊤ᴱᴿᴬ

-- Globᴱᴿᴬ :  Global ERA, defined as ∀ᴱᴿᴬ Globᴱᴿᴬ˙

import Syng.Model.ERA.All
module AllGlob =  Syng.Model.ERA.All ℕ Globᴱᴿᴬ˙

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

-- Conversion between Envᴳ and a pair of Heap and Envᴵⁿᴳ

envᴳ :  Heap →  Envᴵⁿᴳ →  Envᴳ
envᴳ H _ iᴴᵉᵃᵖ =  ↑ H
envᴳ _ Eᴵⁿ (outᴳ j) =  Eᴵⁿ j

memᴳ :  Envᴳ →  Heap
memᴳ E =  E iᴴᵉᵃᵖ .↓

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
  H H' :  Heap
  j :  ℕ
  X :  Set₁
  Fʲ :  X

abstract

  -- envᴳ H ∅ᴵⁿᴳ with inj˙ iᴵⁿᵛ [⊤]ᴺʳ is valid for valid H

  ∅ᴵⁿᴳ-✓ᴺ :  ✓ᴴ H →  envᴳ H ∅ᴵⁿᴳ ✓ᴳ inj˙ iᴺᵃᵐᵉˢ [⊤]ᴺʳ
  ∅ᴵⁿᴳ-✓ᴺ ✓H iᴴᵉᵃᵖ =  ✓ᴴ⇒✓ᴴᵉᵃᵖ ✓H
  ∅ᴵⁿᴳ-✓ᴺ _ iᴺᵃᵐᵉˢ =  ✓ᴺᵃᵐᵉˢ[⊤]
  ∅ᴵⁿᴳ-✓ᴺ _ iᴵⁿᵈˣ =  ∅ᴵⁿᵈˣ-✓ε
  ∅ᴵⁿᴳ-✓ᴺ _ iᴵⁿᵈᵖ =  ∅ᴵⁿᵈᵖ-✓ε
  ∅ᴵⁿᴳ-✓ᴺ _ iᴵⁿᵛ =  ∅ᴵⁿᵛ-✓ε
  ∅ᴵⁿᴳ-✓ᴺ _ iᴸᶠᵗ =  ✓ᴸᶠᵗε
  ∅ᴵⁿᴳ-✓ᴺ _ iᴮᵒʳ =  ∅ᴮᵒʳ-✓ε
  ∅ᴵⁿᴳ-✓ᴺ _ iᵁᵇ =  ✓ᵁᵇε
  ∅ᴵⁿᴳ-✓ᴺ _ elseᴳ =  _

  -- ≡˙ is congruent w.r.t. envᴳ H

  envᴳ-cong :  Eᴵⁿ ≡˙ Fᴵⁿ →  envᴳ H Eᴵⁿ ≡˙ envᴳ H Fᴵⁿ
  envᴳ-cong _ iᴴᵉᵃᵖ =  refl
  envᴳ-cong E≡F (outᴳ j) =  E≡F j

  -- upd˙ iᴴᵉᵃᵖ on envᴳ is the same as just updating the heap

  upd˙-mem-envᴳ :  upd˙ iᴴᵉᵃᵖ (↑ H') (envᴳ H Eᴵⁿ) ≡˙ envᴳ H' Eᴵⁿ
  upd˙-mem-envᴳ iᴴᵉᵃᵖ =  refl
  upd˙-mem-envᴳ (outᴳ _) =  refl

  -- upd˙ (outᴳ j) on envᴳ is the same as upd˙ j on the inner environment

  upd˙-out-envᴳ :  upd˙ (outᴳ j) Fʲ (envᴳ H Eᴵⁿ)  ≡˙  envᴳ H (upd˙ j Fʲ Eᴵⁿ)
  upd˙-out-envᴳ iᴴᵉᵃᵖ =  refl
  upd˙-out-envᴳ {j} (outᴳ k)  with k ≟ j
  … | yes refl =  refl
  … | no _ = refl
