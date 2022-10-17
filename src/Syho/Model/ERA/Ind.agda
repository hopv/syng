--------------------------------------------------------------------------------
-- Exclusive & persistent indirection ERAs
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Ind where

open import Base.Func using (_›_; id)
open import Base.Few using (⊤₀)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using (upd˙)
open import Base.Option using (¿_; š_; ň)
open import Base.Prod using (_×_; _,_)
open import Base.Nat using (ℕ; ṡ_; _<_)
open import Base.List using ([_]; ≡⇒≈ᴸ; ≈ᴸ-[])
open import Syho.Logic.Prop using (Prop∞)
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Exc using (Excᴱᴿᴬ; εˣ; #ˣ_; ň-✓ˣ; ✓ˣ-free)
open import Syho.Model.ERA.Ag using (Agᴱᴿᴬ; ň-✓ᴸ; ✓ᴸ-[]; ✓ᴸ-š-[?]; ✓ᴸ-agree)
import Syho.Model.ERA.Bnd

private variable
  P :  Prop∞
  Qˇ˙ :  ℕ → ¿ Prop∞
  i n :  ℕ

--------------------------------------------------------------------------------
-- Indˣᴱᴿᴬ :  Exclusive indirection ERA

module BndIndˣ =  Syho.Model.ERA.Bnd (Excᴱᴿᴬ Prop∞) ň ň-✓ˣ
open BndIndˣ public using () renaming (
  --  Indˣᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  Bndᴱᴿᴬ to Indˣᴱᴿᴬ;
  inj˙ to inj˙ᴵⁿᵈˣ;
  ↝ᴮⁿᵈ-new to ↝ᴵⁿᵈˣ-new; ↝ᴮⁿᵈ-rem to ↝ᴵⁿᵈˣ-rem)

open ERA Indˣᴱᴿᴬ public using () renaming (Env to Envᴵⁿᵈˣ; Res to Resᴵⁿᵈˣ;
  ε to εᴵⁿᵈˣ; _✓_ to _✓ᴵⁿᵈˣ_; _↝_ to _↝ᴵⁿᵈˣ_)

-- Empty environment of Indˣᴱᴿᴬ

∅ᴵⁿᵈˣ :  Envᴵⁿᵈˣ
∅ᴵⁿᵈˣ =  (λ _ → ň) , 0

-- Exclusively own a proposition at an index

indˣ :  ℕ →  Prop∞ →  Resᴵⁿᵈˣ
indˣ i P =  inj˙ᴵⁿᵈˣ i (#ˣ P)

abstract

  -- ∅ᴵⁿᵈˣ with εᴵⁿᵈˣ is valid

  ∅ᴵⁿᵈˣ-✓ε :  ∅ᴵⁿᵈˣ ✓ᴵⁿᵈˣ εᴵⁿᵈˣ
  ∅ᴵⁿᵈˣ-✓ε =  (λ _ _ → refl) , _

  -- Add a new proposition and get indˣ

  indˣ-new :  ((Qˇ˙ , n) , εᴵⁿᵈˣ)  ↝ᴵⁿᵈˣ λ (_ : ⊤₀) →
                (upd˙ n (š P) Qˇ˙ , ṡ n) , indˣ n P
  indˣ-new =  ↝ᴵⁿᵈˣ-new refl

  -- Remove a proposition consuming indˣ

  indˣ-use :  ((Qˇ˙ , n) , indˣ i P)  ↝ᴵⁿᵈˣ
                λ (_ :  i < n  ×  Qˇ˙ i ≡ š P) →  (upd˙ i ň Qˇ˙ , n) , εᴵⁿᵈˣ
  indˣ-use =  ↝ᴵⁿᵈˣ-rem (λ ()) id ✓ˣ-free

--------------------------------------------------------------------------------
-- Indᵖᴱᴿᴬ :  Persistent indirection ERA

module BndIndᵖ =  Syho.Model.ERA.Bnd (Agᴱᴿᴬ Prop∞) ň (ň-✓ᴸ › ≡⇒≈ᴸ)
open BndIndᵖ public using () renaming (
  --  Indᵖᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  Bndᴱᴿᴬ to Indᵖᴱᴿᴬ;
  inj˙ to inj˙ᴵⁿᵈᵖ;
  ↝ᴮⁿᵈ-new to ↝ᴵⁿᵈᵖ-new; ↝ᴮⁿᵈ-agree to ↝ᴵⁿᵈᵖ-agree)

open ERA Indᵖᴱᴿᴬ public using () renaming (Env to Envᴵⁿᵈᵖ; Res to Resᴵⁿᵈᵖ;
  _✓_ to _✓ᴵⁿᵈᵖ_; ε to εᴵⁿᵈᵖ; _↝_ to _↝ᴵⁿᵈᵖ_)

-- Empty environment of Indᵖᴱᴿᴬ

∅ᴵⁿᵈᵖ :  Envᴵⁿᵈᵖ
∅ᴵⁿᵈᵖ =  (λ _ → ň) , 0

-- Persistently own a proposition at an index

indᵖ :  ℕ →  Prop∞ →  Resᴵⁿᵈᵖ
indᵖ i P =  inj˙ᴵⁿᵈᵖ i [ P ]

abstract

  -- ∅ᴵⁿᵈᵖ is valid

  ∅ᴵⁿᵈᵖ-✓ε :  ∅ᴵⁿᵈᵖ ✓ᴵⁿᵈᵖ εᴵⁿᵈᵖ
  ∅ᴵⁿᵈᵖ-✓ε =  (λ _ _ → refl) , λ _ → ✓ᴸ-[]

  -- Add a new proposition and get indᵖ

  indᵖ-new :  ((Qˇ˙ , n) , εᴵⁿᵈᵖ)  ↝ᴵⁿᵈᵖ λ (_ : ⊤₀) →
                (upd˙ n (š P) Qˇ˙ , ṡ n) , indᵖ n P
  indᵖ-new =  ↝ᴵⁿᵈᵖ-new ✓ᴸ-š-[?]

  -- Get an agreement from indᵖ

  indᵖ-use :  ((Qˇ˙ , n) , indᵖ i P)  ↝ᴵⁿᵈᵖ
                λ (_ :  i < n  ×  Qˇ˙ i ≡ š P) →  (Qˇ˙ , n) , indᵖ i P
  indᵖ-use =  ↝ᴵⁿᵈᵖ-agree (≈ᴸ-[] › λ ()) ✓ᴸ-agree

--------------------------------------------------------------------------------
-- On both indirection ERAs

Envᴵⁿᵈ :  Set₁
Envᴵⁿᵈ =  Envᴵⁿᵈˣ × Envᴵⁿᵈᵖ
