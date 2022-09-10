--------------------------------------------------------------------------------
-- Exclusive & persistent indirection ERAs
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Ind where

open import Base.Level using (2ᴸ)
open import Base.Func using (_∘_; id)
open import Base.Few using (⊤₀; absurd)
open import Base.Eq using (_≡_; refl)
open import Base.Size using (∞)
open import Base.Option using (¿_; š_; ň)
open import Base.Prod using (_×_; π₀; π₁; _,_; -,_; _,-)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Base.Dec using (yes; no; upd˙; _≡?_; ≡?-refl)
open import Base.Nat using (ℕ; ṡ_; _≥_; _<_; <⇒≤; ≤-refl; <-irrefl; _<≥_; ∀≥˙;
  ∀≥˙-upd˙-sat; ∀≥˙-upd˙-ṡ)
open import Base.List using ([_])
open import Syho.Logic.Prop using (Prop'; ⊤')
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Exc using (Excᴱᴿᴬ; #ˣ_; ✓ˣ-alloc; ✓ˣ-agree; ✓ˣ-free)
open import Syho.Model.ERA.Ag using (Agᴱᴿᴬ; ✓ᴸ-alloc; ✓ᴸ-agree)
import Syho.Model.ERA.All
import Syho.Model.ERA.Wrap

private variable
  P :  Prop' ∞
  Qˇ˙ :  ℕ → ¿ Prop' ∞
  i n :  ℕ

--------------------------------------------------------------------------------
-- Indˣᴱᴿᴬ :  Exclusive indirection ERA

module AllIndˣ =  Syho.Model.ERA.All ℕ (λ _ → Excᴱᴿᴬ (Prop' ∞))
open AllIndˣ public using () renaming (
  --  ∀Indˣᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ
  ∀ᴱᴿᴬ to ∀Indˣᴱᴿᴬ)
module WrapIndˣ =  Syho.Model.ERA.Wrap ∀Indˣᴱᴿᴬ ((ℕ → ¿ Prop' ∞) × ℕ) π₀
  (λ (Pˇ˙ , n) → ∀≥˙ n (λ _ → _≡ ň) Pˇ˙)
open WrapIndˣ public using () renaming (
  --  Indˣᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ
  Wrapᴱᴿᴬ to Indˣᴱᴿᴬ)

open ERA Indˣᴱᴿᴬ public using () renaming (Env to Envᴵⁿᵈˣ; Res to Resᴵⁿᵈˣ;
  ε to εᴵⁿᵈˣ; _↝_ to _↝ᴵⁿᵈˣ_)

-- Exclusively own a proposition at an index

lineᴵⁿᵈˣ :  ℕ →  Prop' ∞ →  Resᴵⁿᵈˣ
lineᴵⁿᵈˣ i P =  upd˙ i (#ˣ P) εᴵⁿᵈˣ

abstract

  -- Add a new proposition and get a line

  alloc-indˣ :  ((Qˇ˙ , n) , εᴵⁿᵈˣ)  ↝ᴵⁿᵈˣ  λ(_ : ⊤₀) →
                  (upd˙ n (š P) Qˇ˙ , ṡ n) , lineᴵⁿᵈˣ n P
  alloc-indˣ _ _ .π₀ =  _
  alloc-indˣ _ (✓Qˇ ,-) .π₁ .π₀ =  ∀≥˙-upd˙-ṡ {F = λ _ → _≡ ň} ✓Qˇ
  alloc-indˣ {n = n} _ (✓Qˇ , Qˇ✓Rˣ) .π₁ .π₁ i  with i ≡? n | Qˇ✓Rˣ i
  … | no _ | Qˇi✓Rˣi =  Qˇi✓Rˣi
  … | yes refl | Qˇn✓Rˣn  rewrite ✓Qˇ _ ≤-refl =  ✓ˣ-alloc Qˇn✓Rˣn

  -- Remove a proposition consuming a line

  use-indˣ :  ((Qˇ˙ , n) , lineᴵⁿᵈˣ i P)  ↝ᴵⁿᵈˣ
                λ(_ :  Qˇ˙ i ≡ š P  ×  i < n) →  (upd˙ i ň Qˇ˙ , n) , εᴵⁿᵈˣ
  use-indˣ {n = n} {i} Rˣ˙ (✓Qˇ , Qˇ✓iP∙Rˣ) .π₀  with Qˇ✓iP∙Rˣ i
  … | Qˇi✓#P∙Rˣi  rewrite ≡?-refl {a = i}  with ✓ˣ-agree {x = Rˣ˙ i} Qˇi✓#P∙Rˣi
  …   | Qˇi≡šP  with i <≥ n
  …     | ĩ₀ i<n =  Qˇi≡šP , i<n
  …     | ĩ₁ i≥n  rewrite ✓Qˇ _ i≥n  with Qˇi≡šP
  …       | ()
  use-indˣ _ (✓Qˇ ,-) .π₁ .π₀ =  ∀≥˙-upd˙-sat {F = λ _ → _≡ ň} refl ✓Qˇ
  use-indˣ {i = i} _ (-, Qˇ✓iP∙Rˣ) .π₁ .π₁ j  with j ≡? i | Qˇ✓iP∙Rˣ j
  … | no _ | Qˇj✓Rˣj =  Qˇj✓Rˣj
  … | yes refl | Qˇi✓#P∙Rˣi =  ✓ˣ-free Qˇi✓#P∙Rˣi

--------------------------------------------------------------------------------
-- Indᵖᴱᴿᴬ :  Persistent indirection ERA

module AllIndᵖ =  Syho.Model.ERA.All ℕ (λ _ → Agᴱᴿᴬ (Prop' ∞))
open AllIndᵖ public using () renaming (
  --  ∀Indᵖᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ
  ∀ᴱᴿᴬ to ∀Indᵖᴱᴿᴬ)
module WrapIndᵖ =  Syho.Model.ERA.Wrap ∀Indᵖᴱᴿᴬ ((ℕ → ¿ Prop' ∞) × ℕ) π₀
  (λ (Pˇ˙ , n) → ∀≥˙ n (λ _ → _≡ ň) Pˇ˙)
open WrapIndᵖ public using () renaming (
  --  Indᵖᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ
  Wrapᴱᴿᴬ to Indᵖᴱᴿᴬ)

open ERA Indᵖᴱᴿᴬ public using () renaming (Env to Envᴵⁿᵈᵖ; Res to Resᴵⁿᵈᵖ;
  ε to εᴵⁿᵈᵖ; _↝_ to _↝ᴵⁿᵈᵖ_)

-- Persistently own a proposition at an index

lineᴵⁿᵈᵖ :  ℕ →  Prop' ∞ →  Resᴵⁿᵈᵖ
lineᴵⁿᵈᵖ i P =  upd˙ i [ P ] εᴵⁿᵈᵖ

abstract

  -- Add a new proposition and get a line

  alloc-indᵖ :  ((Qˇ˙ , n) , εᴵⁿᵈᵖ)  ↝ᴵⁿᵈᵖ  λ(_ : ⊤₀) →
                  (upd˙ n (š P) Qˇ˙ , ṡ n) , lineᴵⁿᵈᵖ n P
  alloc-indᵖ _ _ .π₀ =  _
  alloc-indᵖ _ (✓Qˇ ,-) .π₁ .π₀ =  ∀≥˙-upd˙-ṡ {F = λ _ → _≡ ň} ✓Qˇ
  alloc-indᵖ {n = n} _ (✓Qˇ , Qˇ✓Rs) .π₁ .π₁ i  with i ≡? n | Qˇ✓Rs i
  … | no _ | Qˇi✓Rsi =  Qˇi✓Rsi
  … | yes refl | Qˇn✓Rsn  rewrite ✓Qˇ _ ≤-refl =  ✓ᴸ-alloc Qˇn✓Rsn

  -- Get an agreement from a line

  use-indᵖ :  ((Qˇ˙ , n) , lineᴵⁿᵈᵖ i P)  ↝ᴵⁿᵈᵖ
                λ(_ :  Qˇ˙ i ≡ š P  ×  i < n) →  ((Qˇ˙ , n) , lineᴵⁿᵈᵖ i P)
  use-indᵖ {n = n} {i} _ (✓Qˇ , Qˇ✓iP⧺Rs) .π₀  with Qˇ✓iP⧺Rs i
  … | Qˇi✓P∷Rsi  rewrite ≡?-refl {a = i}  with ✓ᴸ-agree Qˇi✓P∷Rsi
  …   | Qˇi≡šP  with i <≥ n
  …     | ĩ₀ i<n =  Qˇi≡šP , i<n
  …     | ĩ₁ i≥n  rewrite ✓Qˇ _ i≥n  with Qˇi≡šP
  …       | ()
  use-indᵖ _ ✓Qˇ✓iP⧺Rs .π₁ =  ✓Qˇ✓iP⧺Rs

--------------------------------------------------------------------------------
-- On both indirection ERAs

Envᴵⁿᵈ :  Set₂
Envᴵⁿᵈ =  Envᴵⁿᵈˣ × Envᴵⁿᵈᵖ
