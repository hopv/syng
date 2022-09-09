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
open import Base.Nat using (ℕ; ṡ_; _≥_; _<_; <⇒≤; ≤-refl; <-irrefl; _<≥_)
open import Base.List using ([_])
open import Syho.Logic.Prop using (Prop'; ⊤')
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Exc using (#ˣ_; ✓ˣ-alloc; ✓ˣ-agree; ✓ˣ-free; Excᴱᴿᴬ)
open import Syho.Model.ERA.Ag using (✓ᴸ-resp; ✓ᴸ-rem; ✓ᴸ-alloc; ✓ᴸ-agree; Agᴱᴿᴬ)
import Syho.Model.ERA.All
import Syho.Model.ERA.Wrap

private variable
  P :  Prop' ∞
  Qˇ˙ :  ℕ → ¿ Prop' ∞
  i n :  ℕ

--------------------------------------------------------------------------------
-- Indˣᴱᴿᴬ :  Exclusive indirection ERA

module AllIndˣ =  Syho.Model.ERA.All (λ (_ : ℕ) → Excᴱᴿᴬ (Prop' ∞))
open AllIndˣ public using () renaming (
  --  ∀Indˣᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ
  ∀ᴱᴿᴬ to ∀Indˣᴱᴿᴬ)
module WrapIndˣ =  Syho.Model.ERA.Wrap ∀Indˣᴱᴿᴬ ((ℕ → ¿ Prop' ∞) × ℕ) π₀
  (λ (Pˇ˙ , n) →  ∀{i} →  i ≥ n →  Pˇ˙ i ≡ ň)
open WrapIndˣ public using () renaming (
  --  Indˣᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ
  Wrapᴱᴿᴬ to Indˣᴱᴿᴬ)

open ERA Indˣᴱᴿᴬ public using () renaming (Env to Env-indˣ)

open ERA Indˣᴱᴿᴬ using () renaming (Res to Resˣ; ε to εˣ; _↝_ to _↝ˣ_)

-- Exclusively own a proposition at an index

line-indˣ :  ℕ →  Prop' ∞ →  Resˣ
line-indˣ i P =  upd˙ i (#ˣ P) εˣ

abstract

  -- Add a new proposition and get a line

  alloc-indˣ :  ((Qˇ˙ , n) , εˣ)  ↝ˣ  λ(_ : ⊤₀) →
                  (upd˙ n (š P) Qˇ˙ , ṡ n) , line-indˣ n P
  alloc-indˣ _ _ .π₀ =  _
  alloc-indˣ {n = n} _ (✓Qˇ ,-) .π₁ .π₀ {i}  with i ≡? n
  … | no _ =  ✓Qˇ ∘ <⇒≤
  … | yes refl =  absurd ∘ <-irrefl
  alloc-indˣ {n = n} Rˣ˙ (✓Qˇ , Qˇ✓Rˣ) .π₁ .π₁ i  with i ≡? n | Qˇ✓Rˣ i
  … | no _ | Qˇi✓Rˣi =  Qˇi✓Rˣi
  … | yes refl | Qˇn✓Rˣn  rewrite ✓Qˇ ≤-refl =  ✓ˣ-alloc {x = Rˣ˙ n} Qˇn✓Rˣn

  -- Remove a proposition consuming a line

  use-indˣ :  ((Qˇ˙ , n) , line-indˣ i P)  ↝ˣ
                λ(_ :  Qˇ˙ i ≡ š P  ×  i < n) →  (upd˙ i ň Qˇ˙ , n) , εˣ
  use-indˣ {n = n} {i} Rˣ˙ (✓Qˇ , Qˇ✓Rˣ∙iP) .π₀  with Qˇ✓Rˣ∙iP i
  … | Qˇi✓Rˣi∙#P  rewrite ≡?-refl {a = i}  with ✓ˣ-agree {x = Rˣ˙ i} Qˇi✓Rˣi∙#P
  …   | Qˇi≡šP  with i <≥ n
  …     | ĩ₀ i<n =  Qˇi≡šP , i<n
  …     | ĩ₁ i≥n  rewrite ✓Qˇ i≥n  with Qˇi≡šP
  …       | ()
  use-indˣ {i = i} Rˣ˙ (✓Qˇ ,-) .π₁ .π₀ {j}  with j ≡? i
  … | no _ =  ✓Qˇ
  … | yes refl =  λ _ → refl
  use-indˣ {i = i} Rˣ˙ (-, Qˇ✓Rˣ∙iP) .π₁ .π₁ j  with j ≡? i | Qˇ✓Rˣ∙iP j
  … | no _ | Qˇj✓Rˣj∙? =  Qˇj✓Rˣj∙?
  … | yes refl | Qˇi✓Rˣi∙#P =  ✓ˣ-free {x = Rˣ˙ i} Qˇi✓Rˣi∙#P

--------------------------------------------------------------------------------
-- Ind□ᴱᴿᴬ :  Persistent indirection ERA

module AllInd□ =  Syho.Model.ERA.All (λ (_ : ℕ) → Agᴱᴿᴬ (Prop' ∞))
open AllInd□ public using () renaming (
  --  ∀Ind□ᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ
  ∀ᴱᴿᴬ to ∀Ind□ᴱᴿᴬ)
module WrapInd□ =  Syho.Model.ERA.Wrap ∀Ind□ᴱᴿᴬ ((ℕ → ¿ Prop' ∞) × ℕ) π₀
  (λ (Pˇ˙ , n) →  ∀{i} →  i ≥ n →  Pˇ˙ i ≡ ň)
open WrapInd□ public using () renaming (
  --  Ind□ᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ
  Wrapᴱᴿᴬ to Ind□ᴱᴿᴬ)

open ERA Ind□ᴱᴿᴬ public using () renaming (Env to Env-ind□)

open ERA Ind□ᴱᴿᴬ using () renaming (Res to Res□; ε to ε□; _↝_ to _↝□_)

-- Persistently own a proposition at an index

line-ind□ :  ℕ →  Prop' ∞ →  Res□
line-ind□ i P =  upd˙ i [ P ] ε□

abstract

  -- Add a new proposition and get a line

  alloc-ind□ :  ((Qˇ˙ , n) , ε□)  ↝□  λ(_ : ⊤₀) →
                  (upd˙ n (š P) Qˇ˙ , ṡ n) , line-ind□ n P
  alloc-ind□ _ _ .π₀ =  _
  alloc-ind□ {n = n} _ (✓Qˇ ,-) .π₁ .π₀ {i}  with i ≡? n
  … | no _ =  ✓Qˇ ∘ <⇒≤
  … | yes refl =  absurd ∘ <-irrefl
  alloc-ind□ {n = n} Rs˙ (✓Qˇ , Qˇ✓Rs) .π₁ .π₁ i  with i ≡? n | Qˇ✓Rs i
  … | no _ | Qˇi✓Rsi =  Qˇi✓Rsi
  … | yes refl | Qˇn✓Rsn  rewrite ✓Qˇ ≤-refl =  ✓ᴸ-alloc Qˇn✓Rsn

  -- Get an agreement from a line

  use-ind□ :  ((Qˇ˙ , n) , line-ind□ i P)  ↝□
                λ(_ :  Qˇ˙ i ≡ š P  ×  i < n) →  ((Qˇ˙ , n) , line-ind□ i P)
  use-ind□ {n = n} {i} Rs˙ (✓Qˇ , Qˇ✓Rs⧺iP) .π₀  with Qˇ✓Rs⧺iP i
  … | Qˇi✓Rsi⧺[P]  rewrite ≡?-refl {a = i}  with ✓ᴸ-agree Qˇi✓Rsi⧺[P]
  …   | Qˇi≡šP  with i <≥ n
  …     | ĩ₀ i<n =  Qˇi≡šP , i<n
  …     | ĩ₁ i≥n  rewrite ✓Qˇ i≥n  with Qˇi≡šP
  …       | ()
  use-ind□ _ ✓Qˇ✓Rs⧺iP .π₁ =  ✓Qˇ✓Rs⧺iP

--------------------------------------------------------------------------------
-- On both indirection ERAs

Env-ind :  Set₂
Env-ind =  Env-indˣ × Env-ind□
