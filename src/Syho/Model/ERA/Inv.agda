--------------------------------------------------------------------------------
-- Invariant ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Inv where

open import Base.Level using (1ᴸ)
open import Base.Few using (⊤₀; ¬_; absurd)
open import Base.Eq using (_≡_; refl; _≡˙_)
open import Base.Dec using (yes; no; _≟_; ≟-refl; upd˙)
open import Base.Zoi using (Zoi; ⊤ᶻ; ^ᶻ_; _⊎ᶻ_; ✔ᶻ_)
open import Base.Option using (¿_; š_; ň)
open import Base.Prod using (_×_; π₀; π₁; _,_; -,_; _,-)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Base.Nat using (ℕ; ṡ_; _<_; ∀≥˙; ≤-refl; _<≥_; ∀≥˙-upd˙-ṡ)
open import Base.List using ([]; [_])
open import Base.Str using ()
open import Syho.Logic.Prop using (Name; Prop∞)
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Zoi using (Zoiᴱᴿᴬ)
open import Syho.Model.ERA.Exc using (?ˣ; #ˣ_; Excᴱᴿᴬ; ✓ˣ-alloc; ✓ˣ-agree)
open import Syho.Model.ERA.Ag using (Agᴱᴿᴬ; ✓ᴸ-[]; ✓ᴸ-alloc; ✓ᴸ-agree)
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
  ∀ᴱᴿᴬ to Invtkᴱᴿᴬ;
  inj˙ to inj˙ᴵⁿᵛᵗᵏ)

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

open ERA Invtkᴱᴿᴬ public using () renaming (ε to εᴵⁿᵛᵗᵏ; refl˜ to refl˜ᴵⁿᵛᵗᵏ)
open ERA Namesᴱᴿᴬ public using () renaming (ε to εᴺᵃᵐᵉˢ)
open ERA Invᴱᴿᴬ public using () renaming (Env to Envᴵⁿᵛ; Res to Resᴵⁿᵛ;
  _≈_ to _≈ᴵⁿᵛ_; _✓_ to _✓ᴵⁿᵛ_; _∙_ to _∙ᴵⁿᵛ_; ε to εᴵⁿᵛ; _↝_ to _↝ᴵⁿᵛ_)

-- Empty environment of Invᴱᴿᴬ

empᴵⁿᵛ :  Envᴵⁿᵛ
empᴵⁿᵛ =  (λ _ → ň) , 0

-- Persistently observe a proposition at an index

inv :  ℕ →  Prop∞ →  Resᴵⁿᵛ
inv i P =  inj˙ᴵⁿᵛᵗᵏ i ([ P ] , ?ˣ) , εᴺᵃᵐᵉˢ

-- Exclusively own a key of an index

invk :  ℕ →  Prop∞ →  Resᴵⁿᵛ
invk i P =  inj˙ᴵⁿᵛᵗᵏ i ([] , #ˣ P) , εᴺᵃᵐᵉˢ

-- Own a name set

[_]ᴺʳ :  (Name → Zoi) →  Resᴵⁿᵛ
[ Nm ]ᴺʳ =  εᴵⁿᵛᵗᵏ , Nm

private variable
  P :  Prop∞
  Pˇ˙ Qˇ˙ :  ℕ → ¿ Prop∞
  i n :  ℕ
  Nm Nm' :  Name → Zoi

abstract

  -- empᴵⁿᵛ with [ ⊤ᶻ ]ᴺʳ is valid

  empᴵⁿᵛ-✓ :  empᴵⁿᵛ ✓ᴵⁿᵛ [ ⊤ᶻ ]ᴺʳ
  empᴵⁿᵛ-✓ =  (λ _ _ → refl) , (λ _ → ✓ᴸ-[] , _) , _

  -- The set of [ ]ᴺʳ is valid

  []ᴺʳ-✔ :  (Pˇ˙ , n) ✓ᴵⁿᵛ [ Nm ]ᴺʳ →  ✔ᶻ Nm
  []ᴺʳ-✔ (-, -, ✔Nm) =  ✔Nm

  -- Update the set part of [ ]ᴺʳ

  []ᴺʳ-cong :  Nm ≡˙ Nm' →  [ Nm ]ᴺʳ ≈ᴵⁿᵛ [ Nm' ]ᴺʳ
  []ᴺʳ-cong Nm≡Nm' =  (refl˜ᴵⁿᵛᵗᵏ , Nm≡Nm')

  -- invk i P cannot overlap

  invk-no2 :  ¬ (Qˇ˙ , n) ✓ᴵⁿᵛ invk i P ∙ᴵⁿᵛ invk i P
  invk-no2 {i = i} (-, ✓iPP , _)  with ✓iPP i .π₁
  … | ✓↯  rewrite ≟-refl {a = i} =  absurd ✓↯

  -- Allocate inv and invk

  inv-invk-alloc :  ((Qˇ˙ , n) , εᴵⁿᵛ)  ↝ᴵⁿᵛ  λ(_ : ⊤₀) →
                      (upd˙ n (š P) Qˇ˙ , ṡ n) , inv n P ∙ᴵⁿᵛ invk n P
  inv-invk-alloc _ _ .π₀ =  _
  inv-invk-alloc _ (✓Qˇ ,-) .π₁ .π₀ =  ∀≥˙-upd˙-ṡ {F = λ _ → _≡ ň} ✓Qˇ
  inv-invk-alloc _ (-, -, ✓c) .π₁ .π₁ .π₁ =  ✓c
  inv-invk-alloc {n = n} _ (✓Qˇ , Qˇ✓ab , _) .π₁ .π₁ .π₀ i  with i ≟ n | Qˇ✓ab i
  … | no _ | Qˇi✓abi =  Qˇi✓abi
  … | yes refl | (Qˇn✓an , Qˇn✓bn)  rewrite ✓Qˇ _ ≤-refl =
    ✓ᴸ-alloc Qˇn✓an , ✓ˣ-alloc Qˇn✓bn

  -- Get agreement from inv

  inv-agree :  ((Qˇ˙ , n) , inv i P)  ↝ᴵⁿᵛ
                 λ(_ :  Qˇ˙ i ≡ š P  ×  i < n) →  (Qˇ˙ , n) , inv i P
  inv-agree _ ✓Qˇ✓iP∙ .π₁ =  ✓Qˇ✓iP∙
  inv-agree {n = n} {i} _ (✓Qˇ , Qˇ✓iP∙ , _) .π₀  with Qˇ✓iP∙ i .π₀
  … | Qˇi✓P∷  rewrite ≟-refl {a = i}  with ✓ᴸ-agree Qˇi✓P∷
  …   | Qˇi≡šP  with i <≥ n
  …     | ĩ₀ i<n =  Qˇi≡šP , i<n
  …     | ĩ₁ i≥n  rewrite ✓Qˇ _ i≥n  with Qˇi≡šP
  …       | ()

  -- Get agreement from invk

  invk-agree :  ((Qˇ˙ , n) , invk i P)  ↝ᴵⁿᵛ
                  λ(_ :  Qˇ˙ i ≡ š P  ×  i < n) →  (Qˇ˙ , n) , invk i P
  invk-agree _ ✓Qˇ✓iP∙ .π₁ =  ✓Qˇ✓iP∙
  invk-agree {n = n} {i} (a ,-) (✓Qˇ , Qˇ✓iP∙ , _) .π₀  with Qˇ✓iP∙ i .π₁
  … | Qˇi✓#P∙  rewrite ≟-refl {a = i}  with ✓ˣ-agree {x = a i .π₁} Qˇi✓#P∙
  …   | Qˇi≡šP  with i <≥ n
  …     | ĩ₀ i<n =  Qˇi≡šP , i<n
  …     | ĩ₁ i≥n  rewrite ✓Qˇ _ i≥n  with Qˇi≡šP
  …       | ()
