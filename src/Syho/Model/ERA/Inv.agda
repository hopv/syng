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

module ProdInvtk =  Syho.Model.ERA.Prod
  (Agᴱᴿᴬ (Name × Prop∞)) (Excᴱᴿᴬ (Name × Prop∞))
open ProdInvtk public using () renaming (
  --  Invtkᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  ×ᴱᴿᴬ to ×Invtkᴱᴿᴬ)
module AllInvtk =  Syho.Model.ERA.All ℕ (λ _ → ×Invtkᴱᴿᴬ)
open AllInvtk public using () renaming (
  --  Invtkᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  ∀ᴱᴿᴬ to Invtkᴱᴿᴬ;
  inj˙ to inj˙ᴵⁿᵛᵗᵏ; inj˙-⌞⌟ to inj˙ᴵⁿᵛᵗᵏ-⌞⌟)

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
module EnvmInv =  Syho.Model.ERA.Envm ×Invᴱᴿᴬ ((ℕ → ¿ (Name × Prop∞)) × ℕ)
  (λ (E ,-) → (λ i → E i , E i) , _)
open EnvmInv public using () renaming (
  --  EnvmInvᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  Envmᴱᴿᴬ to EnvmInvᴱᴿᴬ)
-- The domain of E consists of indices less than n
module EnvvInv =  Syho.Model.ERA.Envv EnvmInvᴱᴿᴬ
  (λ (E , n) → ∀≥˙ n (λ _ → _≡ ň) E)
open EnvvInv public using () renaming (
  --  Invᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  Envvᴱᴿᴬ to Invᴱᴿᴬ)

open ERA Invtkᴱᴿᴬ public using () renaming (ε to εᴵⁿᵛᵗᵏ; refl˜ to refl˜ᴵⁿᵛᵗᵏ)
open ERA Namesᴱᴿᴬ public using () renaming (ε to εᴺᵃᵐᵉˢ; refl˜ to refl˜ᴺᵃᵐᵉˢ)
open ERA Invᴱᴿᴬ public using () renaming (Env to Envᴵⁿᵛ; Res to Resᴵⁿᵛ;
  _≈_ to _≈ᴵⁿᵛ_; _✓_ to _✓ᴵⁿᵛ_; _∙_ to _∙ᴵⁿᵛ_; ε to εᴵⁿᵛ; ⌞_⌟ to ⌞_⌟ᴵⁿᵛ;
  _↝_ to _↝ᴵⁿᵛ_)

-- Empty environment of Invᴱᴿᴬ

empᴵⁿᵛ :  Envᴵⁿᵛ
empᴵⁿᵛ =  (λ _ → ň) , 0

-- Persistently observe a proposition at an index

inv :  ℕ →  Name →  Prop∞ →  Resᴵⁿᵛ
inv i nm P =  inj˙ᴵⁿᵛᵗᵏ i ([ nm , P ] , ?ˣ) , εᴺᵃᵐᵉˢ

-- Exclusively own a key of an index

invk :  ℕ →  Name →  Prop∞ →  Resᴵⁿᵛ
invk i nm P =  inj˙ᴵⁿᵛᵗᵏ i ([] , #ˣ (nm , P)) , εᴺᵃᵐᵉˢ

-- Own a name set

[_]ᴺʳ :  (Name → Zoi) →  Resᴵⁿᵛ
[ Nm ]ᴺʳ =  εᴵⁿᵛᵗᵏ , Nm

private variable
  P :  Prop∞
  E :  ℕ →  ¿ (Name × Prop∞)
  i n :  ℕ
  nm :  Name
  Nm Nm' :  Name → Zoi

abstract

  -- empᴵⁿᵛ with [ ⊤ᶻ ]ᴺʳ is valid

  empᴵⁿᵛ-✓ :  empᴵⁿᵛ ✓ᴵⁿᵛ [ ⊤ᶻ ]ᴺʳ
  empᴵⁿᵛ-✓ =  (λ _ _ → refl) , (λ _ → ✓ᴸ-[] , _) , _

  -- Update the set part of [ ]ᴺʳ

  []ᴺʳ-cong :  Nm ≡˙ Nm' →  [ Nm ]ᴺʳ ≈ᴵⁿᵛ [ Nm' ]ᴺʳ
  []ᴺʳ-cong Nm≡Nm' =  (refl˜ᴵⁿᵛᵗᵏ , Nm≡Nm')

  -- The set of [ ]ᴺʳ is valid

  []ᴺʳ-✔ :  (E , n) ✓ᴵⁿᵛ [ Nm ]ᴺʳ →  ✔ᶻ Nm
  []ᴺʳ-✔ (-, -, ✔Nm) =  ✔Nm

  -- inv i nm P absorbs ⌞ ⌟

  inv-⌞⌟ :  ⌞ inv i nm P ⌟ᴵⁿᵛ ≈ᴵⁿᵛ inv i nm P
  inv-⌞⌟ =  inj˙ᴵⁿᵛᵗᵏ-⌞⌟ , refl˜ᴺᵃᵐᵉˢ

  -- invk i nm P cannot overlap

  invk-no2 :  ¬ (E , n) ✓ᴵⁿᵛ invk i nm P ∙ᴵⁿᵛ invk i nm P
  invk-no2 {i = i} (-, ✓inmPnmP , _)  with ✓inmPnmP i .π₁
  … | ✓↯  rewrite ≟-refl {a = i} =  absurd ✓↯

  -- Allocate inv and invk

  inv-invk-alloc :  ((E , n) , εᴵⁿᵛ)  ↝ᴵⁿᵛ λ (_ : ⊤₀) →
    (upd˙ n (š (nm , P)) E , ṡ n) , inv n nm P ∙ᴵⁿᵛ invk n nm P
  inv-invk-alloc _ _ .π₀ =  _
  inv-invk-alloc _ (✓E ,-) .π₁ .π₀ =  ∀≥˙-upd˙-ṡ {F = λ _ → _≡ ň} ✓E
  inv-invk-alloc _ (-, -, ✓c) .π₁ .π₁ .π₁ =  ✓c
  inv-invk-alloc {n = n} _ (✓E , E✓ab , _) .π₁ .π₁ .π₀ i  with i ≟ n | E✓ab i
  … | no _ | Ei✓abi =  Ei✓abi
  … | yes refl | (En✓an , En✓bn)  rewrite ✓E _ ≤-refl =
    ✓ᴸ-alloc En✓an , ✓ˣ-alloc En✓bn

  -- Get agreement from inv

  inv-agree :  ((E , n) , inv i nm P)  ↝ᴵⁿᵛ
                 λ (_ :  E i ≡ š (nm , P)  ×  i < n) →  (E , n) , inv i nm P
  inv-agree _ ✓E✓inmP∙ .π₁ =  ✓E✓inmP∙
  inv-agree {n = n} {i} _ (✓E , E✓inmP∙ , _) .π₀  with E✓inmP∙ i .π₀
  … | Ei✓P∷  rewrite ≟-refl {a = i}  with ✓ᴸ-agree Ei✓P∷
  …   | Ei≡šP  with i <≥ n
  …     | ĩ₀ i<n =  Ei≡šP , i<n
  …     | ĩ₁ i≥n  rewrite ✓E _ i≥n  with Ei≡šP
  …       | ()

  -- Get agreement from invk

  invk-agree :  ((E , n) , invk i nm P)  ↝ᴵⁿᵛ
                  λ (_ :  E i ≡ š (nm , P)  ×  i < n) →  (E , n) , invk i nm P
  invk-agree _ ✓E✓inmP∙ .π₁ =  ✓E✓inmP∙
  invk-agree {n = n} {i} (a ,-) (✓E , E✓inmP∙ , _) .π₀  with E✓inmP∙ i .π₁
  … | Ei✓#P∙  rewrite ≟-refl {a = i}  with ✓ˣ-agree {x = a i .π₁} Ei✓#P∙
  …   | Ei≡šP  with i <≥ n
  …     | ĩ₀ i<n =  Ei≡šP , i<n
  …     | ĩ₁ i≥n  rewrite ✓E _ i≥n  with Ei≡šP
  …       | ()
