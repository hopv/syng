--------------------------------------------------------------------------------
-- Upper bound ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Symp.Model.ERA.Ub where

open import Base.Level using (0ᴸ; 1ᴸ; ↑_; ↓)
open import Base.Func using (_$_; id)
open import Base.Few using (⊤; ⊤₀; ⊥)
open import Base.Eq using (_≡_; refl; ◠_; _◇_)
open import Base.Dec using (≟-refl)
open import Base.Option using (¿_; ň; š_)
open import Base.Prod using (_×_; π₀; π₁; _,_; -,_; _,-)
open import Base.Nat using (ℕ; _≤_; _⊓_; _⊓∞_; ≤-refl; ≤-trans; ≤⊓-elimʳ; ⊓-≤;
  ⊓∞-comm; ⊓∞-assocʳ; ⊓∞-idem)
open import Symp.Model.ERA.Base using (ERA; Upᴱᴿᴬ)
open import Symp.Model.ERA.Exc using (Exc; εˣ; #ˣ_; ↯ˣ; _∙ˣ_; ∙ˣ-comm;
  ∙ˣ-assocʳ)
import Symp.Model.ERA.Fin

open ERA using (Res; _≈_; _∙_; ε; ⌞_⌟; Env; _✓_; refl˜; ◠˜_; _◇˜_; ∙-congˡ;
  ∙-unitˡ; ∙-comm; ∙-assocʳ; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem; ✓-resp; ✓-rem)

--------------------------------------------------------------------------------
-- Ubb :  Upper bound box

Ubb :  Set₀
Ubb =  Exc ℕ × ¿ ℕ

private variable
  u u' :  Ubb
  o m n :  ℕ

-- ∙ᵁᵇᵇ :  Product of Ubb

infixr 7 _∙ᵁᵇᵇ_
_∙ᵁᵇᵇ_ :  Ubb →  Ubb →  Ubb
(x , m) ∙ᵁᵇᵇ (y , n) =  x ∙ˣ y , m ⊓∞ n

-- ✓ᵁᵇᵇ :  Validity of Ubb

infix 4 ✓ᵁᵇᵇ_
✓ᵁᵇᵇ_ :  Ubb →  Set₀
✓ᵁᵇᵇ (εˣ ,-) =  ⊤
✓ᵁᵇᵇ (#ˣ _ , ň) =  ⊤
✓ᵁᵇᵇ (#ˣ m , š n) =  m ≤ n
✓ᵁᵇᵇ (↯ˣ ,-) =  ⊥

abstract

  -- ≡ (εˣ , ň) is preserved by removal w.r.t. ∙ᵁᵇᵇ

  ≡εᵁᵇᵇ-rem :  u ∙ᵁᵇᵇ u' ≡ (εˣ , ň) →  u' ≡ (εˣ , ň)
  ≡εᵁᵇᵇ-rem {_} {εˣ , ň} _ =  refl
  ≡εᵁᵇᵇ-rem {εˣ ,- } {#ˣ m ,- } ()
  ≡εᵁᵇᵇ-rem {εˣ ,- } {↯ˣ ,- } ()
  ≡εᵁᵇᵇ-rem { -, ň} { -, š _} ()

  -- ✓ᵁᵇᵇ is preserved by removal w.r.t. ∙ᵁᵇᵇ

  ✓ᵁᵇᵇ-rem :  ✓ᵁᵇᵇ u ∙ᵁᵇᵇ u' →  ✓ᵁᵇᵇ u'
  ✓ᵁᵇᵇ-rem {_} {εˣ ,- } _ =  _
  ✓ᵁᵇᵇ-rem {_} {#ˣ _ , ň} _ =  _
  ✓ᵁᵇᵇ-rem {εˣ , ň} {#ˣ _ , š _} m≤n =  m≤n
  ✓ᵁᵇᵇ-rem {εˣ , š k} {#ˣ m , š n} m≤k⊓n =  ≤⊓-elimʳ m≤k⊓n
  ✓ᵁᵇᵇ-rem {εˣ ,- } {↯ˣ ,- } ()

--------------------------------------------------------------------------------
-- Ubbᴱᴿᴬ :  Upper bound box ERA

Ubbᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
Ubbᴱᴿᴬ .Res =  Exc ℕ × ¿ ℕ
Ubbᴱᴿᴬ ._≈_ =  _≡_
Ubbᴱᴿᴬ ._∙_ =  _∙ᵁᵇᵇ_
Ubbᴱᴿᴬ .ε =  εˣ , ň
Ubbᴱᴿᴬ .⌞_⌟ (x , n∞) =  εˣ , n∞
Ubbᴱᴿᴬ .Env =  ⊤
Ubbᴱᴿᴬ ._✓_ _ =  ✓ᵁᵇᵇ_
Ubbᴱᴿᴬ .refl˜ =  refl
Ubbᴱᴿᴬ .◠˜_ =  ◠_
Ubbᴱᴿᴬ ._◇˜_ =  _◇_
Ubbᴱᴿᴬ .∙-congˡ refl =  refl
Ubbᴱᴿᴬ .∙-unitˡ =  refl
Ubbᴱᴿᴬ .∙-comm {x , m∞} {y , n∞}
  rewrite ∙ˣ-comm {x = x} {y} | ⊓∞-comm {m∞} {n∞} =  refl
Ubbᴱᴿᴬ .∙-assocʳ {x , l∞} {y , m∞} {z , n∞}
  rewrite ∙ˣ-assocʳ {x = x} {y} {z} | ⊓∞-assocʳ {l∞} {m∞} {n∞} =  refl
Ubbᴱᴿᴬ .⌞⌟-cong refl =  refl
Ubbᴱᴿᴬ .⌞⌟-add { -, n∞} =  (εˣ , n∞) , refl
Ubbᴱᴿᴬ .⌞⌟-unitˡ { -, n∞}  rewrite ⊓∞-idem {n∞} =  refl
Ubbᴱᴿᴬ .⌞⌟-idem =  refl
Ubbᴱᴿᴬ .✓-resp refl =  id
Ubbᴱᴿᴬ .✓-rem {a = u} =  ✓ᵁᵇᵇ-rem {u}

open ERA Ubbᴱᴿᴬ using () renaming (_↝_ to _↝ᵁᵇᵇ_)

abstract

  -- Lower the number of #ˣ

  #ᵁᵇᵇʳ-upd :  m ≤ n  →   (-, #ˣ n , ň)  ↝ᵁᵇᵇ λ (_ : ⊤₀) →  -, (#ˣ m , š m)
  #ᵁᵇᵇʳ-upd _ _ _ .π₀ =  _
  #ᵁᵇᵇʳ-upd _ (εˣ , ň) _ .π₁ =  ≤-refl
  #ᵁᵇᵇʳ-upd m≤n (εˣ , š l) n≤l .π₁  rewrite ⊓-≤ (≤-trans m≤n n≤l) =  ≤-refl

--------------------------------------------------------------------------------
-- Ubᴱᴿᴬ :  Upper bound ERA

module FinUb =  Symp.Model.ERA.Fin Ubbᴱᴿᴬ (λ{u} → ≡εᵁᵇᵇ-rem {u})
open FinUb public using () renaming (
  --  Ub'ᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
  Finᴱᴿᴬ to Ub'ᴱᴿᴬ;
  --  inj˙ᵁᵇ :  Ub →  Ubb →  Ub →  Ubb
  inj˙ to inj˙ᵁᵇ;
  inj˙-≈ to inj˙ᵁᵇ-≈; inj˙-∙ to inj˙ᵁᵇ-∙; inj˙-⌞⌟ to inj˙ᵁᵇ-⌞⌟;
  ↝ᶠⁱⁿ-new to ↝ᵁᵇ-new; inj˙-↝ᶠⁱⁿ to inj˙-↝ᵁᵇ)

Ubᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
Ubᴱᴿᴬ =  Upᴱᴿᴬ Ub'ᴱᴿᴬ

open ERA Ub'ᴱᴿᴬ public using () renaming (ε to εᵁᵇ'; ◠˜_ to ◠˜ᵁᵇ'_;
  ↝-respʳ to ↝ᵁᵇ'-respʳ)
open ERA Ubᴱᴿᴬ public using () renaming (Res to Resᵁᵇ; _≈_ to _≈ᵁᵇ_;
  _∙_ to _∙ᵁᵇ_; ε to εᵁᵇ; ⌞_⌟ to ⌞_⌟ᵁᵇ; _✓_ to _✓ᵁᵇ_; _↝_ to _↝ᵁᵇ_;
  ◠˜_ to ◠˜ᵁᵇ_)

-- #ᵁᵇ⟨ ⟩ʳ :  Resource for the upper boundee token

infix 8 #ᵁᵇ⟨_⟩ʳ_
#ᵁᵇ⟨_⟩ʳ_ :  ℕ →  ℕ →  Resᵁᵇ
(#ᵁᵇ⟨ o ⟩ʳ n) .↓ =  inj˙ᵁᵇ o (#ˣ n , ň)

-- ≤ᵁᵇ⟨ ⟩ʳ :  Resource for the upper bound token

infix 8 ≤ᵁᵇ⟨_⟩ʳ_
≤ᵁᵇ⟨_⟩ʳ_ :  ℕ →  ℕ →  Resᵁᵇ
(≤ᵁᵇ⟨ o ⟩ʳ n) .↓ =  inj˙ᵁᵇ o (εˣ , š n)

abstract

  -- εᵁᵇ is valid

  ✓ᵁᵇε :  _ ✓ᵁᵇ εᵁᵇ
  ✓ᵁᵇε .↓ =  (0 , λ _ _ → refl) ,-

  -- Merge ≤ᵁᵇʳ w.r.t. ⊓

  ≤ᵁᵇʳ-∙ :  ≤ᵁᵇ⟨ o ⟩ʳ m ∙ᵁᵇ ≤ᵁᵇ⟨ o ⟩ʳ n  ≈ᵁᵇ  ≤ᵁᵇ⟨ o ⟩ʳ (m ⊓ n)
  ≤ᵁᵇʳ-∙ .↓ =  inj˙ᵁᵇ-∙

  -- ≤ᵁᵇʳ absorbs ⌞⌟ᵁᵇ

  ≤ᵁᵇʳ-⌞⌟ :  ⌞ ≤ᵁᵇ⟨ o ⟩ʳ m ⌟ᵁᵇ  ≈ᵁᵇ  ≤ᵁᵇ⟨ o ⟩ʳ m
  ≤ᵁᵇʳ-⌞⌟ .↓ =  inj˙ᵁᵇ-⌞⌟

  -- Upper-bound #ᵁᵇʳ with ≤ᵁᵇʳ

  ≤ᵁᵇʳ-#ᵁᵇʳ :  _ ✓ᵁᵇ ≤ᵁᵇ⟨ o ⟩ʳ m ∙ᵁᵇ #ᵁᵇ⟨ o ⟩ʳ n  →   n ≤ m
  ≤ᵁᵇʳ-#ᵁᵇʳ {o = o} (↑ (-, ✓≤m∙#n))  with ✓≤m∙#n o
  … | ✓≤m∙#ni  rewrite ≟-refl {a = o} =  ✓≤m∙#ni

  -- Create #ᵁᵇʳ and ≤ᵁᵇʳ at a fresh index

  #ᵁᵇʳ-new :  (-, εᵁᵇ)  ↝ᵁᵇ λ o →  -, ≤ᵁᵇ⟨ o ⟩ʳ n ∙ᵁᵇ #ᵁᵇ⟨ o ⟩ʳ n
  #ᵁᵇʳ-new {n = n} (↑ u˙) (↑ ✓u)
    with ↝ᵁᵇ'-respʳ {a = εᵁᵇ'} (◠˜ᵁᵇ' inj˙ᵁᵇ-∙) (↝ᵁᵇ-new $ ≤-refl {n}) u˙ ✓u
  … | o , ✓≤n∙#n∙u =  o , ↑ ✓≤n∙#n∙u

  -- Lower the number of #ᵁᵇʳ to get new ≤ᵁᵇʳ

  #ᵁᵇʳ-upd :  m ≤ n  →
    (-, #ᵁᵇ⟨ o ⟩ʳ n)  ↝ᵁᵇ λ (_ : ⊤₀) →  -, ≤ᵁᵇ⟨ o ⟩ʳ m ∙ᵁᵇ #ᵁᵇ⟨ o ⟩ʳ m
  #ᵁᵇʳ-upd m≤n (↑ u˙) (↑ ✓#n∙u)  with ↝ᵁᵇ'-respʳ {a = inj˙ᵁᵇ _ _}
    (◠˜ᵁᵇ' inj˙ᵁᵇ-∙) (inj˙-↝ᵁᵇ (λ ()) (#ᵁᵇᵇʳ-upd m≤n)) u˙ ✓#n∙u
  … | -, ✓≤m∙#m∙u =  -, ↑ ✓≤m∙#m∙u
