--------------------------------------------------------------------------------
-- Constructing Dec
--------------------------------------------------------------------------------

module Base.Dec.Construct where

open import Base.Level using (Level)
open import Base.Dec using (Dec; yes; no)
open import Base.Few using (¬; ¬¬-intro)
open import Base.Prod using (_×_; _,_)
open import Base.Sum using (_⊎_; inj₀; inj₁; ⊎-case)
open import Base.Func using (_$_)

private variable
  ℓA ℓB : Level
  A : Set ℓA
  B : Set ℓB

abstract

  -- ¬
  ¬? : Dec A → Dec (¬ A)
  ¬? (yes a) = no (¬¬-intro a)
  ¬? (no ¬a) = yes ¬a

  -- ×
  infixr 2 _×?_
  _×?_ : Dec A → Dec B → Dec (A × B)
  (yes a) ×? (yes b) = yes (a , b)
  (no ¬a) ×? _ = no (λ (a , _) → ¬a a)
  _ ×? (no ¬b) = no (λ (_ , b) → ¬b b)

  -- ⊎
  infixr 1 _⊎?_
  _⊎?_ : Dec A → Dec B → Dec (A ⊎ B)
  (yes a) ⊎? _ = yes (inj₀ a)
  _ ⊎? (yes b) = yes (inj₁ b)
  (no ¬a) ⊎? (no ¬b) = no $ ⊎-case ¬a ¬b
