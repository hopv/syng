--------------------------------------------------------------------------------
-- Constructing Dec
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Dec.Construct where

open import Base.Level using (Level)
open import Base.Dec using (Dec; yes; no)
open import Base.Bool using (Bool; tt; ff; Tt)
open import Base.Few using (¬_; ⇒¬¬)
open import Base.Prod using (_×_; _,_; -,_)
open import Base.Sum using (_⊎_; inj₀; inj₁; ⊎-case)
open import Base.Func using (_$_)

private variable
  ℓX ℓY :  Level
  b :  Bool
  X :  Set ℓX
  Y :  Set ℓY

abstract

  -- From conversion between Tt
  dec-Tt :  (Tt b → X) →  (X → Tt b) →  Dec X
  dec-Tt {tt} ⇒X _ =  yes $ ⇒X _
  dec-Tt {ff} _ X⇒ =  no X⇒

  -- ¬
  infix 3 ¬?_
  ¬?_ :  Dec X →  Dec (¬ X)
  ¬? yes x =  no $ ⇒¬¬ x
  ¬? no ¬x =  yes ¬x

  -- ×
  infixr 1 _×?_
  _×?_ :  Dec X →  Dec Y →  Dec (X × Y)
  yes x ×? yes y =  yes $ x , y
  no ¬x ×? _ =  no $ λ (x , _) → ¬x x
  _ ×? no ¬y =  no $ λ (-, y) → ¬y y

  -- ⊎
  infixr 0 _⊎?_
  _⊎?_ :  Dec X →  Dec Y →  Dec (X ⊎ Y)
  yes x ⊎? _ =  yes $ inj₀ x
  _ ⊎? yes y =  yes $ inj₁ y
  no ¬x ⊎? no ¬y =  no $ ⊎-case ¬x ¬y
