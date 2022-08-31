--------------------------------------------------------------------------------
-- Decision
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Dec where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.Func using (_$_)
open import Base.Few using (¬_; ⇒¬¬)
open import Base.Bool using (Bool; tt; ff; Tt)
open import Base.Prod using (_×_; _,_; -,_)
open import Base.Sum using (_⊎_; inj₀; inj₁; ⊎-case)

private variable
  ł ł' ł'' :  Level
  b :  Bool
  A B :  Set ł

--------------------------------------------------------------------------------
-- Decision on a proposition (or a type)

data  Dec (A : Set ł) :  Set ł  where
  yes :  A →  Dec A
  no :  ¬ A →  Dec A

-- Decision on a one-argument predicate

Dec¹ :  ∀{A : Set ł} →  (A → Set ł') →  Set (ł ⊔ᴸ ł')
Dec¹ F =  ∀ a →  Dec (F a)

-- Decision on a two-argument predicate

Dec² :  ∀{A : Set ł} {B : Set ł'} →  (A → B → Set ł'') →  Set (ł ⊔ᴸ ł' ⊔ᴸ ł'')
Dec² F =  ∀ a b →  Dec (F a b)

abstract

  -- Derive Dec from conversion between Tt

  dec-Tt :  (Tt b → A) →  (A → Tt b) →  Dec A
  dec-Tt {tt} ⇒X _ =  yes $ ⇒X _
  dec-Tt {ff} _ X⇒ =  no X⇒

  -- Derive Dec on ¬

  infix 3 ¬?_
  ¬?_ :  Dec A →  Dec (¬ A)
  ¬? yes a =  no $ ⇒¬¬ a
  ¬? no ¬a =  yes ¬a

  -- Derive Dec on ×

  infixr 1 _×?_
  _×?_ :  Dec A →  Dec B →  Dec (A × B)
  yes a ×? yes b =  yes (a , b)
  no ¬a ×? _ =  no λ (a , _) → ¬a a
  _ ×? no ¬b =  no λ (-, b) → ¬b b

  -- Derive Dec on ⊎

  infixr 0 _⊎?_
  _⊎?_ :  Dec A →  Dec B →  Dec (A ⊎ B)
  yes a ⊎? _ =  yes $ inj₀ a
  _ ⊎? yes b =  yes $ inj₁ b
  no ¬a ⊎? no ¬b =  no $ ⊎-case ¬a ¬b
