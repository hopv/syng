--------------------------------------------------------------------------------
-- Level-polymorphic 2/1/0-element set
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Level using (Level; 0ᴸ)
module Base.Few where

private variable
  ℓ ℓA ℓF :  Level
  A :  Set ℓA

--------------------------------------------------------------------------------
-- ⟨2⟩ :  2-element set / doubleton set

data  ⟨2⟩ {ℓ} :  Set ℓ  where
  0₂ 1₂ :  ⟨2⟩

-- Function from ⟨2⟩

binary :  ∀ {F : ⟨2⟩ {ℓ} → Set ℓF} →  F 0₂ →  F 1₂ →  (x : ⟨2⟩) →  F x
binary a _ 0₂ =  a
binary _ b 1₂ =  b

--------------------------------------------------------------------------------
-- ⊤ :  1-element set / singleton set / truth

record  ⊤ {ℓ} :  Set ℓ  where
  instance constructor 0⊤

--------------------------------------------------------------------------------
-- ⊥ :  0-element set / empty set / falsehood

data  ⊥ {ℓ} :  Set ℓ  where

-- Function from ⊥

absurd :  ∀ {F : ⊥ {ℓ} → Set ℓF} →  (x : ⊥) →  F x
absurd ()

--------------------------------------------------------------------------------
-- ¬ :  Negation

infix 3 ¬_
¬_ :  Set ℓA → Set ℓA
¬ A =  A →  ⊥ {0ᴸ}

-- Introducing ¬¬

⇒¬¬ :  A →  ¬ ¬ A
⇒¬¬ a ¬a =  ¬a a

-- Squashing ¬¬¬ into ¬

¬¬¬⇒¬ :  ¬ ¬ ¬ A →  ¬ A
¬¬¬⇒¬ ¬¬¬a a =  ¬¬¬a (⇒¬¬ a)
