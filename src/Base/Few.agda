--------------------------------------------------------------------------------
-- Level-polymorphic 2/1/0-element set
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Base.Level using (Level; 0ᴸ)
module Base.Few where

private variable
  Λ ΛA ΛF :  Level
  A :  Set ΛA

--------------------------------------------------------------------------------
-- ⟨2⟩ :  2-element set / doubleton set

data  ⟨2⟩ {Λ} :  Set Λ  where
  0₂ 1₂ :  ⟨2⟩

-- Function from ⟨2⟩

binary :  ∀ {F : ⟨2⟩ {Λ} → Set ΛF} →  F 0₂ →  F 1₂ →  (x : ⟨2⟩) →  F x
binary a _ 0₂ =  a
binary _ b 1₂ =  b

--------------------------------------------------------------------------------
-- ⊤ :  1-element set / singleton set / truth

record  ⊤ {Λ} :  Set Λ  where
  instance constructor 0⊤

--------------------------------------------------------------------------------
-- ⊥ :  0-element set / empty set / falsehood

data  ⊥ {Λ} :  Set Λ  where

-- Function from ⊥

absurd :  ∀ {F : ⊥ {Λ} → Set ΛF} →  (x : ⊥) →  F x
absurd ()

--------------------------------------------------------------------------------
-- ¬ :  Negation

infix 3 ¬_
¬_ :  Set ΛA → Set ΛA
¬ A =  A →  ⊥ {0ᴸ}

-- Introducing ¬¬

⇒¬¬ :  A →  ¬ ¬ A
⇒¬¬ a ¬a =  ¬a a

-- Squashing ¬¬¬ into ¬

¬¬¬⇒¬ :  ¬ ¬ ¬ A →  ¬ A
¬¬¬⇒¬ ¬¬¬a a =  ¬¬¬a (⇒¬¬ a)
