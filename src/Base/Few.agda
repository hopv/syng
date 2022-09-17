--------------------------------------------------------------------------------
-- Level-polymorphic 2/1/0-element set
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Few where

open import Base.Level using (Level; 0ᴸ)

private variable
  ł ł' :  Level
  A :  Set ł

--------------------------------------------------------------------------------
-- ⟨2⟩ :  2-element set / doubleton set

data  ⟨2⟩ {ł} :  Set ł  where
  0₂ 1₂ :  ⟨2⟩

-- Function from ⟨2⟩

binary :  ∀{F : ⟨2⟩ {ł} → Set ł'} →  F 0₂ →  F 1₂ →  (x : ⟨2⟩) →  F x
binary a _ 0₂ =  a
binary _ b 1₂ =  b

--------------------------------------------------------------------------------
-- ⊤ :  1-element set / singleton set / truth

record  ⊤ {ł} :  Set ł  where
  instance constructor 0⊤

-- ⊤ of level 0

⊤₀ :  Set₀
⊤₀ =  ⊤

--------------------------------------------------------------------------------
-- ⊥ :  0-element set / empty set / falsehood

data  ⊥ {ł} :  Set ł  where

-- ⊥ of level 0

⊥₀ :  Set₀
⊥₀ =  ⊥

-- Function from ⊥

absurd :  ∀{F : ⊥ {ł} → Set ł'} →  (x : ⊥) →  F x
absurd ()

--------------------------------------------------------------------------------
-- ¬ :  Negation

infix 3 ¬_
¬_ :  Set ł → Set ł
¬ A =  A →  ⊥₀

-- Introduce ¬¬

⇒¬¬ :  A →  ¬ ¬ A
⇒¬¬ a ¬a =  ¬a a

-- Squash ¬¬¬ into ¬

¬¬¬⇒¬ :  ¬ ¬ ¬ A →  ¬ A
¬¬¬⇒¬ ¬¬¬a a =  ¬¬¬a (⇒¬¬ a)
