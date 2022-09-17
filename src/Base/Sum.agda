--------------------------------------------------------------------------------
-- Sum
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Sum where

open import Base.Level using (Level; _⊔ᴸ_)

private variable
  ł ł' :  Level
  A B C :  Set ł

--------------------------------------------------------------------------------
-- ⊎ :  Sum

infixr 0 _⊎_
infix 8 ĩ₀_ ĩ₁_
data  _⊎_ (A : Set ł) (B : Set ł') :  Set (ł ⊔ᴸ ł')  where
  -- ĩ₀, ĩ₁ :  Inject from A, B into A ⊎ B
  ĩ₀_ :  A →  A ⊎ B
  ĩ₁_ :  B →  A ⊎ B

-- Case analysis of ⊎

⊎-case :  (A → C) →  (B → C) →  A ⊎ B →  C
⊎-case f _ (ĩ₀ a) =  f a
⊎-case _ g (ĩ₁ b) =  g b
