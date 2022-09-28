--------------------------------------------------------------------------------
-- Sum
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Sum where

open import Base.Level using (Level; _⊔ᴸ_)
open import Base.Dec using (Dec; yes; no; ≡Dec; _≟_)

private variable
  ł ł' :  Level
  A B C :  Set ł

--------------------------------------------------------------------------------
-- ⨿ :  Sum

infixr 0 _⨿_
infix 8 ĩ₀_ ĩ₁_
data  _⨿_ (A : Set ł) (B : Set ł') :  Set (ł ⊔ᴸ ł')  where
  -- ĩ₀, ĩ₁ :  Inject from A, B into A ⨿ B
  ĩ₀_ :  A →  A ⨿ B
  ĩ₁_ :  B →  A ⨿ B

-- Case analysis of ⨿

⨿-case :  (A → C) →  (B → C) →  A ⨿ B →  C
⨿-case f _ (ĩ₀ a) =  f a
⨿-case _ g (ĩ₁ b) =  g b

instance

  -- Derive Dec on ⨿

  ⨿-Dec :  {{Dec A}} →  {{Dec B}} →  Dec $ A ⨿ B
  ⨿-Dec {{yes a}} =  yes $ ĩ₀ a
  ⨿-Dec {{_}} {{yes b}} =  yes $ ĩ₁ b
  ⨿-Dec {{no ¬a}} {{no ¬b}} =  no $ ⨿-case ¬a ¬b

  -- Equality decision for ⨿

  ⨿-≡Dec :  {{≡Dec A}} →  {{≡Dec B}} →  ≡Dec $ A ⨿ B
  ⨿-≡Dec ._≟_ (ĩ₀ a) (ĩ₀ a')  with a ≟ a'
  … | yes refl =  yes refl
  … | no a≢a' =  no λ{ refl → a≢a' refl }
  ⨿-≡Dec ._≟_ (ĩ₁ b) (ĩ₁ b')  with b ≟ b'
  … | yes refl =  yes refl
  … | no b≢b' =  no λ{ refl → b≢b' refl }
  ⨿-≡Dec ._≟_ (ĩ₀ _) (ĩ₁ _) =  no λ ()
  ⨿-≡Dec ._≟_ (ĩ₁ _) (ĩ₀ _) =  no λ ()
