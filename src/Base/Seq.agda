--------------------------------------------------------------------------------
-- Infinite sequence
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Base.Seq where

open import Base.Level using (Level)
open import Base.Func using (_$_)
open import Base.Dec using (Dec; yes; no)
open import Base.Size using (𝕊; ∞; Thunk; !)
open import Base.Nat using (ℕ; ṡ_)
open import Base.List using (List; []; _∷_; List⁺; [_]⁺; _∷⁺_)

private variable
  ł :  Level
  ι :  𝕊
  A :  Set ł

--------------------------------------------------------------------------------
-- Seq :  Infinite sequence

data  Seq (ι : 𝕊) (A : Set ł) :  Set ł

-- Seq under Thunk

Seq˂ :  𝕊 →  Set ł →  Set ł
Seq˂ ι A =  Thunk (λ ι' → Seq ι' A) ι

infixr 5 _∷ˢ_
data  Seq ι A  where
  -- Cons, of A and Seq˂ ι A
  _∷ˢ_ :  A →  Seq˂ ι A →  Seq ι A

-- Utility
Seq∞ Seq˂∞ :  Set ł →  Set ł
Seq∞ =  Seq ∞
Seq˂∞ =  Seq˂ ∞

-- hdˢ :  Head of Seq

hdˢ :  Seq ι A →  A
hdˢ (a ∷ˢ _) =  a

-- tlˢ :  Tail of Seq

tlˢ :  Seq ι A →  Seq˂ ι A
tlˢ (_ ∷ˢ as˂) =  as˂

-- repˢ :  Just repeat an element

repˢ :  A →  Seq ι A
repˢ a =  a ∷ˢ λ{ .! → repˢ a }

-- rep²ˢ :  Just repeat two elements

rep²ˢ :  A →  A →  Seq ι A
rep²ˢ a b =  a ∷ˢ λ{ .! → rep²ˢ b a }

instance

  -- Decide Seq A

  Seq-Dec :  {{Dec A}} →  Dec $ Seq ι A
  Seq-Dec {{yes a}} =  yes $ repˢ a
  Seq-Dec {{no ¬a}} =  no λ{ as → ¬a $ hdˢ as }

--------------------------------------------------------------------------------
-- ‼ˢ :  Index read

infix 5 _‼ˢ_
_‼ˢ_ :  Seq∞ A →  ℕ →  A
(a ∷ˢ _) ‼ˢ 0 =  a
(_ ∷ˢ as˂) ‼ˢ ṡ i =  as˂ .! ‼ˢ i

--------------------------------------------------------------------------------
-- take :  Take a list from a sequence

takeˢ :  ℕ →  Seq∞ A →  List A
takeˢ 0 _ =  []
takeˢ (ṡ n) (a ∷ˢ as˂) =  a ∷ takeˢ n (as˂ .!)

--------------------------------------------------------------------------------
-- List⁺ and Seq

-- ⁺⧺ˢ :  Append List⁺ to Seq˂

infixr 5 _⁺⧺ˢ_
_⁺⧺ˢ_ :  List⁺ A →  Seq˂ ι A →  Seq ι A
[ a ]⁺ ⁺⧺ˢ bs˂ =  a ∷ˢ bs˂
(a ∷⁺ as) ⁺⧺ˢ bs˂ =  a ∷ˢ λ{ .! → as ⁺⧺ˢ bs˂ }

-- rep⁺ˢ :  Repeat List⁺ to get Seq

rep⁺ˢ :  List⁺ A →  Seq ι A
rep⁺ˢ as =  as ⁺⧺ˢ λ{ .! → rep⁺ˢ as }
