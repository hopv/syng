--------------------------------------------------------------------------------
-- Infinite sequence
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Base.Seq where

open import Base.Level using (Level)
open import Base.Func using (_$_)
open import Base.Size using (Size; ∞; Thunk; !)
open import Base.Inh using (Inh; any)
open import Base.Nat using (ℕ; ṡ_)
open import Base.List using (List⁺; [_]⁺; _∷⁺_)

private variable
  ł :  Level
  ι :  Size
  A :  Set ł

--------------------------------------------------------------------------------
-- Seq :  Infinite sequence

data  Seq (A : Set ł) (ι : Size) :  Set ł

-- Seq under Thunk

Seq˂ :  Set ł →  Size →  Set ł
Seq˂ A ι =  Thunk (Seq A) ι

infixr 5 _∷ˢ_
data  Seq A ι  where
  -- Cons, of A and Seq˂ A ι
  _∷ˢ_ :  A →  Seq˂ A ι →  Seq A ι

-- hdˢ :  Head of Seq

hdˢ :  Seq A ι →  A
hdˢ (a ∷ˢ _) =  a

-- tlˢ :  Tail of Seq

tlˢ :  Seq A ι →  Seq˂ A ι
tlˢ (_ ∷ˢ as) =  as

-- repˢ :  Just repeat an element

repˢ :  A →  Seq A ι
repˢ a =  a ∷ˢ λ{ .! → repˢ a }

instance

  -- Seq A is inhabited if A is inhabited

  Seq-Inh :  {{Inh A}} →  Inh $ Seq A ι
  Seq-Inh .any =  repˢ any

--------------------------------------------------------------------------------
-- ‼ˢ :  Index read

infix 5 _‼ˢ_
_‼ˢ_ :  Seq A ∞ →  ℕ →  A
(a ∷ˢ _) ‼ˢ 0 =  a
(_ ∷ˢ as) ‼ˢ ṡ i =  as .! ‼ˢ i

--------------------------------------------------------------------------------
-- List⁺ and Seq

-- ⁺⧺ˢ :  Append List⁺ to Thunk Seq

infixr 5 _⁺⧺ˢ_
_⁺⧺ˢ_ :  List⁺ A →  Seq˂ A ι →  Seq A ι
[ a ]⁺ ⁺⧺ˢ bs =  a ∷ˢ bs
(a ∷⁺ as) ⁺⧺ˢ bs =  a ∷ˢ λ{ .! → as ⁺⧺ˢ bs }

-- rep⁺ˢ :  Repeat List⁺ to get Seq

rep⁺ˢ :  List⁺ A →  Seq A ι
rep⁺ˢ as =  as ⁺⧺ˢ λ{ .! → rep⁺ˢ as }
