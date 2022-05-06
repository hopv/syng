--------------------------------------------------------------------------------
-- Proof-mode-like rules in Shog
--------------------------------------------------------------------------------

-- The rules work for a proposition P ∗ Q ∗ R ∗ ...
-- (Recall that ∗ is right-associative)

{-# OPTIONS --sized-types #-}

open import Base.Level using (Level)
module Shog.Logic.ProofMode (ℓ : Level) where

open import Base.Size using (Size; ∞)
open import Base.Func using (_$_; _∘_)

open import Base.NElem using (2-ary)
open import Shog.Logic.Core ℓ

private variable
  ι : Size
  P P' Q Q' R R' S S' T T' U U' V V' : Prop' ∞
  A B : Set ℓ
  F : A → Set ℓ
  P˙ Q˙ : A → Prop' ∞
  Jr : JudgRes

------------------------------------------------------------------------------
-- Modifying an element by a sequent

0-mono : P ⊢[ ι ] P' → P ∗ Q ⊢[ ι ] P' ∗ Q
0-mono = ∗-monoˡ

1'-mono : Q ⊢[ ι ] Q' → P ∗ Q ⊢[ ι ] P ∗ Q'
1'-mono = ∗-monoʳ

1-mono : Q ⊢[ ι ] Q' → P ∗ Q ∗ R ⊢[ ι ] P ∗ Q' ∗ R
1-mono = 1'-mono ∘ 0-mono

2'-mono : R ⊢[ ι ] R' → P ∗ Q ∗ R ⊢[ ι ] P ∗ Q ∗ R'
2'-mono = 1'-mono ∘ 1'-mono

2-mono : R ⊢[ ι ] R' → P ∗ Q ∗ R ∗ S ⊢[ ι ] P ∗ Q ∗ R' ∗ S
2-mono = 2'-mono ∘ 0-mono

3'-mono : S ⊢[ ι ] S' → P ∗ Q ∗ R ∗ S ⊢[ ι ] P ∗ Q ∗ R ∗ S'
3'-mono = 2'-mono ∘ 1'-mono

3-mono : S ⊢[ ι ] S' → P ∗ Q ∗ R ∗ S ∗ T ⊢[ ι ] P ∗ Q ∗ R ∗ S' ∗ T
3-mono = 3'-mono ∘ 0-mono

4'-mono : T ⊢[ ι ] T' → P ∗ Q ∗ R ∗ S ∗ T ⊢[ ι ] P ∗ Q ∗ R ∗ S ∗ T'
4'-mono = 3'-mono ∘ 1'-mono

4-mono : T ⊢[ ι ] T' → P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ ι ] P ∗ Q ∗ R ∗ S ∗ T' ∗ U
4-mono = 4'-mono ∘ 0-mono

5'-mono : U ⊢[ ι ] U' → P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ ι ] P ∗ Q ∗ R ∗ S ∗ T ∗ U'
5'-mono = 4'-mono ∘ 1'-mono

5-mono : U ⊢[ ι ] U' →
  P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ ι ] P ∗ Q ∗ R ∗ S ∗ T ∗ U' ∗ V
5-mono = 5'-mono ∘ 0-mono

6'-mono : V ⊢[ ι ] V' →
  P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ ι ] P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V'
6'-mono = 5'-mono ∘ 1'-mono

------------------------------------------------------------------------------
-- Moving an element to the head

1'⇒0 : P ∗ Q ⊢[ ι ] Q ∗ P
1'⇒0 = ∗-comm

1⇒0 : P ∗ Q ∗ R ⊢[ ι ] Q ∗ P ∗ R
1⇒0 = ∗-assocʳ » ∗-monoˡ ∗-comm » ∗-assocˡ

2'⇒0 : P ∗ Q ∗ R ⊢[ ι ] R ∗ P ∗ Q
2'⇒0 = 1'-mono 1'⇒0 » 1⇒0

2⇒0 : P ∗ Q ∗ R ∗ S ⊢[ ι ] R ∗ P ∗ Q ∗ S
2⇒0 = 1'-mono 1⇒0 » 1⇒0

3'⇒0 : P ∗ Q ∗ R ∗ S ⊢[ ι ] S ∗ P ∗ Q ∗ R
3'⇒0 = 1'-mono 2'⇒0 » 1⇒0

3⇒0 : P ∗ Q ∗ R ∗ S ∗ T ⊢[ ι ] S ∗ P ∗ Q ∗ R ∗ T
3⇒0 = 1'-mono 2⇒0 » 1⇒0

4'⇒0 : P ∗ Q ∗ R ∗ S ∗ T ⊢[ ι ] T ∗ P ∗ Q ∗ R ∗ S
4'⇒0 = 1'-mono 3'⇒0 » 1⇒0

4⇒0 : P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ ι ] T ∗ P ∗ Q ∗ R ∗ S ∗ U
4⇒0 = 1'-mono 3⇒0 » 1⇒0

5'⇒0 : P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ ι ] U ∗ P ∗ Q ∗ R ∗ S ∗ T
5'⇒0 = 1'-mono 4'⇒0 » 1⇒0

5⇒0 : P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ ι ] U ∗ P ∗ Q ∗ R ∗ S ∗ T ∗ V
5⇒0 = 1'-mono 4⇒0 » 1⇒0

6'⇒0 : P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ ι ] V ∗ P ∗ Q ∗ R ∗ S ∗ T ∗ U
6'⇒0 = 1'-mono 5'⇒0 » 1⇒0

------------------------------------------------------------------------------
-- Moving the head to somewhere

0⇒1' : P ∗ Q ⊢[ ι ] Q ∗ P
0⇒1' = 1'⇒0

0⇒1 : P ∗ Q ∗ R ⊢[ ι ] Q ∗ P ∗ R
0⇒1 = 1⇒0

0⇒2' : P ∗ Q ∗ R ⊢[ ι ] Q ∗ R ∗ P
0⇒2' = 0⇒1 » 1'-mono 0⇒1'

0⇒2 : P ∗ Q ∗ R ∗ S ⊢[ ι ] Q ∗ R ∗ P ∗ S
0⇒2 = 0⇒1 » 1'-mono 0⇒1

0⇒3' : P ∗ Q ∗ R ∗ S ⊢[ ι ] Q ∗ R ∗ S ∗ P
0⇒3' = 0⇒1 » 1'-mono 0⇒2'

0⇒3 : P ∗ Q ∗ R ∗ S ∗ T ⊢[ ι ] Q ∗ R ∗ S ∗ P ∗ T
0⇒3 = 0⇒1 » 1'-mono 0⇒2

0⇒4' : P ∗ Q ∗ R ∗ S ∗ T ⊢[ ι ] Q ∗ R ∗ S ∗ T ∗ P
0⇒4' = 0⇒1 » 1'-mono 0⇒3'

0⇒4 : P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ ι ] Q ∗ R ∗ S ∗ T ∗ P ∗ U
0⇒4 = 0⇒1 » 1'-mono 0⇒3

0⇒5' : P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ ι ] Q ∗ R ∗ S ∗ T ∗ U ∗ P
0⇒5' = 0⇒1 » 1'-mono 0⇒4'

0⇒5 : P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ ι ] Q ∗ R ∗ S ∗ T ∗ U ∗ P ∗ V
0⇒5 = 0⇒1 » 1'-mono 0⇒4

0⇒6' : P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ ι ] Q ∗ R ∗ S ∗ T ∗ U ∗ V ∗ P
0⇒6' = 0⇒1 » 1'-mono 0⇒5'

------------------------------------------------------------------------------
-- Operations on the head

-- Eliminated the head
0⇒ : P ∗ Q ⊢[ ι ] Q
0⇒ = ∗-elimʳ

-- Use only the head
by0 : P ∗ Q ⊢[ ι ] P
by0 = ∗-elimˡ

-- Split the head
0-split : (P ∗ Q) ∗ R ⊢[ ι ] P ∗ Q ∗ R
0-split = ∗-assocˡ

-- Merge the two at the head
01-merge : P ∗ Q ∗ R ⊢[ ι ] (P ∗ Q) ∗ R
01-merge = ∗-assocʳ

-- Duplicate the head when it is persistent
0-dup-Pers : {{Pers P}} → P ∗ Q ⊢[ ι ] P ∗ P ∗ Q
0-dup-Pers = 0-mono dup-Pers » ∗-assocˡ

-- Introduce ⊤ to the head
⊤⇒0 : P ⊢[ ι ] ⊤ ∗ P
⊤⇒0 = ⊤∗-intro

-- Eliminate ∃/∨/⊥ from the head

0-∃-elim : (∀ a → P˙ a ∗ Q ⊢[ ι ]* Jr) → (∃˙ _ P˙) ∗ Q ⊢[ ι ]* Jr
0-∃-elim →P˙∗⊢ = ∗-comm » ∗-∃-out » ∃-elim $ λ a → ∗-comm » →P˙∗⊢ a

0-∨-elim : P ∗ Q ⊢[ ι ]* Jr → P' ∗ Q ⊢[ ι ]* Jr → (P ∨ P') ∗ Q ⊢[ ι ]* Jr
0-∨-elim P∗⊢ P'∗⊢ = 0-∃-elim (2-ary P∗⊢ P'∗⊢)

0-⊥-elim : ⊥ ∗ Q ⊢[ ι ]* Jr
0-⊥-elim = ∗-elimˡ » ⊥-elim

-- Introduce ⌜ ⌝ to the head

⌜⌝⇒0 : A → P ⊢[ ι ] ⌜ A ⌝ ∗ P
⌜⌝⇒0 = ⌜⌝∗-intro

-- Eliminate ⌜ ⌝ from the head

0-⌜⌝-elim : (A → Q ⊢[ ι ] R) → ⌜ A ⌝ ∗ Q ⊢[ ι ] R
0-⌜⌝-elim = ⌜⌝∗-elim

-- Apply the head to the succedent

0--∗-apply : Q ⊢[ ι ] P → (P -∗ P') ∗ Q ⊢[ ι ] P'
0--∗-apply Q⊢P = 0-mono (-∗-monoˡ Q⊢P) » 0⇒1' » -∗-apply
