------------------------------------------------------------------------
-- Proof-mode-like rules in Shog
------------------------------------------------------------------------

-- The rules work for a proposition P ∗ Q ∗ R ∗ ...
-- (Recall that ∗ is right-associative)

{-# OPTIONS --sized-types #-}

module Shog.Logic.ProofMode where

open import Level using (Level)
open import Size using (Size; ∞)
open import Function.Base using (_$_; _∘_)

open import Shog.Util using (binary)
open import Shog.Logic.Prop
open import Shog.Logic.Core

private variable
  ℓ : Level
  i : Size
  P P' Q Q' R R' S S' T T' U U' V V' : Propˢ ℓ ∞
  A B : Set ℓ
  F : A → Set ℓ
  Pᶠ Qᶠ : A → Propˢ ℓ ∞
  Jr : JudgRes ℓ

------------------------------------------------------------------------
-- Modifying an element by a sequent

0-mono : P ⊢[ i ] P' → P ∗ Q ⊢[ i ] P' ∗ Q
0-mono = ∗-mono₀

1'-mono : Q ⊢[ i ] Q' → P ∗ Q ⊢[ i ] P ∗ Q'
1'-mono = ∗-mono₁

1-mono : Q ⊢[ i ] Q' → P ∗ Q ∗ R ⊢[ i ] P ∗ Q' ∗ R
1-mono = 1'-mono ∘ 0-mono

2'-mono : R ⊢[ i ] R' → P ∗ Q ∗ R ⊢[ i ] P ∗ Q ∗ R'
2'-mono = 1'-mono ∘ 1'-mono

2-mono : R ⊢[ i ] R' → P ∗ Q ∗ R ∗ S ⊢[ i ] P ∗ Q ∗ R' ∗ S
2-mono = 2'-mono ∘ 0-mono

3'-mono : S ⊢[ i ] S' → P ∗ Q ∗ R ∗ S ⊢[ i ] P ∗ Q ∗ R ∗ S'
3'-mono = 2'-mono ∘ 1'-mono

3-mono : S ⊢[ i ] S' → P ∗ Q ∗ R ∗ S ∗ T ⊢[ i ] P ∗ Q ∗ R ∗ S' ∗ T
3-mono = 3'-mono ∘ 0-mono

4'-mono : T ⊢[ i ] T' → P ∗ Q ∗ R ∗ S ∗ T ⊢[ i ] P ∗ Q ∗ R ∗ S ∗ T'
4'-mono = 3'-mono ∘ 1'-mono

4-mono : T ⊢[ i ] T' → P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ i ] P ∗ Q ∗ R ∗ S ∗ T' ∗ U
4-mono = 4'-mono ∘ 0-mono

5'-mono : U ⊢[ i ] U' → P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ i ] P ∗ Q ∗ R ∗ S ∗ T ∗ U'
5'-mono = 4'-mono ∘ 1'-mono

5-mono : U ⊢[ i ] U' →
  P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ i ] P ∗ Q ∗ R ∗ S ∗ T ∗ U' ∗ V
5-mono = 5'-mono ∘ 0-mono

6'-mono : V ⊢[ i ] V' →
  P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ i ] P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V'
6'-mono = 5'-mono ∘ 1'-mono

------------------------------------------------------------------------
-- Moving an element to the head

1'⇒0 : P ∗ Q ⊢[ i ] Q ∗ P
1'⇒0 = ∗-comm

1⇒0 : P ∗ Q ∗ R ⊢[ i ] Q ∗ P ∗ R
1⇒0 = ∗-assoc₁ » ∗-mono₀ ∗-comm » ∗-assoc₀

2'⇒0 : P ∗ Q ∗ R ⊢[ i ] R ∗ P ∗ Q
2'⇒0 = 1'-mono 1'⇒0 » 1⇒0

2⇒0 : P ∗ Q ∗ R ∗ S ⊢[ i ] R ∗ P ∗ Q ∗ S
2⇒0 = 1'-mono 1⇒0 » 1⇒0

3'⇒0 : P ∗ Q ∗ R ∗ S ⊢[ i ] S ∗ P ∗ Q ∗ R
3'⇒0 = 1'-mono 2'⇒0 » 1⇒0

3⇒0 : P ∗ Q ∗ R ∗ S ∗ T ⊢[ i ] S ∗ P ∗ Q ∗ R ∗ T
3⇒0 = 1'-mono 2⇒0 » 1⇒0

4'⇒0 : P ∗ Q ∗ R ∗ S ∗ T ⊢[ i ] T ∗ P ∗ Q ∗ R ∗ S
4'⇒0 = 1'-mono 3'⇒0 » 1⇒0

4⇒0 : P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ i ] T ∗ P ∗ Q ∗ R ∗ S ∗ U
4⇒0 = 1'-mono 3⇒0 » 1⇒0

5'⇒0 : P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ i ] U ∗ P ∗ Q ∗ R ∗ S ∗ T
5'⇒0 = 1'-mono 4'⇒0 » 1⇒0

5⇒0 : P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ i ] U ∗ P ∗ Q ∗ R ∗ S ∗ T ∗ V
5⇒0 = 1'-mono 4⇒0 » 1⇒0

6'⇒0 : P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ i ] V ∗ P ∗ Q ∗ R ∗ S ∗ T ∗ U
6'⇒0 = 1'-mono 5'⇒0 » 1⇒0

------------------------------------------------------------------------
-- Moving the head to somewhere

0⇒1' : P ∗ Q ⊢[ i ] Q ∗ P
0⇒1' = 1'⇒0

0⇒1 : P ∗ Q ∗ R ⊢[ i ] Q ∗ P ∗ R
0⇒1 = 1⇒0

0⇒2' : P ∗ Q ∗ R ⊢[ i ] Q ∗ R ∗ P
0⇒2' = 0⇒1 » 1'-mono 0⇒1'

0⇒2 : P ∗ Q ∗ R ∗ S ⊢[ i ] Q ∗ R ∗ P ∗ S
0⇒2 = 0⇒1 » 1'-mono 0⇒1

0⇒3' : P ∗ Q ∗ R ∗ S ⊢[ i ] Q ∗ R ∗ S ∗ P
0⇒3' = 0⇒1 » 1'-mono 0⇒2'

0⇒3 : P ∗ Q ∗ R ∗ S ∗ T ⊢[ i ] Q ∗ R ∗ S ∗ P ∗ T
0⇒3 = 0⇒1 » 1'-mono 0⇒2

0⇒4' : P ∗ Q ∗ R ∗ S ∗ T ⊢[ i ] Q ∗ R ∗ S ∗ T ∗ P
0⇒4' = 0⇒1 » 1'-mono 0⇒3'

0⇒4 : P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ i ] Q ∗ R ∗ S ∗ T ∗ P ∗ U
0⇒4 = 0⇒1 » 1'-mono 0⇒3

0⇒5' : P ∗ Q ∗ R ∗ S ∗ T ∗ U ⊢[ i ] Q ∗ R ∗ S ∗ T ∗ U ∗ P
0⇒5' = 0⇒1 » 1'-mono 0⇒4'

0⇒5 : P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ i ] Q ∗ R ∗ S ∗ T ∗ U ∗ P ∗ V
0⇒5 = 0⇒1 » 1'-mono 0⇒4

0⇒6' : P ∗ Q ∗ R ∗ S ∗ T ∗ U ∗ V ⊢[ i ] Q ∗ R ∗ S ∗ T ∗ U ∗ V ∗ P
0⇒6' = 0⇒1 » 1'-mono 0⇒5'

------------------------------------------------------------------------
-- Operations on the head

0⇒ : P ∗ Q ⊢[ i ] Q
0⇒ = ∗-elim₁

by0 : P ∗ Q ⊢[ i ] P
by0 = ∗-elim₀

0-split : (P ∗ Q) ∗ R ⊢[ i ] P ∗ Q ∗ R
0-split = ∗-assoc₀

01-merge : P ∗ Q ∗ R ⊢[ i ] (P ∗ Q) ∗ R
01-merge = ∗-assoc₁

0-dup-Pers : {{Pers P}} → P ∗ Q ⊢[ i ] P ∗ P ∗ Q
0-dup-Pers = 0-mono dup-Pers » ∗-assoc₀

⊤⇒0 : P ⊢[ i ] ⊤ˢ ∗ P
⊤⇒0 = ⊤∗-intro

0-∃-elim : (∀ a → Pᶠ a ∗ Q ⊢[ i ]* Jr) → (∃^ _ Pᶠ) ∗ Q ⊢[ i ]* Jr
0-∃-elim →Pᶠ∗⊢ = ∗-comm » ∗-∃-out » ∃-elim $ λ a → ∗-comm » →Pᶠ∗⊢ a

0-∨-elim : P ∗ Q ⊢[ i ]* Jr → P' ∗ Q ⊢[ i ]* Jr → (P ∨ˢ P') ∗ Q ⊢[ i ]* Jr
0-∨-elim P∗⊢ P'∗⊢ = 0-∃-elim (binary P∗⊢ P'∗⊢)

0-⊥-elim : ⊥ˢ ∗ Q ⊢[ i ]* Jr
0-⊥-elim = ∗-elim₀ » ⊥-elim

⌜⌝⇒0 : A → P ⊢[ i ] ⌜ A ⌝ ∗ P
⌜⌝⇒0 = ⌜⌝∗-intro

0-⌜⌝-elim : (A → Q ⊢[ i ] R) → ⌜ A ⌝ ∗ Q ⊢[ i ] R
0-⌜⌝-elim = ⌜⌝∗-elim

0--∗-apply : Q ⊢[ i ] P → (P -∗ P') ∗ Q ⊢[ i ] P'
0--∗-apply Q⊢P = 0-mono (-∗-mono₀ Q⊢P) » 0⇒1' » -∗-apply
