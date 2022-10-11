--------------------------------------------------------------------------------
-- Prove the semantic soundness of the pure sequent
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Sound where

open import Base.Func using (_$_; _›_; id)
open import Base.Few using (0₂; 1₂; binary; absurd)
open import Base.Size using (Size; ∞; !)
open import Base.Prod using (_,_; π₀; π₁; ∑-case)
open import Syho.Logic.Prop using (Prop∞)
open import Syho.Logic.Core using (_⊢[_]_; ⊢-refl; _»_; ∀-intro; ∃-elim; ∀-elim;
  ∃-intro; choice; →-intro; →-elim; ∗-monoˡ; ⊤∗-elim; ⊤∗-intro; ∗-comm;
  ∗-assocˡ; -∗-intro; -∗-elim; ⤇-mono; ⤇-intro; ⤇-join; ⤇-eatˡ; ⤇-⌜⌝∧-out;
  □-mono; □-elim; □-dup; □ˡ-∧⇒∗; □-∀-in; □-∃-out)
open import Syho.Logic.Mem using (↦⟨⟩-merge; ↦⟨⟩-split; ↦⟨⟩-≤1; ↦⟨⟩-agree)
open import Syho.Logic.Ind using (○-mono; ○-eatˡ; ↪⇛-≤; ↪⇛-eatˡ⁻ˡᵘ; ↪⇛-monoʳᵘ;
  ↪⇛-eatˡ⁻ʳ; ↪⇛-frameˡ; ○⇒↪⇛;  ↪ᵃ⟨⟩-≤; ↪ᵃ⟨⟩-eatˡ⁻ˡᵘ; ↪ᵃ⟨⟩-monoʳᵘ; ↪ᵃ⟨⟩-eatˡ⁻ʳ;
  ↪ᵃ⟨⟩-frameˡ; ○⇒↪ᵃ⟨⟩; ↪⟨⟩ᵀ⇒↪⟨⟩ᴾ; ↪⟨⟩ᵀ-≤; ↪⟨⟩-eatˡ⁻ˡᵘᴺ; ↪⟨⟩-monoʳᵘᴺ; ↪⟨⟩-eatˡ⁻ʳ;
  ↪⟨⟩-frameˡ; ○⇒↪⟨⟩; ↪⟨⟩∞-≤; ↪⟨⟩∞-eatˡ⁻ᵘᴺ; ○⇒↪⟨⟩∞)
open import Syho.Logic.Inv using ([]ᴺ-resp; []ᴺ-merge; []ᴺ-split; []ᴺ-✔; Inv-⇒□;
  Inv-resp-□∧; OInv-mono; OInv-eatˡ)
open import Syho.Logic.Lft using ([]ᴸ⟨⟩-merge; []ᴸ⟨⟩-split; []ᴸ⟨⟩-≤1; †ᴸ-⇒□;
  []ᴸ⟨⟩-†ᴸ-no; []ᴸ-alloc)
open import Syho.Model.Prop.Base using (_⊨✓_; →ᵒ-intro; →ᵒ-elim; ∗ᵒ-monoˡ;
  ∗ᵒ-mono✓ˡ; ?∗ᵒ-intro; ∗ᵒ-elimʳ; ∗ᵒ-comm; ∗ᵒ-assocˡ; -∗ᵒ-intro; -∗ᵒ-elim;
  ⤇ᵒ-mono✓; ⤇ᵒ-intro; ⤇ᵒ-join; ⤇ᵒ-eatˡ; ⤇ᵒ-⌜⌝ᵒ×-out; □ᵒ-mono✓; □ᵒ-elim; □ᵒ-dup;
  □ᵒˡ-×ᵒ⇒∗ᵒ)
open import Syho.Model.Prop.Mem using (↦⟨⟩ᵒ-merge; ↦⟨⟩ᵒ-split; ↦⟨⟩ᵒ-≤1;
  ↦⟨⟩ᵒ-agree)
open import Syho.Model.Prop.Names using ([]ᴺᵒ-resp; []ᴺᵒ-merge; []ᴺᵒ-split;
  []ᴺᵒ-✔)
open import Syho.Model.Prop.Ind using (○ᵒ-mono; ○ᵒ-eatˡ; ↪⇛ᵒ-≤; ↪⇛ᵒ-eatˡ⁻ˡᵘ;
  ↪⇛ᵒ-monoʳᵘ; ↪⇛ᵒ-eatˡ⁻ʳ; ↪⇛ᵒ-frameˡ; ○ᵒ⇒↪⇛ᵒ; ↪ᵃ⟨⟩ᵒ-≤; ↪ᵃ⟨⟩ᵒ-eatˡ⁻ˡᵘ;
  ↪ᵃ⟨⟩ᵒ-monoʳᵘ; ↪ᵃ⟨⟩ᵒ-eatˡ⁻ʳ; ↪ᵃ⟨⟩ᵒ-frameˡ; ○ᵒ⇒↪ᵃ⟨⟩ᵒ; ↪⟨⟩ᵀᵒ⇒↪⟨⟩ᴾᵒ; ↪⟨⟩ᵀᵒ-≤;
  ↪⟨⟩ᵒ-eatˡ⁻ˡᵘᴺ; ↪⟨⟩ᵒ-monoʳᵘᴺ; ↪⟨⟩ᵒ-eatˡ⁻ʳ; ↪⟨⟩ᵒ-frameˡ; ○ᵒ⇒↪⟨⟩ᵒ; ↪⟨⟩∞ᵒ-≤;
  ↪⟨⟩∞ᵒ-eatˡ⁻ᵘᴺ; ○ᵒ⇒↪⟨⟩∞ᵒ)
open import Syho.Model.Prop.Inv using (Invᵒ-⇒□ᵒ; Invᵒ-resp-□ᵒ×ᵒ; OInvᵒ-mono;
  OInvᵒ-eatˡ)
open import Syho.Model.Prop.Lft using ([]ᴸ⟨⟩ᵒ-merge; []ᴸ⟨⟩ᵒ-split; []ᴸ⟨⟩ᵒ-≤1;
  †ᴸᵒ-⇒□ᵒ; []ᴸ⟨⟩ᵒ-†ᴸᵒ-no; []ᴸᵒ-alloc)
open import Syho.Model.Prop.Interp using (⸨_⸩; ⸨⸩-Mono; ⸨⸩-⇒ᴮ)

private variable
  P Q R S T :  Prop∞

--------------------------------------------------------------------------------
-- ⊢-sem :  Semantic soundness of the pure sequent

abstract

  ⊢-sem :  P ⊢[ ∞ ] Q →  ⸨ P ⸩ ⊨✓ ⸨ Q ⸩

  -- ⊢-refl :  P ⊢[ ∞ ] P

  ⊢-sem ⊢-refl _ =  id

  -- _»_ :  P ⊢[ ∞ ] Q →  Q ⊢[ ∞ ] R →  P ⊢[ ∞ ] R

  ⊢-sem (P⊢Q » Q⊢R) ✓a =  ⊢-sem P⊢Q ✓a › ⊢-sem Q⊢R ✓a

  -- ∀-intro :  (∀' x → P ⊢[ ∞ ] Q˙ x) →  P ⊢[ ∞ ] ∀˙ Q˙

  ⊢-sem (∀-intro ∀xP⊢Qx) ✓a Pa x =  ⊢-sem (∀xP⊢Qx x) ✓a Pa

  -- ∃-elim :  (∀' x → P˙ x ⊢[ ∞ ] Q) →  ∃˙ P˙ ⊢[ ∞ ] Q

  ⊢-sem (∃-elim ∀xPx⊢Q) ✓a =  ∑-case λ x → ⊢-sem (∀xPx⊢Q x) ✓a

  -- ∀-elim :  ∀ x →  ∀˙ P˙ ⊢[ ∞ ] P˙ x

  ⊢-sem (∀-elim x) _ ∀Pa =  ∀Pa x

  -- ∃-intro :  ∀ x →  P˙ x ⊢[ ∞ ] ∃˙ P˙

  ⊢-sem (∃-intro x) _ Px =  x , Px

  -- choice :  ∀' x , ∃ y , P˙˙ x y ⊢[ ∞ ] ∃ y˙ , ∀' x , P˙˙ x (y˙ x)

  -- It can be proved axiom-free thanks to the logic's predicativity

  ⊢-sem choice _ ∀x∃yPxy .π₀ x =  ∀x∃yPxy x .π₀
  ⊢-sem choice _ ∀x∃yPxy .π₁ x =  ∀x∃yPxy x .π₁

  -- →-intro :  P ∧ Q ⊢[ ∞ ] R →  Q ⊢[ ∞ ] P →' R

  ⊢-sem (→-intro {Q = Q} P∧Q⊢R) _ =
    →ᵒ-intro (⸨⸩-Mono {Q}) λ ✓b (Pb , Qb) → ⊢-sem P∧Q⊢R ✓b $ binary Pb Qb

  -- →-elim :  Q ⊢[ ∞ ] P →' R →  P ∧ Q ⊢[ ∞ ] R

  ⊢-sem (→-elim Q⊢P→R) ✓a P∧Qa =  →ᵒ-elim (⊢-sem Q⊢P→R) ✓a (P∧Qa 0₂ , P∧Qa 1₂)

  -- ∗-monoˡ :  P ⊢[ ∞ ] Q →  P ∗ R ⊢[ ∞ ] Q ∗ R

  ⊢-sem (∗-monoˡ P⊢Q) =  ∗ᵒ-mono✓ˡ (⊢-sem P⊢Q)

  -- ⊤∗-elim :  ⊤' ∗ P ⊢[ ∞ ] P

  ⊢-sem (⊤∗-elim {P}) _ =  ∗ᵒ-elimʳ $ ⸨⸩-Mono {P}

  -- ⊤∗-intro :  P ⊢[ ∞ ] ⊤' ∗ P

  ⊢-sem ⊤∗-intro _ =  ?∗ᵒ-intro absurd

  -- ∗-comm :  P ∗ Q ⊢[ ∞ ] Q ∗ P

  ⊢-sem ∗-comm _ =  ∗ᵒ-comm

  -- ∗-assocˡ :  (P ∗ Q) ∗ R ⊢[ ∞ ] P ∗ (Q ∗ R)

  ⊢-sem ∗-assocˡ _ =  ∗ᵒ-assocˡ

  -- -∗-intro :  P ∗ Q ⊢[ ∞ ] R →  Q ⊢[ ∞ ] P -∗ R

  ⊢-sem (-∗-intro P∗Q⊢R) _ =  -∗ᵒ-intro $ ⊢-sem P∗Q⊢R

  -- -∗-elim :  Q ⊢[ ∞ ] P -∗ R →  P ∗ Q ⊢[ ∞ ] R

  ⊢-sem (-∗-elim {R = R} Q⊢P-∗R) =  -∗ᵒ-elim (⸨⸩-Mono {R}) $ ⊢-sem Q⊢P-∗R

  -- ⤇-mono :  P ⊢[ ∞ ] Q →  ⤇ P ⊢[ ∞ ] ⤇ Q

  ⊢-sem (⤇-mono P⊢Q) _ =  ⤇ᵒ-mono✓ $ ⊢-sem P⊢Q

  -- ⤇-intro :  P ⊢[ ∞ ] ⤇ P

  ⊢-sem ⤇-intro _ =  ⤇ᵒ-intro

  -- ⤇-join :  ⤇ ⤇ P ⊢[ ∞ ] ⤇ P

  ⊢-sem ⤇-join _ =  ⤇ᵒ-join

  -- ⤇-eatˡ :  Q ∗ ⤇ P ⊢[ ∞ ] ⤇ (Q ∗ P)

  ⊢-sem ⤇-eatˡ _ =  ⤇ᵒ-eatˡ

  -- ⤇-⌜⌝∧-out :  ⤇ (⌜ X ⌝∧ P) ⊢[ ∞ ] ⌜ X ⌝∧ ⤇ P

  ⊢-sem ⤇-⌜⌝∧-out =  ⤇ᵒ-⌜⌝ᵒ×-out

  -- □-mono :  P ⊢[ ∞ ] Q →  □ P ⊢[ ∞ ] □ Q

  ⊢-sem (□-mono P⊢Q) =  □ᵒ-mono✓ $ ⊢-sem P⊢Q

  -- □-elim :  □ P ⊢[ ∞ ] P

  ⊢-sem (□-elim {P}) _ =  □ᵒ-elim $ ⸨⸩-Mono {P}

  -- □-dup :  □ P ⊢[ ∞ ] □ □ P

  ⊢-sem (□-dup {P}) _ =   □ᵒ-dup $ ⸨⸩-Mono {P}

  -- □ˡ-∧⇒∗ :  □ P ∧ Q ⊢[ ∞ ] □ P ∗ Q

  ⊢-sem (□ˡ-∧⇒∗ {P}) _ □P∧Qa =  □ᵒˡ-×ᵒ⇒∗ᵒ (⸨⸩-Mono {P}) (□P∧Qa 0₂ , □P∧Qa 1₂)

  -- □-∀-in :  ∀˙ (□_ ∘ P˙) ⊢[ ∞ ] □ ∀˙ P˙

  ⊢-sem □-∀-in _ =  id

  -- □-∃-out :  □ ∃˙ P˙ ⊢[ ∞ ] ∃˙ (□_ ∘ P˙)

  ⊢-sem □-∃-out _ =  id

  -- ↦⟨⟩-merge :  θ ↦⟨ p ⟩ ᵗv  ∗  θ ↦⟨ q ⟩ ᵗv  ⊢[ ∞ ]  θ ↦⟨ p +ᴿ⁺ q ⟩ ᵗv

  ⊢-sem ↦⟨⟩-merge _ =  ↦⟨⟩ᵒ-merge

  -- ↦⟨⟩-split :  θ ↦⟨ p +ᴿ⁺ q ⟩ ᵗv  ⊢[ ∞ ]  θ ↦⟨ p ⟩ ᵗv  ∗  θ ↦⟨ q ⟩ ᵗv

  ⊢-sem ↦⟨⟩-split _ =  ↦⟨⟩ᵒ-split

  -- ↦⟨⟩-≤1 :  θ ↦⟨ p ⟩ ᵗv  ⊢[ ∞ ]  ⌜ p ≤1ᴿ⁺ ⌝

  ⊢-sem ↦⟨⟩-≤1 ✓a =  ↦⟨⟩ᵒ-≤1 ✓a › (_, absurd)

  -- ↦⟨⟩-agree :  θ ↦⟨ p ⟩ ᵗu  ∗  θ ↦⟨ q ⟩ ᵗv  ⊢[ ∞ ]  ⌜ ᵗu ≡ ᵗv ⌝

  ⊢-sem ↦⟨⟩-agree ✓a =  ↦⟨⟩ᵒ-agree ✓a › (_, absurd)

  -- ○-mono :  P˂ .! ⊢[< ∞ ] Q˂ .! →  ○ P˂ ⊢[ ∞ ] ○ Q˂

  ⊢-sem (○-mono P⊢Q) _ =  ○ᵒ-mono $ P⊢Q .!

  -- ○-eatˡ :  {{Basic Q}} →  Q ∗ ○ P˂ ⊢[ ∞ ] ○ ¡ (Q ∗ P˂ .!)

  ⊢-sem (○-eatˡ {Q}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {Q}) › ○ᵒ-eatˡ

  -- ↪⇛-≤ :  i ≤ j  →   P˂ ↪[ i ]⇛ Q˂  ⊢[ ∞ ]  P˂ ↪[ j ]⇛ Q˂

  ⊢-sem (↪⇛-≤ i≤j) _ =  ↪⇛ᵒ-≤ i≤j

  -- ↪⇛-eatˡ⁻ˡᵘ :  {{Basic R}}  →   R  ∗  P'˂ .!  ⊢[< ∞ ][ i ]⇛  P˂ .! →
  --               R  ∗  (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ∞ ]  P'˂ ↪[ i ]⇛ Q˂

  ⊢-sem (↪⇛-eatˡ⁻ˡᵘ {R} R∗P'⊢⇛P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⇛ᵒ-eatˡ⁻ˡᵘ $ R∗P'⊢⇛P .!

  -- ↪⇛-monoʳᵘ :  Q˂ .!  ⊢[< ∞ ][ i ]⇛  Q'˂ .! →
  --              P˂ ↪[ i ]⇛ Q˂  ⊢[ ∞ ]  P˂ ↪[ i ]⇛ Q'˂

  ⊢-sem (↪⇛-monoʳᵘ Q⊢⇛Q') _ =  ↪⇛ᵒ-monoʳᵘ $ Q⊢⇛Q' .!

  -- ↪⇛-eatˡ⁻ʳ :  {{Basic R}}  →
  --   R  ∗  (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ∞ ]  P˂ ↪[ i ]⇛ ¡ (R ∗ Q˂ .!)

  ⊢-sem (↪⇛-eatˡ⁻ʳ {R}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⇛ᵒ-eatˡ⁻ʳ

  -- ↪⇛-frameˡ :  P˂ ↪[ i ]⇛ Q˂  ⊢[ ∞ ]  ¡ (R ∗ P˂ .!) ↪[ i ]⇛ ¡ (R ∗ Q˂ .!)

  ⊢-sem ↪⇛-frameˡ _ =  ↪⇛ᵒ-frameˡ

  -- ○⇒↪⇛ :  P˂ .!  ∗  R˂ .! ⊢[< ∞ ][ i ]⇛  Q˂ .!  →
  --         ○ R˂  ⊢[ ∞ ]  P˂ ↪[ i ]⇛ Q˂

  ⊢-sem (○⇒↪⇛ P∗R⊢⇛Q) _ =  ○ᵒ⇒↪⇛ᵒ $ P∗R⊢⇛Q .!

  -- ↪ᵃ⟨⟩-≤ :  i ≤ j  →   P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ∞ ]  P˂ ↪[ j ]ᵃ⟨ red ⟩ Q˂˙

  ⊢-sem (↪ᵃ⟨⟩-≤ i≤j) _ =  ↪ᵃ⟨⟩ᵒ-≤ i≤j

  -- ↪ᵃ⟨⟩-eatˡ⁻ˡᵘ :  {{Basic R}}  →   R  ∗  P'˂ .!  ⊢[< ∞ ][ i ]⇛  P˂ .!  →
  --                 R ∗ (P˂ ↪[ j ]ᵃ⟨ red ⟩ Q˂˙)  ⊢[ ∞ ]  P'˂ ↪[ j ]ᵃ⟨ red ⟩ Q˂˙

  ⊢-sem (↪ᵃ⟨⟩-eatˡ⁻ˡᵘ {R} R∗P'⊢⇛P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪ᵃ⟨⟩ᵒ-eatˡ⁻ˡᵘ $ R∗P'⊢⇛P .!

  -- ↪ᵃ⟨⟩-monoʳᵘ :  (∀ v →  Q˂˙ v .!  ⊢[< ∞ ][ i ]⇛  Q'˂˙ v .!)  →
  --                P˂ ↪[ j ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ∞ ]  P˂ ↪[ j ]ᵃ⟨ red ⟩ Q'˂˙

  ⊢-sem (↪ᵃ⟨⟩-monoʳᵘ ∀vQ⊢⇛Q') _ =  ↪ᵃ⟨⟩ᵒ-monoʳᵘ λ v → ∀vQ⊢⇛Q' v .!

  -- ↪ᵃ⟨⟩-eatˡ⁻ʳ :  {{Basic R}}  →
  --   R  ∗  (P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙)  ⊢[ ∞ ]
  --     P˂ ↪[ i ]ᵃ⟨ red ⟩ λ v → ¡ (R ∗ Q˂˙ v .!)

  ⊢-sem (↪ᵃ⟨⟩-eatˡ⁻ʳ {R}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪ᵃ⟨⟩ᵒ-eatˡ⁻ʳ

  -- ↪ᵃ⟨⟩-frameˡ :  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ∞ ]
  --                  ¡ (R ∗ P˂ .!) ↪[ i ]ᵃ⟨ red ⟩ λ v → ¡ (R ∗ Q˂˙ v .!)

  ⊢-sem ↪ᵃ⟨⟩-frameˡ _ =  ↪ᵃ⟨⟩ᵒ-frameˡ

  -- ○⇒↪ᵃ⟨⟩ :  P˂ .!  ∗  R˂ .!  ⊢[< ∞ ][ i ]ᵃ⟨ red ⟩ (λ v →  Q˂˙ v .!)  →
  --           ○ R˂  ⊢[ ∞ ]  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙

  ⊢-sem (○⇒↪ᵃ⟨⟩ P∗R⊢⟨red⟩Q) _ =  ○ᵒ⇒↪ᵃ⟨⟩ᵒ $ P∗R⊢⟨red⟩Q .!

  -- ↪⟨⟩ᵀ⇒↪⟨⟩ᴾ :  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ∞ ]  P˂ ↪⟨ e ⟩ᴾ Q˂˙

  ⊢-sem ↪⟨⟩ᵀ⇒↪⟨⟩ᴾ _ =  ↪⟨⟩ᵀᵒ⇒↪⟨⟩ᴾᵒ

  -- ↪⟨⟩ᵀ-≤ :  i ≤ j  →   P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ∞ ]  P˂ ↪⟨ e ⟩ᵀ[ j ] Q˂˙

  ⊢-sem (↪⟨⟩ᵀ-≤ i≤j) _ =  ↪⟨⟩ᵀᵒ-≤ i≤j

  -- ↪⟨⟩-eatˡ⁻ˡᵘᴺ :  {{Basic R}}  →   R  ∗  P'˂ .!  ⊢[< ∞ ][ i ]⇛ᴺ  P˂ .!  →
  --                 R  ∗  (P˂ ↪⟨ e ⟩[ κ ] Q˂˙)  ⊢[ ∞ ]  P'˂ ↪⟨ e ⟩[ κ ] Q˂˙

  ⊢-sem (↪⟨⟩-eatˡ⁻ˡᵘᴺ {R} R∗P'⊢⇛P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⟨⟩ᵒ-eatˡ⁻ˡᵘᴺ $ R∗P'⊢⇛P .!

  -- ↪⟨⟩-monoʳᵘᴺ :  (∀ v →  Q˂˙ v .!  ⊢[< ∞ ][ i ]⇛ᴺ  Q'˂˙ v .!)  →
  --                P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ∞ ]  P˂ ↪⟨ e ⟩[ κ ] Q'˂˙

  ⊢-sem (↪⟨⟩-monoʳᵘᴺ ∀vQ⊢⇛Q') _ =  ↪⟨⟩ᵒ-monoʳᵘᴺ λ v → ∀vQ⊢⇛Q' v .!

  -- ↪⟨⟩-eatˡ⁻ʳ :  {{Basic R}}  →
  --   R  ∗  (P˂ ↪⟨ e ⟩[ κ ] Q˂˙)  ⊢[ ∞ ]  P˂ ↪⟨ e ⟩[ κ ] λ v → ¡ (R ∗ Q˂˙ v .!)

  ⊢-sem (↪⟨⟩-eatˡ⁻ʳ {R}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⟨⟩ᵒ-eatˡ⁻ʳ

  -- ↪⟨⟩-frameˡ :  P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ∞ ]
  --                 ¡ (R ∗ P˂ .!) ↪⟨ e ⟩[ κ ] λ v → ¡ (R ∗ Q˂˙ v .!)

  ⊢-sem ↪⟨⟩-frameˡ _ =  ↪⟨⟩ᵒ-frameˡ

  -- ○⇒↪⟨⟩ :  P˂ .!  ∗  R˂ .! ⊢[< ∞ ]⟨ e ⟩[ κ ] (λ v →  Q˂˙ v .!)  →
  --          ○ R˂  ⊢[ ∞ ]  P˂ ↪⟨ e ⟩[ κ ] Q˂˙

  ⊢-sem (○⇒↪⟨⟩ P∗R⊢⟨e⟩Q) _ =  ○ᵒ⇒↪⟨⟩ᵒ $ P∗R⊢⟨e⟩Q .!

  -- ↪⟨⟩∞-≤ :  i ≤ j  →   P˂ ↪[ i ]⟨ e ⟩∞  ⊢[ ∞ ]  P˂ ↪[ j ]⟨ e ⟩∞

  ⊢-sem (↪⟨⟩∞-≤ i≤j) _ =  ↪⟨⟩∞ᵒ-≤ i≤j

  -- ↪⟨⟩∞-eatˡ⁻ᵘᴺ :  {{Basic R}}  →   R  ∗  Q˂ .!  ⊢[< ∞ ][ i ]⇛ᴺ  P˂ .!  →
  --                 R  ∗  (P˂ ↪[ j ]⟨ e ⟩∞)  ⊢[ ∞ ]  Q˂ ↪[ j ]⟨ e ⟩∞

  ⊢-sem (↪⟨⟩∞-eatˡ⁻ᵘᴺ {R} R∗Q⊢⇛P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⟨⟩∞ᵒ-eatˡ⁻ᵘᴺ $ R∗Q⊢⇛P .!

  -- ○⇒↪⟨⟩∞ :  P˂ .!  ∗  Q˂ .!  ⊢[< ∞ ][ i ]⟨ e ⟩∞   →
  --           ○ Q˂  ⊢[ ∞ ]  P˂ ↪[ i ]⟨ e ⟩∞

  ⊢-sem (○⇒↪⟨⟩∞ P∗Q⊢⟨e⟩∞) _ =  ○ᵒ⇒↪⟨⟩∞ᵒ $ P∗Q⊢⟨e⟩∞ .!

  -- []ᴺ-resp :  Nm ≡˙ Nm' →  [ Nm ]ᴺ ⊢[ ∞ ] [ Nm' ]ᴺ

  ⊢-sem ([]ᴺ-resp Nm≡Nm') _ =  []ᴺᵒ-resp Nm≡Nm'

  -- []ᴺ-merge :  [ Nm ]ᴺ  ∗  [ Nm' ]ᴺ  ⊢[ ∞ ]  [ Nm ⊎ᶻ Nm' ]ᴺ

  ⊢-sem []ᴺ-merge _ =  []ᴺᵒ-merge

  -- []ᴺ-split :  [ Nm ⊎ᶻ Nm' ]ᴺ  ⊢[ ∞ ]  [ Nm ]ᴺ  ∗  [ Nm' ]ᴺ

  ⊢-sem []ᴺ-split _ =  []ᴺᵒ-split

  -- []ᴺ-✔ :  [ Nm ]ᴺ  ⊢[ ∞ ]  ⌜ ✔ᶻ Nm ⌝

  ⊢-sem []ᴺ-✔ ✓∙ =  []ᴺᵒ-✔ ✓∙ › (_, absurd)

  -- Inv-⇒□ :  Inv nm P˂  ⊢[ ∞ ]  □ Inv nm P˂

  ⊢-sem Inv-⇒□ _ =  Invᵒ-⇒□ᵒ

  -- Inv-resp-□∧ :  {{Basic R}}  →
  --   R  ∧  P˂ .!  ⊢[< ∞ ]  Q˂ .!  →   R  ∧  Q˂ .!  ⊢[< ∞ ]  P˂ .!  →
  --   □ R  ∧  Inv nm P˂  ⊢[ ∞ ]  Inv nm Q˂

  ⊢-sem (Inv-resp-□∧ {R} R∧P⊢Q R∧Q⊢P) ✓a =
    (λ □R∧InvPa → ⸨⸩-⇒ᴮ {R} $ □R∧InvPa 0₂ , □R∧InvPa 1₂) ›
    Invᵒ-resp-□ᵒ×ᵒ (R∧P⊢Q .!) (R∧Q⊢P .!) ✓a

  -- OInv-mono :  P˂ .!  ⊢[< ∞ ]  Q˂ .!  →   OInv nm Q˂  ⊢[ ∞ ]  OInv nm P˂

  ⊢-sem (OInv-mono P⊢Q) _ =  OInvᵒ-mono $ P⊢Q .!

  -- OInv-eatˡ :  {{Basic Q}} →
  --   Q  ∗  OInv nm P˂  ⊢[ ∞ ]  OInv nm (¡ (Q -∗ P˂ .!))

  ⊢-sem (OInv-eatˡ {Q}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {Q}) › OInvᵒ-eatˡ

  -- []ᴸ⟨⟩-merge :  [ α ]ᴸ⟨ p ⟩  ∗  [ α ]ᴸ⟨ q ⟩  ⊢[ ∞ ]  [ α ]ᴸ⟨ p +ᴿ⁺ q ⟩

  ⊢-sem []ᴸ⟨⟩-merge _ =  []ᴸ⟨⟩ᵒ-merge

  -- []ᴸ⟨⟩-split :  [ α ]ᴸ⟨ p +ᴿ⁺ q ⟩  ⊢[ ∞ ]  [ α ]ᴸ⟨ p ⟩  ∗  [ α ]ᴸ⟨ q ⟩

  ⊢-sem []ᴸ⟨⟩-split _ =  []ᴸ⟨⟩ᵒ-split

  -- []ᴸ⟨⟩-≤1 :  [ α ]ᴸ⟨ p ⟩  ⊢[ ∞ ]  ⌜ p ≤1ᴿ⁺ ⌝

  ⊢-sem []ᴸ⟨⟩-≤1 p≤1 =  []ᴸ⟨⟩ᵒ-≤1 p≤1 › (_, absurd)

  -- †ᴸ-⇒□ :  †ᴸ α  ⊢[ ∞ ]  □ †ᴸ α

  ⊢-sem †ᴸ-⇒□ _ =  †ᴸᵒ-⇒□ᵒ

  -- []ᴸ⟨⟩-†ᴸ-no :  [ α ]ᴸ⟨ p ⟩  ∗  †ᴸ α  ⊢[ ∞ ]  ⊥'

  ⊢-sem []ᴸ⟨⟩-†ᴸ-no ✓∙ =  []ᴸ⟨⟩ᵒ-†ᴸᵒ-no ✓∙ › λ ()

  -- []ᴸ-alloc :  ⊤'  ⊢[ ∞ ] ⤇  ∃ α , [ α ]ᴸ

  ⊢-sem []ᴸ-alloc _ _ =  []ᴸᵒ-alloc
