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
  ∃-intro; choice; →-intro; →-elim; ⊤∗-elim; ⊤∗-intro; ∗-comm; ∗-assocˡ;
  ∗-monoˡ; -∗-intro; -∗-elim; ⤇-mono; ⤇-intro; ⤇-join; ⤇-eatˡ; ⤇-⌜⌝∧-out; □-mono;
  □-elim; □-dup; □ˡ-∧⇒∗; □-∀-in; □-∃-out)
open import Syho.Logic.Ind using (○-mono; ○-eatˡ; ↪⇛-ṡ; ↪⇛-eatˡ⁻ˡᵘ; ↪⇛-eatˡ⁻ʳ;
  ↪⇛-monoʳᵘ; ↪⇛-frameˡ; ○⇒↪⇛;  ↪ᵃ⟨⟩-ṡ; ↪ᵃ⟨⟩-eatˡ⁻ˡᵘ; ↪ᵃ⟨⟩-eatˡ⁻ʳ; ↪ᵃ⟨⟩-monoʳᵘ;
  ↪ᵃ⟨⟩-frameˡ; ○⇒↪ᵃ⟨⟩; ↪⟨⟩ᵀ⇒↪⟨⟩ᴾ; ↪⟨⟩ᵀ-ṡ; ↪⟨⟩-eatˡ⁻ˡᵘ; ↪⟨⟩-eatˡ⁻ʳ; ↪⟨⟩-monoʳᵘ;
  ↪⟨⟩-frameˡ; ○⇒↪⟨⟩)
open import Syho.Logic.Inv using ([]ᴺ-resp; []ᴺ-merge; []ᴺ-split; []ᴺ-✔; Inv-⇒□;
  Inv-resp-∧; OInv-mono; OInv-eatˡ)
open import Syho.Logic.Mem using (↦⟨⟩-agree; ↦⟨⟩-≤1; ↦⟨⟩-merge; ↦⟨⟩-split)
open import Syho.Model.Prop.Base using (_⊨✓_; →ᵒ-intro; →ᵒ-elim; ∗ᵒ-monoˡ;
  ∗ᵒ-mono✓ˡ; ?∗ᵒ-intro; ∗ᵒ-elimʳ; ∗ᵒ-comm; ∗ᵒ-assocˡ; -∗ᵒ-intro; -∗ᵒ-elim;
  ⤇ᵒ-mono✓; ⤇ᵒ-intro; ⤇ᵒ-join; ⤇ᵒ-eatˡ; ⤇ᵒ-⌜⌝ᵒ×-out; □ᵒ-mono✓; □ᵒ-elim; □ᵒ-dup;
  □ᵒˡ-×ᵒ⇒∗ᵒ; ∗ᵒ⇒∗ᵒ' {- for now -})
open import Syho.Model.Prop.Mem using (↦⟨⟩ᵒ-agree; ↦⟨⟩ᵒ-≤1; ↦⟨⟩ᵒ-merge;
  ↦⟨⟩ᵒ-split)
open import Syho.Model.Prop.Names using ([]ᴺᵒ-resp; []ᴺᵒ-merge; []ᴺᵒ-split;
  []ᴺᵒ-✔)
open import Syho.Model.Prop.Ind using (○ᵒ-mono; ○ᵒ-eatˡ; ↪⇛ᵒ-ṡ; ↪⇛ᵒ-eatˡ⁻ˡᵘ;
  ↪⇛ᵒ-eatˡ⁻ʳ; ↪⇛ᵒ-monoʳᵘ; ↪⇛ᵒ-frameˡ; ○ᵒ⇒↪⇛ᵒ; ↪ᵃ⟨⟩ᵒ-ṡ; ↪ᵃ⟨⟩ᵒ-eatˡ⁻ˡᵘ;
  ↪ᵃ⟨⟩ᵒ-eatˡ⁻ʳ; ↪ᵃ⟨⟩ᵒ-monoʳᵘ; ↪ᵃ⟨⟩ᵒ-frameˡ; ○ᵒ⇒↪ᵃ⟨⟩ᵒ; ↪⟨⟩ᵀᵒ⇒↪⟨⟩ᴾᵒ; ↪⟨⟩ᵀᵒ-ṡ;
  ↪⟨⟩ᵒ-eatˡ⁻ˡᵘ; ↪⟨⟩ᵒ-eatˡ⁻ʳ; ↪⟨⟩ᵒ-monoʳᵘ; ↪⟨⟩ᵒ-frameˡ; ○ᵒ⇒↪⟨⟩ᵒ)
open import Syho.Model.Prop.Interp using (⸨_⸩; ⸨⸩-⇒ᴮ; ⸨⸩-Mono)

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

  -- ⊤∗-elim :  ⊤' ∗ P ⊢[ ∞ ] P

  ⊢-sem (⊤∗-elim {P}) _ =  ∗ᵒ-elimʳ $ ⸨⸩-Mono {P}

  -- ⊤∗-intro :  P ⊢[ ∞ ] ⊤' ∗ P

  ⊢-sem ⊤∗-intro _ =  ?∗ᵒ-intro absurd

  -- ∗-comm :  P ∗ Q ⊢[ ∞ ] Q ∗ P

  ⊢-sem ∗-comm _ =  ∗ᵒ-comm

  -- ∗-assocˡ :  (P ∗ Q) ∗ R ⊢[ ∞ ] P ∗ (Q ∗ R)

  ⊢-sem ∗-assocˡ _ =  ∗ᵒ-assocˡ

  -- ∗-monoˡ :  P ⊢[ ∞ ] Q →  P ∗ R ⊢[ ∞ ] Q ∗ R

  ⊢-sem (∗-monoˡ P⊢Q) =  ∗ᵒ-mono✓ˡ (⊢-sem P⊢Q)

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

  -- ○-mono :  P˂ .! ⊢[< ∞ ] Q˂ .! →  ○ P˂ ⊢[ ∞ ] ○ Q˂

  ⊢-sem (○-mono P⊢Q) _ =  ○ᵒ-mono $ P⊢Q .!

  -- ○-eatˡ :  {{Basic Q}} →  Q ∗ ○ P˂ ⊢[ ∞ ] ○ ¡ (Q ∗ P˂ .!)

  ⊢-sem (○-eatˡ {Q}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {Q}) › ○ᵒ-eatˡ

  -- ↪⇛-ṡ :  P˂ ↪[ i ]⇛ Q˂  ⊢[ ∞ ]  P˂ ↪[ ṡ i ]⇛ Q˂

  ⊢-sem ↪⇛-ṡ _ =  ↪⇛ᵒ-ṡ

  -- ↪⇛-eatˡ⁻ˡᵘ :  {{Basic R}} →   R  ∗  P'˂ .!  ⊢[< ι ][ i ]⇛  P˂ .! →
  --               R  ∗  (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ∞ ]  P'˂ ↪[ i ]⇛ Q˂

  ⊢-sem (↪⇛-eatˡ⁻ˡᵘ {R} R∗P'⊢⇛P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⇛ᵒ-eatˡ⁻ˡᵘ $ R∗P'⊢⇛P .!

  -- ↪⇛-eatˡ⁻ʳ :  {{Basic R}} →
  --   R  ∗  (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ∞ ]  P˂ ↪[ i ]⇛ ¡ (R ∗ Q˂ .!)

  ⊢-sem (↪⇛-eatˡ⁻ʳ {R}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⇛ᵒ-eatˡ⁻ʳ

  -- ↪⇛-monoʳᵘ :  Q˂ .!  ⊢[< ∞ ][ i ]⇛  Q'˂ .! →
  --              P˂ ↪[ i ]⇛ Q˂  ⊢[ ∞ ]  P˂ ↪[ i ]⇛ Q'˂

  ⊢-sem (↪⇛-monoʳᵘ Q⊢⇛Q') _ =  ↪⇛ᵒ-monoʳᵘ $ Q⊢⇛Q' .!

  -- ↪⇛-frameˡ :  P˂ ↪[ i ]⇛ Q˂  ⊢[ ∞ ]  ¡ (R ∗ P˂ .!) ↪[ i ]⇛ ¡ (R ∗ Q˂ .!)

  ⊢-sem ↪⇛-frameˡ _ =  ↪⇛ᵒ-frameˡ

  -- ○⇒↪⇛ :  P˂ .!  ∗  R˂ .! ⊢[< ι ][ i ]⇛  Q˂ .!  →
  --         ○ R˂  ⊢[ ι ]  P˂ ↪[ i ]⇛ Q˂

  ⊢-sem (○⇒↪⇛ P∗R⊢⇛Q) _ =  ○ᵒ⇒↪⇛ᵒ $ P∗R⊢⇛Q .!

  -- ↪ᵃ⟨⟩-ṡ :  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]  P˂ ↪[ ṡ i ]ᵃ⟨ red ⟩ Q˂˙

  ⊢-sem ↪ᵃ⟨⟩-ṡ _ =  ↪ᵃ⟨⟩ᵒ-ṡ

  -- ↪ᵃ⟨⟩-eatˡ⁻ˡᵘ :  {{Basic R}} →  R ∗ P'˂ .! ⊢[< ι ][ j ]⇛ P˂ .! →
  --                 R ∗ (P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙)  ⊢[ ι ]  P'˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙

  ⊢-sem (↪ᵃ⟨⟩-eatˡ⁻ˡᵘ {R} R∗P'⊢⇛P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪ᵃ⟨⟩ᵒ-eatˡ⁻ˡᵘ $ R∗P'⊢⇛P .!

  -- ↪ᵃ⟨⟩-eatˡ⁻ˡᵘ :  {{Basic R}} →  R ∗ P'˂ .! ⊢[< ι ][ j ]⇛ P˂ .! →
  --                 R ∗ (P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙)  ⊢[ ι ]  P'˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙

  ⊢-sem (↪ᵃ⟨⟩-eatˡ⁻ʳ {R}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪ᵃ⟨⟩ᵒ-eatˡ⁻ʳ

  -- ↪ᵃ⟨⟩-monoʳᵘ :  (∀ v →  Q˂˙ v .!  ⊢[< ι ][ j ]⇛  Q'˂˙ v .!)  →
  --                P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q'˂˙

  ⊢-sem (↪ᵃ⟨⟩-monoʳᵘ ∀vQ⊢⇛Q') _ =  ↪ᵃ⟨⟩ᵒ-monoʳᵘ λ v → ∀vQ⊢⇛Q' v .!

  -- ↪ᵃ⟨⟩-frameˡ :  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]
  --                  ¡ (R ∗ P˂ .!) ↪[ i ]ᵃ⟨ red ⟩ λ v → ¡ (R ∗ Q˂˙ v .!)

  ⊢-sem ↪ᵃ⟨⟩-frameˡ _ =  ↪ᵃ⟨⟩ᵒ-frameˡ

  -- ○⇒↪ᵃ⟨⟩ :  (P˂ .!  ∗  R˂ .! ⊢[< ι ][ i ]ᵃ⟨ red ⟩ λ v →  Q˂˙ v .!)  →
  --           ○ R˂  ⊢[ ι ]  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙

  ⊢-sem (○⇒↪ᵃ⟨⟩ P∗R⊢⟨red⟩Q) _ =  ○ᵒ⇒↪ᵃ⟨⟩ᵒ $ P∗R⊢⟨red⟩Q .!

  -- ↪⟨⟩ᵀ⇒↪⟨⟩ᴾ :  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q˂˙

  ⊢-sem ↪⟨⟩ᵀ⇒↪⟨⟩ᴾ _ =  ↪⟨⟩ᵀᵒ⇒↪⟨⟩ᴾᵒ

  -- ↪⟨⟩ᵀ-ṡ :  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ∞ ]  P˂ ↪⟨ e ⟩ᵀ[ ṡ i ] Q˂˙

  ⊢-sem ↪⟨⟩ᵀ-ṡ _ =  ↪⟨⟩ᵀᵒ-ṡ

  -- ↪⟨⟩-eatˡ⁻ˡᵘ :  {{Basic R}} →
  --   (R  ∗  P'˂ .!)  ∗  [ ⊤ᶻ ]ᴺ  ⊢[< ι ][ i ]⇛  P˂ .!  ∗  [ ⊤ᶻ ]ᴺ  →
  --   R  ∗  (P˂ ↪⟨ e ⟩[ κ ] Q˂˙)  ⊢[ ι ]  P'˂ ↪⟨ e ⟩[ κ ] Q˂˙

  ⊢-sem (↪⟨⟩-eatˡ⁻ˡᵘ {R} R∗P'⊢⇛P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⟨⟩ᵒ-eatˡ⁻ˡᵘ $ R∗P'⊢⇛P .!

  -- ↪⟨⟩-eatˡ⁻ʳ :  {{Basic R}} →
  --   R  ∗  (P˂ ↪⟨ e ⟩[ κ ] Q˂˙)  ⊢[ ∞ ]  P˂ ↪⟨ e ⟩[ κ ] λ v → ¡ (R ∗ Q˂˙ v .!)

  ⊢-sem (↪⟨⟩-eatˡ⁻ʳ {R}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⟨⟩ᵒ-eatˡ⁻ʳ

  -- ↪⟨⟩-monoʳᵘ :
  --   (∀ v →  Q˂˙ v .!  ∗  [ ⊤ᶻ ]ᴺ  ⊢[< ι ][ i ]⇛  Q'˂˙ v .!  ∗  [ ⊤ᶻ ]ᴺ)  →
  --   P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩[ κ ] Q'˂˙

  ⊢-sem (↪⟨⟩-monoʳᵘ ∀vQ⊢⇛Q') _ =  ↪⟨⟩ᵒ-monoʳᵘ λ v → ∀vQ⊢⇛Q' v .!

  -- ↪⟨⟩-frameˡ :  P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ∞ ]
  --                 ¡ (R ∗ P˂ .!) ↪⟨ e ⟩[ κ ] λ v → ¡ (R ∗ Q˂˙ v .!)

  ⊢-sem ↪⟨⟩-frameˡ _ =  ↪⟨⟩ᵒ-frameˡ

  -- ○⇒↪⟨⟩ :  (P˂ .!  ∗  R˂ .! ⊢[< ι ]⟨ e ⟩[ κ ] λ v →  Q˂˙ v .!)  →
  --          ○ R˂  ⊢[ ∞ ]  P˂ ↪⟨ e ⟩[ κ ] Q˂˙

  ⊢-sem (○⇒↪⟨⟩ P∗R⊢⟨e⟩Q) _ =  ○ᵒ⇒↪⟨⟩ᵒ $ P∗R⊢⟨e⟩Q .!

  -- []ᴺ-resp :  Nm ≡˙ Nm' →  [ Nm ]ᴺ ⊢[ ι ] [ Nm' ]ᴺ

  ⊢-sem ([]ᴺ-resp Nm≡Nm') _ =  []ᴺᵒ-resp Nm≡Nm'

  -- []ᴺ-merge :  [ Nm ]ᴺ  ∗  [ Nm' ]ᴺ  ⊢[ ι ]  [ Nm ⊎ᶻ Nm' ]ᴺ

  ⊢-sem []ᴺ-merge _ =  []ᴺᵒ-merge

  -- []ᴺ-split :  [ Nm ⊎ᶻ Nm' ]ᴺ  ⊢[ ι ]  [ Nm ]ᴺ  ∗  [ Nm' ]ᴺ

  ⊢-sem []ᴺ-split _ =  []ᴺᵒ-split

  -- []ᴺ-✔ :  [ Nm ]ᴺ  ⊢[ ι ]  ⌜ ✔ᶻ Nm ⌝

  ⊢-sem []ᴺ-✔ ✓∙ =  []ᴺᵒ-✔ ✓∙ › (_, absurd)

  -- Inv-⇒□ :  Inv nm P˂  ⊢[ ι ]  □ Inv nm P˂

  ⊢-sem Inv-⇒□ _ ()

  -- Inv-resp-∧ :  {{Pers R}} →  {{Basic R}} →
  --   R  ∧  P˂ .!  ⊢[< ι ]  Q˂ .!  →   R  ∧  Q˂ .!  ⊢[< ι ]  P˂ .!  →
  --   R  ∧  Inv nm P˂  ⊢[ ι ]  Inv nm Q˂

  ⊢-sem (Inv-resp-∧ R∧P⊢Q R∧Q⊢P) _ =  (_$ 1₂) › absurd

  -- OInv-mono :  P˂ .!  ⊢[< ι ]  Q˂ .!  →   OInv nm P˂  ⊢[ ι ]  OInv nm Q˂

  ⊢-sem (OInv-mono P⊢Q) _ ()

  -- OInv-eatˡ :  {{Basic Q}} →
  --   Q  ∗  OInv nm P˂  ⊢[ ι ]  OInv nm (¡ (Q -∗ P˂ .!))

  ⊢-sem OInv-eatˡ _ =  ∗ᵒ⇒∗ᵒ' › λ ()

  -- ↦⟨⟩-agree :  θ ↦⟨ p ⟩ ᵗu  ∗  θ ↦⟨ q ⟩ ᵗv  ⊢[ ∞ ]  ⌜ ᵗu ≡ ᵗv ⌝

  ⊢-sem ↦⟨⟩-agree ✓a =  ↦⟨⟩ᵒ-agree ✓a › (_, absurd)

  -- ↦⟨⟩-≤1 :  θ ↦⟨ p ⟩ ᵗv  ⊢[ ∞ ]  ⌜ p ≤1ᴿ⁺ ⌝

  ⊢-sem ↦⟨⟩-≤1 ✓a =  ↦⟨⟩ᵒ-≤1 ✓a › (_, absurd)

  -- ↦⟨⟩-merge :  θ ↦⟨ p ⟩ ᵗv  ∗  θ ↦⟨ q ⟩ ᵗv  ⊢[ ∞ ]  θ ↦⟨ p +ᴿ⁺ q ⟩ ᵗv

  ⊢-sem ↦⟨⟩-merge _ =  ↦⟨⟩ᵒ-merge

  -- ↦⟨⟩-split :  θ ↦⟨ p +ᴿ⁺ q ⟩ ᵗv  ⊢[ ∞ ]  θ ↦⟨ p ⟩ ᵗv  ∗  θ ↦⟨ q ⟩ ᵗv

  ⊢-sem ↦⟨⟩-split _ =  ↦⟨⟩ᵒ-split
