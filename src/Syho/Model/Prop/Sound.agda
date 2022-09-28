--------------------------------------------------------------------------------
-- Prove the semantic soundness of the pure sequent
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Sound where

open import Base.Func using (_$_; _›_; id)
open import Base.Few using (0₂; 1₂; binary; absurd)
open import Base.Size using (Size; ∞; !)
open import Base.Prod using (_,_; π₀; π₁; ∑-case)
open import Syho.Logic.Prop using (Prop')
open import Syho.Logic.Core using (_⊢[_]_; ⊢-refl; _»_; ∀-intro; ∃-elim; ∀-elim;
  ∃-intro; choice; →-intro; →-elim; ⊤∗-elim; ⊤∗-intro; ∗-comm; ∗-assocˡ;
  ∗-monoˡ; -∗-intro; -∗-elim; ⤇-mono; ⤇-intro; ⤇-join; ⤇-eatˡ; ⤇-⌜⌝∧-out; □-mono;
  □-elim; □-dup; □ˡ-∧⇒∗; □-∀-in; □-∃-out)
open import Syho.Logic.Ind using (○-mono; ○-eatˡ; ↪⇛-ṡ; ↪⇛-eatˡ⁻ˡᵘ; ↪⇛-eatˡ⁻ʳ;
  ↪⇛-monoʳᵘ; ↪⇛-frameˡ; ○⇒↪⇛; ↪⟨⟩ᴾ-eatˡ⁻ˡᵘ; ↪⟨⟩ᴾ-eatˡ⁻ʳ; ↪⟨⟩ᴾ-monoʳᵘ;
  ↪⟨⟩ᴾ-frameˡ; ○⇒↪⟨⟩ᴾ; ↪⟨⟩ᵀ-ṡ; ↪⟨⟩ᵀ-eatˡ⁻ˡᵘ; ↪⟨⟩ᵀ-eatˡ⁻ʳ; ↪⟨⟩ᵀ-monoʳᵘ;
  ↪⟨⟩ᵀ-frameˡ; ○⇒↪⟨⟩ᵀ)
open import Syho.Logic.Mem using (↦⟨⟩-agree; ↦⟨⟩-≤1; ↦⟨⟩-merge; ↦⟨⟩-split)
open import Syho.Model.Prop.Base using (_⊨✓_; →ᵒ-intro; →ᵒ-elim; ∗ᵒ-monoˡ;
  ∗ᵒ-mono✓ˡ; ?∗ᵒ-intro; ∗ᵒ-elimʳ; ∗ᵒ-comm; ∗ᵒ-assocˡ; -∗ᵒ-intro; -∗ᵒ-elim;
  ⤇ᵒ-mono✓; ⤇ᵒ-intro; ⤇ᵒ-join; ⤇ᵒ-eatˡ; ⤇ᵒ-⌜⌝ᵒ×-out; □ᵒ-mono✓; □ᵒ-elim; □ᵒ-dup;
  □ᵒˡ-×ᵒ⇒∗ᵒ)
open import Syho.Model.Prop.Mem using (↦⟨⟩ᵒ-agree; ↦⟨⟩ᵒ-≤1; ↦⟨⟩ᵒ-merge;
  ↦⟨⟩ᵒ-split)
open import Syho.Model.Prop.Ind using (○ᵒ_; _↪[_]⇛ᵒ_; _↪⟨_⟩ᴾᵒ_; _↪⟨_⟩ᵀ[_]ᵒ_;
  ○ᵒ-mono; ○ᵒ-eatˡ; ↪⇛ᵒ-ṡ; ↪⇛ᵒ-eatˡ⁻ˡᵘ; ↪⇛ᵒ-eatˡ⁻ʳ; ↪⇛ᵒ-monoʳᵘ; ↪⇛ᵒ-frameˡ;
  ○ᵒ⇒↪⇛ᵒ; ↪⟨⟩ᴾᵒ-eatˡ⁻ˡᵘ; ↪⟨⟩ᴾᵒ-eatˡ⁻ʳ; ↪⟨⟩ᴾᵒ-monoʳᵘ; ↪⟨⟩ᴾᵒ-frameˡ; ○ᵒ⇒↪⟨⟩ᴾᵒ;
  ↪⟨⟩ᵀᵒ-ṡ; ↪⟨⟩ᵀᵒ-eatˡ⁻ˡᵘ; ↪⟨⟩ᵀᵒ-eatˡ⁻ʳ; ↪⟨⟩ᵀᵒ-monoʳᵘ; ↪⟨⟩ᵀᵒ-frameˡ; ○ᵒ⇒↪⟨⟩ᵀᵒ)
open import Syho.Model.Prop.Interp using (⸨_⸩; ⸨⸩-⇒ᴮ; ⸨⸩-Mono)

private variable
  P Q R S T :  Prop' ∞

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

  ⊢-sem choice _ ∀x∃₁yPxy .π₀ x =  ∀x∃₁yPxy x .π₀
  ⊢-sem choice _ ∀x∃₁yPxy .π₁ x =  ∀x∃₁yPxy x .π₁

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

  -- ⤇-eatˡ :  P ∗ ⤇ Q ⊢[ ∞ ] ⤇ (P ∗ Q)

  ⊢-sem ⤇-eatˡ _ =  ⤇ᵒ-eatˡ

  -- ⤇-⌜⌝∧-out :  ⤇ (⌜ X ⌝∧ P) ⊢[ ι ] ⌜ X ⌝∧ ⤇ P

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

  -- ↪⇛-eatˡ⁻ˡᵘ :  {{Basic R}} →  R ∗ P'˂ .! ⊢[< ∞ ][ i ]⇛ P˂ .! →
  --               R ∗ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ∞ ]  P'˂ ↪[ i ]⇛ Q˂

  ⊢-sem (↪⇛-eatˡ⁻ˡᵘ {R} R∗P'⊢⇛P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⇛ᵒ-eatˡ⁻ˡᵘ $ R∗P'⊢⇛P .!

  -- ↪⇛-eatˡ⁻ʳ :  {{Basic R}} →
  --   R ∗ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ∞ ]  P˂ ↪[ i ]⇛ ¡ (R ∗ Q˂ .!)

  ⊢-sem (↪⇛-eatˡ⁻ʳ {R}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⇛ᵒ-eatˡ⁻ʳ

  -- ↪⇛-monoʳᵘ :  Q˂ .! ⊢[< ∞ ][ i ]⇛ Q'˂ .! →
  --              P˂ ↪[ i ]⇛ Q˂  ⊢[ ∞ ]  P˂ ↪[ i ]⇛ Q'˂

  ⊢-sem (↪⇛-monoʳᵘ Q⊢⇛Q') _ =  ↪⇛ᵒ-monoʳᵘ $ Q⊢⇛Q' .!

  -- ↪⇛-frameˡ :  P˂ ↪[ i ]⇛ Q˂  ⊢[ ∞ ]  ¡ (R ∗ P˂ .!) ↪[ i ]⇛ ¡ (R ∗ Q˂ .!)

  ⊢-sem ↪⇛-frameˡ _ =  ↪⇛ᵒ-frameˡ

  -- ○⇒↪⇛ :  P˂ .! ∗ R˂ .! ⊢[< ∞ ][ i ]⇛ Q˂ .! →  ○ R˂  ⊢[ ∞ ]  P˂ ↪[ i ]⇛ Q˂

  ⊢-sem (○⇒↪⇛ P∗R⊢⇛Q) _ =  ○ᵒ⇒↪⇛ᵒ $ P∗R⊢⇛Q .!

  -- ↪⟨⟩ᴾ-eatˡ⁻ˡᵘ :  {{Basic R}} →  R ∗ P'˂ .! ⊢[< ∞ ][ i ]⇛ P˂ .! →
  --                 R ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂˙)  ⊢[ ∞ ]  P'˂ ↪⟨ e ⟩ᴾ Q˂˙

  ⊢-sem (↪⟨⟩ᴾ-eatˡ⁻ˡᵘ {R} R∗P'⊢⇛P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⟨⟩ᴾᵒ-eatˡ⁻ˡᵘ $ R∗P'⊢⇛P .!

  -- ↪⟨⟩ᴾ-eatˡ⁻ʳ :  {{Basic R}} →
  --   R ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂˙)  ⊢[ ∞ ]  P˂ ↪⟨ e ⟩ᴾ λ v → ¡ (R ∗ Q˂˙ v .!)

  ⊢-sem (↪⟨⟩ᴾ-eatˡ⁻ʳ {R}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⟨⟩ᴾᵒ-eatˡ⁻ʳ

  -- ↪⟨⟩ᴾ-monoʳᵘ :  (∀ v →  Q˂˙ v .! ⊢[< ∞ ][ i ]⇛ Q'˂˙ v .!) →
  --                P˂ ↪⟨ e ⟩ᴾ Q˂˙  ⊢[ ∞ ]  P˂ ↪⟨ e ⟩ᴾ Q'˂˙

  ⊢-sem (↪⟨⟩ᴾ-monoʳᵘ ∀vQ⊢⇛Q') _ =  ↪⟨⟩ᴾᵒ-monoʳᵘ λ v → ∀vQ⊢⇛Q' v .!

  -- ↪⟨⟩ᴾ-frameˡ :  P˂ ↪⟨ e ⟩ᴾ Q˂˙  ⊢[ ∞ ]
  --                  ¡ (R ∗ P˂ .!) ↪⟨ e ⟩ᴾ λ v → ¡ (R ∗ Q˂˙ v .!)

  ⊢-sem ↪⟨⟩ᴾ-frameˡ _ =  ↪⟨⟩ᴾᵒ-frameˡ

  -- ○⇒↪⟨⟩ᴾ :  P˂ .! ∗ R˂ .! ⊢[< ∞ ]⟨ e ⟩ᴾ (λ v → Q˂˙ v .!) →
  --           ○ R˂  ⊢[ ∞ ]  P˂ ↪⟨ e ⟩ᴾ Q˂˙

  ⊢-sem (○⇒↪⟨⟩ᴾ P∗R⊢⟨e⟩Q) _ =  ○ᵒ⇒↪⟨⟩ᴾᵒ $ P∗R⊢⟨e⟩Q .!

  -- ↪⟨⟩ᵀ-ṡ :  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ∞ ]  P˂ ↪⟨ e ⟩ᵀ[ ṡ i ] Q˂˙

  ⊢-sem ↪⟨⟩ᵀ-ṡ _ =  ↪⟨⟩ᵀᵒ-ṡ

  -- ↪⟨⟩ᵀ-eatˡ⁻ˡᵘ :  {{Basic R}} →  R ∗ P'˂ .! ⊢[< ∞ ][ j ]⇛ P˂ .! →
  --                 R ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙)  ⊢[ ∞ ]  P'˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙

  ⊢-sem (↪⟨⟩ᵀ-eatˡ⁻ˡᵘ {R} R∗P'⊢⇛P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⟨⟩ᵀᵒ-eatˡ⁻ˡᵘ $ R∗P'⊢⇛P .!

  -- ↪⟨⟩ᵀ-eatˡ⁻ʳ :  {{Basic R}} →
  --   R ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙)  ⊢[ ∞ ]  P˂ ↪⟨ e ⟩ᵀ[ i ] λ v → ¡ (R ∗ Q˂˙ v .!)

  ⊢-sem (↪⟨⟩ᵀ-eatˡ⁻ʳ {R}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⟨⟩ᵀᵒ-eatˡ⁻ʳ

  -- ↪⟨⟩ᵀ-monoʳᵘ :  (∀ v →  Q˂˙ v .! ⊢[< ∞ ][ j ]⇛ Q'˂˙ v .!) →
  --                P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ∞ ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q'˂˙

  ⊢-sem (↪⟨⟩ᵀ-monoʳᵘ ∀vQ⊢⇛Q') _ =  ↪⟨⟩ᵀᵒ-monoʳᵘ λ v → ∀vQ⊢⇛Q' v .!

  -- ↪⟨⟩ᵀ-frameˡ :  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ∞ ]
  --                  ¡ (R ∗ P˂ .!) ↪⟨ e ⟩ᵀ[ i ] λ v → ¡ (R ∗ Q˂˙ v .!)

  ⊢-sem ↪⟨⟩ᵀ-frameˡ _ =  ↪⟨⟩ᵀᵒ-frameˡ

  -- ○⇒↪⟨⟩ᵀ :  P˂ .! ∗ R˂ .! ⊢[< ∞ ]⟨ e ⟩ᵀ[ i ] (λ v → Q˂˙ v .!) →
  --           ○ R˂  ⊢[ ∞ ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙

  ⊢-sem (○⇒↪⟨⟩ᵀ P∗R⊢⟨e⟩Q) _ =  ○ᵒ⇒↪⟨⟩ᵀᵒ $ P∗R⊢⟨e⟩Q .!

  -- ↦⟨⟩-agree :  θ ↦⟨ p ⟩ ᵗu  ∗  θ ↦⟨ q ⟩ ᵗv  ⊢[ ∞ ]  ⌜ ᵗu ≡ ᵗv ⌝

  ⊢-sem ↦⟨⟩-agree ✓a =  ↦⟨⟩ᵒ-agree ✓a › (_, absurd)

  -- ↦⟨⟩-≤1 :  θ ↦⟨ p ⟩ ᵗv  ⊢[ ∞ ]  ⌜ p ≤1ᴿ⁺ ⌝

  ⊢-sem ↦⟨⟩-≤1 ✓a =  ↦⟨⟩ᵒ-≤1 ✓a › (_, absurd)

  -- ↦⟨⟩-merge :  θ ↦⟨ p ⟩ ᵗv  ∗  θ ↦⟨ q ⟩ ᵗv  ⊢[ ∞ ]  θ ↦⟨ p +ᴿ⁺ q ⟩ ᵗv

  ⊢-sem ↦⟨⟩-merge _ =  ↦⟨⟩ᵒ-merge

  -- ↦⟨⟩-split :  θ ↦⟨ p +ᴿ⁺ q ⟩ ᵗv  ⊢[ ∞ ]  θ ↦⟨ p ⟩ ᵗv  ∗  θ ↦⟨ q ⟩ ᵗv

  ⊢-sem ↦⟨⟩-split _ =  ↦⟨⟩ᵒ-split
