--------------------------------------------------------------------------------
-- Fancy update on the indirection modality and the precursors
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Symp.Model.Fupd.Ind where

open import Base.Level using (Level; _⊔ᴸ_; 1ᴸ)
open import Base.Size using (∞)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Eq using (_≡_; refl; _≡˙_; _◇˙_)
open import Base.Dec using (upd˙²)
open import Base.Option using (¿_)
open import Base.Prod using (_×_; _,_; -,_; -ᴵ,_; ∑-case; ∑ᴵ-case)
open import Base.Sum using (ĩ₀_; ĩ₁_; ⨿-case)
open import Base.Nat using (ℕ)
open import Symp.Lang.Expr using (Type; Expr∞)
open import Symp.Lang.Ktxred using (Redex)
open import Symp.Logic.Prop using (WpKind; Prop∞; _∗_)
open import Symp.Logic.Fupd using (_⊢[_][_]⇛_)
open import Symp.Logic.Hor using (_⊢[_][_]ᵃ⟨_⟩_; _⊢[_]⟨_⟩[_]_; _⊢[_][_]⟨_⟩∞)
open import Symp.Model.ERA.Ind using (Envᴵⁿᵈˣ; Envᴵⁿᵈᵖ; Envᴵⁿᵈ)
open import Symp.Model.ERA.Glob using (Envᴵⁿᴳ; jᴵⁿᵈˣ; jᴵⁿᵈᵖ; ∅ᴵⁿᴳ)
open import Symp.Model.Prop.Base using (Propᵒ; _⊨_; ⊨_; ∃ᵒ-syntax; ⌜_⌝ᵒ×_; _∗ᵒ_;
  _-∗ᵒ_; □ᵒ_; ∗ᵒ-mono; ∗ᵒ-mono✓ˡ; ∗ᵒ-monoˡ; ∗ᵒ-mono✓ʳ; ∗ᵒ-monoʳ; ∗ᵒ-assocˡ;
  ∗ᵒ-assocʳ; ∗ᵒ-elimˡ; ∗ᵒ-elimʳ; ?∗ᵒ-intro; ∗ᵒ?-intro; -∗ᵒ-monoˡ; -∗ᵒ-applyˡ;
  ⤇ᴱ⟨⟩-mono; ⤇ᴱ⟨⟩-mono✓; ⤇ᴱ⟨⟩-param; ⤇ᴱ⟨⟩-eatʳ; □ᵒ-Mono; □ᵒ-elim; dup-□ᵒ;
  □ᵒ-∗ᵒ-in)
open import Symp.Model.Prop.Smry using (Smry; Smry-Mono; Smry-0; Smry-add-š;
  Smry-rem-<)
open import Symp.Model.Prop.Ind using (Indˣ; Indᵖ; Ind; ○ᵒ_; _↪[_]⇛ᴹ_;
  _↪[_]ᵃ⟨_⟩ᵒ_; _↪⟨_⟩[_]ᵒ_; _↪[_]⟨_⟩∞ᵒ; Indᵖ-Mono; Indˣ-new'; Indˣ-use';
  □ᵒIndᵖ-new'; Indᵖ-use'; Ind⇒○ᵒ)
open import Symp.Model.Prop.Interp using (⸨_⸩; ⸨⸩-Mono; ⸨⸩-ᴮ⇒)
open import Symp.Model.Prop.Sound using (⊢-sem)
open import Symp.Model.Fupd.Base using ([_]⇛ᵍ_; [_]⇛ᵍ¹_; ⇛ᵍ-mono✓; ⇛ᵍ-mono;
  ⇛ᵍ¹-make; ⇛ᵍ¹-intro; ⇛ᵍ-join2; ⇛ᵍ-eatˡ)

private variable
  ł :  Level
  i :  ℕ
  P Q :  Prop∞
  X :  Set₀
  Q˙ :  X →  Prop∞
  Pᵒ :  Propᵒ ł
  κ :  WpKind
  T :  Type
  red :  Redex T
  e :  Expr∞ T

--------------------------------------------------------------------------------
-- On Indˣᴱᴿᴬ

-- Invᴵⁿᵈˣ :  Invariant for Indˣᴱᴿᴬ

Invᴵⁿᵈˣ :  Envᴵⁿᵈˣ →  Propᵒ 1ᴸ
Invᴵⁿᵈˣ (P˙ , n) =  Smry (λ _ → ⸨_⸩) P˙ n

-- ⇛ᴵⁿᵈˣ :  Fancy update on Indˣᴱᴿᴬ

infix 3 ⇛ᴵⁿᵈˣ_
⇛ᴵⁿᵈˣ_ :  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⇛ᴵⁿᵈˣ Pᵒ =  [ jᴵⁿᵈˣ , Invᴵⁿᵈˣ ]⇛ᵍ¹ Pᵒ

abstract

  -- Get Invᴵⁿᵈˣ (∅ᴵⁿᴳ jᴵⁿᵈˣ) for free

  Invᴵⁿᵈˣ-∅ :  ⊨ Invᴵⁿᵈˣ (∅ᴵⁿᴳ jᴵⁿᵈˣ)
  Invᴵⁿᵈˣ-∅ =  Smry-0

  -- Introduce ⇛ᴵⁿᵈˣ

  ⇛ᴵⁿᵈˣ-intro :  Pᵒ  ⊨ ⇛ᴵⁿᵈˣ  Pᵒ
  ⇛ᴵⁿᵈˣ-intro =  ⇛ᵍ¹-intro

  -- Get Indˣ P by storing ⸨ P ⸩

  Indˣ-new :  ⸨ P ⸩  ⊨ ⇛ᴵⁿᵈˣ  Indˣ P
  Indˣ-new =  ⇛ᵍ¹-make $ ?∗ᵒ-intro Indˣ-new' › ⤇ᴱ⟨⟩-eatʳ ›
    ⤇ᴱ⟨⟩-mono (λ _ → ∗ᵒ-monoʳ Smry-add-š) › ⤇ᴱ⟨⟩-param

  -- Consume Indˣ P to get ⸨ P ⸩

  Indˣ-use :  Indˣ P  ⊨  ⇛ᴵⁿᵈˣ  ⸨ P ⸩
  Indˣ-use =  ⇛ᵍ¹-make $ ∗ᵒ-monoˡ Indˣ-use' › ⤇ᴱ⟨⟩-eatʳ ›
    ⤇ᴱ⟨⟩-mono (λ{ (-, i<n , ≡šP) → ∗ᵒ-elimʳ Smry-Mono › Smry-rem-< i<n ≡šP }) ›
    ⤇ᴱ⟨⟩-param

--------------------------------------------------------------------------------
-- On Indᵖᴱᴿᴬ

-- Invᴵⁿᵈᵖ :  Invariant for Indᵖᴱᴿᴬ

Invᴵⁿᵈᵖ :  Envᴵⁿᵈᵖ →  Propᵒ 1ᴸ
Invᴵⁿᵈᵖ (P˙ , n) =  □ᵒ Smry (λ _ → ⸨_⸩) P˙ n

-- ⇛ᴵⁿᵈᵖ :  Fancy update on Indᵖᴱᴿᴬ

infix 3 ⇛ᴵⁿᵈᵖ_
⇛ᴵⁿᵈᵖ_ :  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⇛ᴵⁿᵈᵖ Pᵒ =  [ jᴵⁿᵈᵖ , Invᴵⁿᵈᵖ ]⇛ᵍ¹ Pᵒ

abstract

  -- Get Invᴵⁿᵈᵖ (∅ᴵⁿᴳ jᴵⁿᵈᵖ) for free

  Invᴵⁿᵈᵖ-∅ :  ⊨ Invᴵⁿᵈᵖ (∅ᴵⁿᴳ jᴵⁿᵈᵖ)
  Invᴵⁿᵈᵖ-∅ =  Smry-0

  -- Introduce ⇛ᴵⁿᵈᵖ

  ⇛ᴵⁿᵈᵖ-intro :  Pᵒ  ⊨ ⇛ᴵⁿᵈᵖ  Pᵒ
  ⇛ᴵⁿᵈᵖ-intro =  ⇛ᵍ¹-intro

  -- Get □ᵒ Indᵖ P by storing □ᵒ ⸨ P ⸩ minus □ᵒ Indᵖ P

  □ᵒIndᵖ-new-rec :  □ᵒ Indᵖ P -∗ᵒ □ᵒ ⸨ P ⸩  ⊨ ⇛ᴵⁿᵈᵖ  □ᵒ Indᵖ P
  □ᵒIndᵖ-new-rec {P} =  ⇛ᵍ¹-make $ ?∗ᵒ-intro □ᵒIndᵖ-new' › ⤇ᴱ⟨⟩-eatʳ ›
    -- □IndP∗(□IndP-∗□P)∗Inv → (□IndP∗□IndP)∗(□IndP-∗□P)∗Inv →
    -- □IndP∗(□IndP∗(□IndP-∗□P)∗Inv) → → □IndP∗(□P∗Inv) → → □IndP∗Inv
    ⤇ᴱ⟨⟩-mono✓ (λ _ ✓∙ → ∗ᵒ-monoˡ (dup-□ᵒ Indᵖ-Mono) › ∗ᵒ-assocʳ ›
      ∗ᵒ-mono✓ʳ (λ ✓∙ → ∗ᵒ-assocˡ ›
        ∗ᵒ-mono✓ˡ (-∗ᵒ-applyˡ $ □ᵒ-Mono $ ⸨⸩-Mono {P}) ✓∙ › □ᵒ-∗ᵒ-in ›
        Smry-add-š) ✓∙) › ⤇ᴱ⟨⟩-param

  -- Use Indᵖ P to get ⸨ P ⸩

  Indᵖ-use :  Indᵖ P  ⊨ ⇛ᴵⁿᵈᵖ  ⸨ P ⸩
  Indᵖ-use {P} =  ⇛ᵍ¹-make $ ∗ᵒ-monoˡ Indᵖ-use' › ⤇ᴱ⟨⟩-eatʳ ›
    -- Ind∗Inv → Inv → Inv∗Inv → (P∗Inv)∗Inv → P∗Inv
    ⤇ᴱ⟨⟩-mono (λ{ (-, i<n , ≡šP) → ∗ᵒ-elimʳ (□ᵒ-Mono Smry-Mono) ›
      dup-□ᵒ Smry-Mono › ∗ᵒ-monoˡ $ □ᵒ-elim Smry-Mono › Smry-rem-< i<n ≡šP ›
      ∗ᵒ-elimˡ (⸨⸩-Mono {P}) }) › ⤇ᴱ⟨⟩-param

--------------------------------------------------------------------------------
-- On Indˣᴱᴿᴬ and Indᵖᴱᴿᴬ

-- Invariant for Indˣᴱᴿᴬ and Indᵖᴱᴿᴬ

Invᴵⁿᵈ :  Envᴵⁿᵈ →  Propᵒ 1ᴸ
Invᴵⁿᵈ (Eᴵⁿᵈˣ , Eᴵⁿᵈᵖ) =  Invᴵⁿᵈˣ Eᴵⁿᵈˣ ∗ᵒ Invᴵⁿᵈᵖ Eᴵⁿᵈᵖ

-- Get Envᴵⁿᵈ out of Envᴵⁿᴳ

envᴵⁿᵈ :  Envᴵⁿᴳ →  Envᴵⁿᵈ
envᴵⁿᵈ E =  E jᴵⁿᵈˣ , E jᴵⁿᵈᵖ

-- Update Envᴵⁿᴳ with Envᴵⁿᵈ

updᴱᴵⁿᵈ :  Envᴵⁿᵈ →  Envᴵⁿᴳ →  Envᴵⁿᴳ
updᴱᴵⁿᵈ (Fᴵⁿᵈˣ , Fᴵⁿᵈᵖ) =  upd˙² jᴵⁿᵈˣ Fᴵⁿᵈˣ jᴵⁿᵈᵖ Fᴵⁿᵈᵖ

-- Fancy update for Indˣᴱᴿᴬ and Indᵖᴱᴿᴬ

infix 3 ⇛ᴵⁿᵈ_
⇛ᴵⁿᵈ_ :  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⇛ᴵⁿᵈ Pᵒ =  [ envᴵⁿᵈ , updᴱᴵⁿᵈ , Invᴵⁿᵈ ]⇛ᵍ Pᵒ

abstract

  -- Get Invᴵⁿᵈ (envᴵⁿᵈ ∅ᴵⁿᴳ) for free

  Invᴵⁿᵈ-∅ :  ⊨ Invᴵⁿᵈ (envᴵⁿᵈ ∅ᴵⁿᴳ)
  Invᴵⁿᵈ-∅ =  Invᴵⁿᵈˣ-∅ ▷ ∗ᵒ?-intro Invᴵⁿᵈᵖ-∅

  -- ⇛ᴵⁿᵈˣ into ⇛ᴵⁿᵈ

  ⇛ᴵⁿᵈˣ⇒⇛ᴵⁿᵈ :  ⇛ᴵⁿᵈˣ Pᵒ  ⊨  ⇛ᴵⁿᵈ Pᵒ
  ⇛ᴵⁿᵈˣ⇒⇛ᴵⁿᵈ =  ⇛ᵍ-mono ⇛ᴵⁿᵈᵖ-intro › ⇛ᵍ-join2 refl

  -- ⊨⇛ᴵⁿᵈᵖ into ⊨⇛ᴵⁿᵈ

  ⇛ᴵⁿᵈᵖ⇒⇛ᴵⁿᵈ :  ⇛ᴵⁿᵈᵖ Pᵒ  ⊨  ⇛ᴵⁿᵈ Pᵒ
  ⇛ᴵⁿᵈᵖ⇒⇛ᴵⁿᵈ =  ⇛ᴵⁿᵈˣ-intro › ⇛ᵍ-join2 refl

  -- Introduce ⇛ᴵⁿᵈ

  ⇛ᴵⁿᵈ-intro :  Pᵒ  ⊨ ⇛ᴵⁿᵈ  Pᵒ
  ⇛ᴵⁿᵈ-intro =  ⇛ᴵⁿᵈˣ-intro › ⇛ᴵⁿᵈˣ⇒⇛ᴵⁿᵈ

  -- Get Ind ⸨ P ⸩ by storing ⸨ P ⸩

  Ind-new :  ⸨ P ⸩  ⊨ ⇛ᴵⁿᵈ  Ind P
  Ind-new =  Indˣ-new › ⇛ᴵⁿᵈˣ⇒⇛ᴵⁿᵈ › ⇛ᵍ-mono ĩ₀_

  -- Get □ᵒ Ind P by storing □ᵒ ⸨ P ⸩ minus □ᵒ Ind P

  □ᵒInd-new-rec :  □ᵒ Ind P -∗ᵒ □ᵒ ⸨ P ⸩  ⊨ ⇛ᴵⁿᵈ  □ᵒ Ind P
  □ᵒInd-new-rec =  -∗ᵒ-monoˡ ĩ₁_ › □ᵒIndᵖ-new-rec › ⇛ᴵⁿᵈᵖ⇒⇛ᴵⁿᵈ › ⇛ᵍ-mono ĩ₁_

  -- Consume Ind P to get ⸨ P ⸩

  Ind-use :  Ind P  ⊨ ⇛ᴵⁿᵈ  ⸨ P ⸩
  Ind-use =  ⨿-case (Indˣ-use › ⇛ᴵⁿᵈˣ⇒⇛ᴵⁿᵈ) (Indᵖ-use › ⇛ᴵⁿᵈᵖ⇒⇛ᴵⁿᵈ)

--------------------------------------------------------------------------------
-- On ○ᵒ

abstract

  ○ᵒ-new :  ⸨ P ⸩  ⊨ ⇛ᴵⁿᵈ  ○ᵒ P
  ○ᵒ-new =  Ind-new › ⇛ᵍ-mono Ind⇒○ᵒ

  □ᵒ○ᵒ-new-rec :  □ᵒ ○ᵒ P -∗ᵒ □ᵒ ⸨ P ⸩  ⊨ ⇛ᴵⁿᵈ  □ᵒ ○ᵒ P
  □ᵒ○ᵒ-new-rec =  -∗ᵒ-monoˡ Ind⇒○ᵒ › □ᵒInd-new-rec › ⇛ᵍ-mono Ind⇒○ᵒ

  ○ᵒ-use :  ○ᵒ P  ⊨ ⇛ᴵⁿᵈ  ⸨ P ⸩
  ○ᵒ-use =  ∑-case λ Q → ∑ᴵ-case $ ∑-case λ _ → ∑-case λ Q∗R⊢P →
    ∗ᵒ-monoʳ Ind-use › ⇛ᵍ-eatˡ › ⇛ᵍ-mono✓ λ ✓∙ →
    ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {Q}) › ⊢-sem Q∗R⊢P ✓∙

--------------------------------------------------------------------------------
-- On ↪⇛ᵒ, ↪ᵃ⟨ ⟩ᵒ, ↪⟨ ⟩ᵒ and ↪⟨ ⟩∞ᵒ

  ↪⇛ᵒ-use :  P ↪[ i ]⇛ᴹ Q  ⊨ ⇛ᴵⁿᵈ  ∃ᵒ R ,  ⌜ P ∗ R ⊢[ ∞ ][ i ]⇛ Q ⌝ᵒ×  ⸨ R ⸩
  ↪⇛ᵒ-use =  ∑-case λ S → ∑ᴵ-case $ ∑-case λ _ → ∑-case λ P∗S∗T⊢⇛Q →
    ∗ᵒ-monoʳ Ind-use › ⇛ᵍ-eatˡ › ⇛ᵍ-mono $
    ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {S}) › (P∗S∗T⊢⇛Q ,_) › -,_

  ↪ᵃ⟨⟩ᵒ-use :  P ↪[ i ]ᵃ⟨ red ⟩ᵒ Q˙  ⊨ ⇛ᴵⁿᵈ
                 ∃ᵒ R ,  ⌜ P ∗ R ⊢[ ∞ ][ i ]ᵃ⟨ red ⟩ Q˙ ⌝ᵒ×  ⸨ R ⸩
  ↪ᵃ⟨⟩ᵒ-use =  ∑-case λ S → ∑ᴵ-case $ ∑-case λ _ → ∑-case λ P∗S∗T⊢⟨red⟩Q →
    ∗ᵒ-monoʳ Ind-use › ⇛ᵍ-eatˡ › ⇛ᵍ-mono $
    ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {S}) › (P∗S∗T⊢⟨red⟩Q ,_) › -,_

  ↪⟨⟩ᵒ-use :  P ↪⟨ e ⟩[ κ ]ᵒ Q˙  ⊨ ⇛ᴵⁿᵈ
                ∃ᵒ R ,  ⌜ P ∗ R ⊢[ ∞ ]⟨ e ⟩[ κ ] Q˙ ⌝ᵒ×  ⸨ R ⸩
  ↪⟨⟩ᵒ-use =  ∑-case λ S → ∑ᴵ-case $ ∑-case λ _ → ∑-case λ P∗S∗T⊢⟨e⟩Q →
    ∗ᵒ-monoʳ Ind-use › ⇛ᵍ-eatˡ › ⇛ᵍ-mono $
    ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {S}) › (P∗S∗T⊢⟨e⟩Q ,_) › -,_

  ↪⟨⟩∞ᵒ-use :  P ↪[ i ]⟨ e ⟩∞ᵒ  ⊨ ⇛ᴵⁿᵈ
                 ∃ᵒ Q ,  ⌜ P ∗ Q ⊢[ ∞ ][ i ]⟨ e ⟩∞ ⌝ᵒ×  ⸨ Q ⸩
  ↪⟨⟩∞ᵒ-use =  ∑-case λ R → ∑ᴵ-case $ ∑-case λ _ → ∑-case λ P∗R∗S⊢⟨e⟩∞ →
    ∗ᵒ-monoʳ Ind-use › ⇛ᵍ-eatˡ › ⇛ᵍ-mono $
    ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {R}) › (P∗R∗S⊢⟨e⟩∞ ,_) › -,_
