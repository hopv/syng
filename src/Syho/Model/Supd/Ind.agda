--------------------------------------------------------------------------------
-- Super update on the indirection modality and the precursors
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Ind where

open import Base.Level using (Level; _⊔ᴸ_; 1ᴸ)
open import Base.Size using (∞)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Eq using (_≡_; refl; _≡˙_; _◇˙_)
open import Base.Dec using (upd˙²)
open import Base.Option using (¿_)
open import Base.Prod using (_×_; _,_; -,_; -ᴵ,_; ∑-case; ∑ᴵ-case)
open import Base.Sum using (ĩ₀_; ĩ₁_; ⨿-case)
open import Base.Nat using (ℕ)
open import Syho.Lang.Expr using (Type; Expr∞; Mem)
open import Syho.Lang.Ktxred using (Redex)
open import Syho.Logic.Prop using (WpKind; Prop∞; _∗_)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_)
open import Syho.Logic.Hor using (_⊢[_][_]ᵃ⟨_⟩_; _⊢[_]⟨_⟩[_]_; _⊢[_][_]⟨_⟩∞)
open import Syho.Model.ERA.Ind using (Envᴵⁿᵈˣ; εᴵⁿᵈˣ; Envᴵⁿᵈᵖ; Envᴵⁿᵈ;
  indˣ-new; indˣ-use; indᵖ-new; indᵖ-use)
open import Syho.Model.ERA.Glob using (Envᴵⁿᴳ; jᴵⁿᵈˣ; jᴵⁿᵈᵖ; empᴵⁿᴳ)
open import Syho.Model.Prop.Base using (Propᵒ; _⊨_; ⊨_; ∃ᵒ-syntax; ⌜_⌝ᵒ×_; _∗ᵒ_;
  _-∗ᵒ_; □ᵒ_; ∗ᵒ-mono; ∗ᵒ-monoˡ; ∗ᵒ-monoʳ; ∗ᵒ-mono✓ˡ; ∗ᵒ-mono✓ʳ; ∗ᵒ-assocˡ;
  ∗ᵒ-assocʳ; ∗ᵒ-elimˡ; ∗ᵒ-elimʳ; ?∗ᵒ-intro; ∗ᵒ?-intro; ∃ᵒ∗ᵒ-out; -∗ᵒ-monoˡ;
  -∗ᵒ-applyˡ; ⤇ᴱ-mono; ⤇ᴱ-mono✓; ⤇ᴱ-param; ⤇ᴱ-eatʳ; □ᵒ-Mono; □ᵒ-elim; dup-□ᵒ;
  □ᵒ-∗ᵒ-in; ↝-◎⟨⟩-⤇ᴱ; ε↝-◎⟨⟩-⤇ᴱ)
open import Syho.Model.Prop.Smry using (Smry; Smry-Mono; Smry-0; Smry-add-š;
  Smry-rem-<)
open import Syho.Model.Prop.Ind using (Indˣ; Indᵖ; Ind; ○ᵒ_; _↪[_]⇛ᴹ_;
  _↪[_]ᵃ⟨_⟩ᵒ_; _↪⟨_⟩[_]ᵒ_; _↪[_]⟨_⟩∞ᵒ; Indᵖ-Mono; Indˣ-make; □ᵒIndᵖ-make;
  Ind⇒○ᵒ)
open import Syho.Model.Prop.Interp using (⸨_⸩; ⸨⸩-Mono; ⸨⸩-ᴮ⇒)
open import Syho.Model.Prop.Sound using (⊢-sem)
open import Syho.Model.Supd.Base using ([_]⇛ᵍᶠ_; [_]⇛ᵍ¹_; ⇛ᵍᶠ-mono✓; ⇛ᵍᶠ-mono;
  ⇛ᵍ¹-make; ⇛ᵍ¹-intro; ⇛ᵍᶠ-join2; ⇛ᵍᶠ-eatˡ)

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
  M M' :  Mem

--------------------------------------------------------------------------------
-- On Indˣᴱᴿᴬ

-- Invariant for Indˣᴱᴿᴬ

Invᴵⁿᵈˣ :  Envᴵⁿᵈˣ →  Propᵒ 1ᴸ
Invᴵⁿᵈˣ (P˙ , n) =  Smry (λ _ → ⸨_⸩) P˙ n

-- Super update on Indˣᴱᴿᴬ

infix 3 ⇛ᴵⁿᵈˣ_
⇛ᴵⁿᵈˣ_ :  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⇛ᴵⁿᵈˣ Pᵒ =  [ jᴵⁿᵈˣ , Invᴵⁿᵈˣ ]⇛ᵍ¹ Pᵒ

abstract

  -- Get Invᴵⁿᵈˣ (empᴵⁿᴳ jᴵⁿᵈˣ) for free

  Invᴵⁿᵈˣ-emp :  ⊨ Invᴵⁿᵈˣ (empᴵⁿᴳ jᴵⁿᵈˣ)
  Invᴵⁿᵈˣ-emp =  Smry-0

  -- Introduce ⇛ᴵⁿᵈˣ

  ⇛ᴵⁿᵈˣ-intro :  Pᵒ  ⊨ ⇛ᴵⁿᵈˣ  Pᵒ
  ⇛ᴵⁿᵈˣ-intro =  ⇛ᵍ¹-intro

  -- Get Indˣ P by storing P

  Indˣ-new :  ⸨ P ⸩  ⊨  ⇛ᴵⁿᵈˣ  Indˣ P
  Indˣ-new =  ⇛ᵍ¹-make $ ?∗ᵒ-intro (ε↝-◎⟨⟩-⤇ᴱ indˣ-new) › ⤇ᴱ-eatʳ ›
    (⤇ᴱ-mono λ _ → ∗ᵒ-mono Indˣ-make Smry-add-š) › ⤇ᴱ-param

  -- Consume Indˣ P to get P

  Indˣ-use :  Indˣ P  ⊨  ⇛ᴵⁿᵈˣ  ⸨ P ⸩
  Indˣ-use =  ⇛ᵍ¹-make $ ∃ᵒ∗ᵒ-out › ∑-case λ _ →
    ∗ᵒ-monoˡ (↝-◎⟨⟩-⤇ᴱ {bⁱ˙ = λ _ → εᴵⁿᵈˣ} indˣ-use) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ{ (≡šP , i<n) → ∗ᵒ-elimʳ Smry-Mono › Smry-rem-< ≡šP i<n }) ›
    ⤇ᴱ-param

--------------------------------------------------------------------------------
-- On Indᵖᴱᴿᴬ

-- Invariant for Indᵖᴱᴿᴬ

Invᴵⁿᵈᵖ :  Envᴵⁿᵈᵖ →  Propᵒ 1ᴸ
Invᴵⁿᵈᵖ (P˙ , n) =  □ᵒ Smry (λ _ → ⸨_⸩) P˙ n

-- Super update on Indᵖᴱᴿᴬ

infix 3 ⇛ᴵⁿᵈᵖ_
⇛ᴵⁿᵈᵖ_ :  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⇛ᴵⁿᵈᵖ Pᵒ =  [ jᴵⁿᵈᵖ , Invᴵⁿᵈᵖ ]⇛ᵍ¹ Pᵒ

abstract

  -- Get Invᴵⁿᵈᵖ (empᴵⁿᴳ jᴵⁿᵈᵖ) for free

  Invᴵⁿᵈᵖ-emp :  ⊨ Invᴵⁿᵈᵖ (empᴵⁿᴳ jᴵⁿᵈᵖ)
  Invᴵⁿᵈᵖ-emp =  Smry-0

  -- Introduce ⇛ᴵⁿᵈᵖ

  ⇛ᴵⁿᵈᵖ-intro :  Pᵒ  ⊨ ⇛ᴵⁿᵈᵖ  Pᵒ
  ⇛ᴵⁿᵈᵖ-intro =  ⇛ᵍ¹-intro

  -- Get □ᵒ Indᵖ P by storing □ P minus □ᵒ Indᵖ P

  □ᵒIndᵖ-new-rec :  □ᵒ Indᵖ P -∗ᵒ □ᵒ ⸨ P ⸩  ⊨ ⇛ᴵⁿᵈᵖ  □ᵒ Indᵖ P
  □ᵒIndᵖ-new-rec {P} =  ⇛ᵍ¹-make $ ?∗ᵒ-intro (ε↝-◎⟨⟩-⤇ᴱ indᵖ-new) ›
    ⤇ᴱ-eatʳ › ⤇ᴱ-mono✓ (λ _ ✓∙ → ∗ᵒ-monoˡ (□ᵒIndᵖ-make › dup-□ᵒ Indᵖ-Mono) ›
      -- (□IndP∗□IndP)∗(□IndP-∗□P)∗Inv → □IndP∗(□IndP∗(□IndP-∗□P)∗Inv) → →
      -- □IndP∗(□P∗Inv) → → □IndP∗Inv
      ∗ᵒ-assocˡ › ∗ᵒ-mono✓ʳ (λ ✓∙ → ∗ᵒ-assocʳ ›
        ∗ᵒ-mono✓ˡ (-∗ᵒ-applyˡ $ □ᵒ-Mono $ ⸨⸩-Mono {P}) ✓∙ › □ᵒ-∗ᵒ-in ›
        Smry-add-š) ✓∙) › ⤇ᴱ-param

  -- Use Indᵖ P to get P

  Indᵖ-use :  Indᵖ P  ⊨ ⇛ᴵⁿᵈᵖ  ⸨ P ⸩
  Indᵖ-use {P} =  ⇛ᵍ¹-make $ ∃ᵒ∗ᵒ-out › ∑-case λ _ →
    ∗ᵒ-monoˡ (↝-◎⟨⟩-⤇ᴱ indᵖ-use) › ⤇ᴱ-eatʳ › ⤇ᴱ-mono (λ{ (≡šP , i<n) →
      ∗ᵒ-elimʳ (□ᵒ-Mono Smry-Mono) › dup-□ᵒ Smry-Mono › ∗ᵒ-monoˡ $
      □ᵒ-elim Smry-Mono › Smry-rem-< ≡šP i<n › ∗ᵒ-elimˡ (⸨⸩-Mono {P}) }) ›
    ⤇ᴱ-param

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

-- Super update for Indˣᴱᴿᴬ and Indᵖᴱᴿᴬ

infix 3 ⇛ᴵⁿᵈ_
⇛ᴵⁿᵈ_ :  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⇛ᴵⁿᵈ Pᵒ =  [ envᴵⁿᵈ , updᴱᴵⁿᵈ , Invᴵⁿᵈ ]⇛ᵍᶠ Pᵒ

abstract

  -- Get Invᴵⁿᵈ (envᴵⁿᵈ empᴵⁿᴳ) for free

  Invᴵⁿᵈ-emp :  ⊨ Invᴵⁿᵈ (envᴵⁿᵈ empᴵⁿᴳ)
  Invᴵⁿᵈ-emp =  Invᴵⁿᵈˣ-emp ▷ ∗ᵒ?-intro Invᴵⁿᵈᵖ-emp

  -- ⇛ᴵⁿᵈˣ into ⇛ᴵⁿᵈ

  ⇛ᴵⁿᵈˣ⇒⇛ᴵⁿᵈ :  ⇛ᴵⁿᵈˣ Pᵒ  ⊨  ⇛ᴵⁿᵈ Pᵒ
  ⇛ᴵⁿᵈˣ⇒⇛ᴵⁿᵈ =  ⇛ᵍᶠ-mono ⇛ᴵⁿᵈᵖ-intro › ⇛ᵍᶠ-join2 refl

  -- ⊨⇛ᴵⁿᵈᵖ into ⊨⇛ᴵⁿᵈ

  ⇛ᴵⁿᵈᵖ⇒⇛ᴵⁿᵈ :  ⇛ᴵⁿᵈᵖ Pᵒ  ⊨  ⇛ᴵⁿᵈ Pᵒ
  ⇛ᴵⁿᵈᵖ⇒⇛ᴵⁿᵈ =  ⇛ᴵⁿᵈˣ-intro › ⇛ᵍᶠ-join2 refl

  -- Introduce ⇛ᴵⁿᵈ

  ⇛ᴵⁿᵈ-intro :  Pᵒ  ⊨ ⇛ᴵⁿᵈ  Pᵒ
  ⇛ᴵⁿᵈ-intro =  ⇛ᴵⁿᵈˣ-intro › ⇛ᴵⁿᵈˣ⇒⇛ᴵⁿᵈ

  -- Get Ind P by storing P

  Ind-new :  ⸨ P ⸩  ⊨ ⇛ᴵⁿᵈ  Ind P
  Ind-new =  Indˣ-new › ⇛ᴵⁿᵈˣ⇒⇛ᴵⁿᵈ › ⇛ᵍᶠ-mono ĩ₀_

  -- Get □ᵒ Ind P by storing □ P minus □ᵒ Ind P

  □ᵒInd-new-rec :  □ᵒ Ind P -∗ᵒ □ᵒ ⸨ P ⸩  ⊨ ⇛ᴵⁿᵈ  □ᵒ Ind P
  □ᵒInd-new-rec =  -∗ᵒ-monoˡ ĩ₁_ › □ᵒIndᵖ-new-rec › ⇛ᴵⁿᵈᵖ⇒⇛ᴵⁿᵈ › ⇛ᵍᶠ-mono ĩ₁_

  -- Consume Ind P to get P

  Ind-use :  Ind P  ⊨ ⇛ᴵⁿᵈ  ⸨ P ⸩
  Ind-use =  ⨿-case (Indˣ-use › ⇛ᴵⁿᵈˣ⇒⇛ᴵⁿᵈ) (Indᵖ-use › ⇛ᴵⁿᵈᵖ⇒⇛ᴵⁿᵈ)

--------------------------------------------------------------------------------
-- On ○ᵒ

abstract

  ○ᵒ-new :  ⸨ P ⸩  ⊨ ⇛ᴵⁿᵈ  ○ᵒ P
  ○ᵒ-new =  Ind-new › ⇛ᵍᶠ-mono Ind⇒○ᵒ

  □ᵒ○ᵒ-new-rec :  □ᵒ ○ᵒ P -∗ᵒ □ᵒ ⸨ P ⸩  ⊨ ⇛ᴵⁿᵈ  □ᵒ ○ᵒ P
  □ᵒ○ᵒ-new-rec =  -∗ᵒ-monoˡ Ind⇒○ᵒ › □ᵒInd-new-rec › ⇛ᵍᶠ-mono Ind⇒○ᵒ

  ○ᵒ-use :  ○ᵒ P  ⊨ ⇛ᴵⁿᵈ  ⸨ P ⸩
  ○ᵒ-use =  ∑-case λ Q → ∑ᴵ-case $ ∑-case λ _ → ∑-case λ Q∗R⊢P →
    ∗ᵒ-monoʳ Ind-use › ⇛ᵍᶠ-eatˡ › ⇛ᵍᶠ-mono✓ λ ✓∙ →
    ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {Q}) › ⊢-sem Q∗R⊢P ✓∙

--------------------------------------------------------------------------------
-- On ↪⇛ᵒ, ↪ᵃ⟨ ⟩ᵒ, ↪⟨ ⟩ᵒ and ↪⟨ ⟩∞ᵒ

  ↪⇛ᵒ-use :  P ↪[ i ]⇛ᴹ Q  ⊨ ⇛ᴵⁿᵈ  ∃ᵒ R ,  ⌜ P ∗ R ⊢[ ∞ ][ i ]⇛ Q ⌝ᵒ×  ⸨ R ⸩
  ↪⇛ᵒ-use =  ∑-case λ S → ∑ᴵ-case $ ∑-case λ _ → ∑-case λ P∗S∗T⊢⇛Q →
    ∗ᵒ-monoʳ Ind-use › ⇛ᵍᶠ-eatˡ › ⇛ᵍᶠ-mono $
    ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {S}) › (P∗S∗T⊢⇛Q ,_) › -,_

  ↪ᵃ⟨⟩ᵒ-use :  P ↪[ i ]ᵃ⟨ red ⟩ᵒ Q˙  ⊨ ⇛ᴵⁿᵈ
                 ∃ᵒ R ,  ⌜ P ∗ R ⊢[ ∞ ][ i ]ᵃ⟨ red ⟩ Q˙ ⌝ᵒ×  ⸨ R ⸩
  ↪ᵃ⟨⟩ᵒ-use =  ∑-case λ S → ∑ᴵ-case $ ∑-case λ _ → ∑-case λ P∗S∗T⊢⟨red⟩Q →
    ∗ᵒ-monoʳ Ind-use › ⇛ᵍᶠ-eatˡ › ⇛ᵍᶠ-mono $
    ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {S}) › (P∗S∗T⊢⟨red⟩Q ,_) › -,_

  ↪⟨⟩ᵒ-use :  P ↪⟨ e ⟩[ κ ]ᵒ Q˙  ⊨ ⇛ᴵⁿᵈ
                ∃ᵒ R ,  ⌜ P ∗ R ⊢[ ∞ ]⟨ e ⟩[ κ ] Q˙ ⌝ᵒ×  ⸨ R ⸩
  ↪⟨⟩ᵒ-use =  ∑-case λ S → ∑ᴵ-case $ ∑-case λ _ → ∑-case λ P∗S∗T⊢⟨e⟩Q →
    ∗ᵒ-monoʳ Ind-use › ⇛ᵍᶠ-eatˡ › ⇛ᵍᶠ-mono $
    ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {S}) › (P∗S∗T⊢⟨e⟩Q ,_) › -,_

  ↪⟨⟩∞ᵒ-use :  P ↪[ i ]⟨ e ⟩∞ᵒ  ⊨ ⇛ᴵⁿᵈ
                 ∃ᵒ Q ,  ⌜ P ∗ Q ⊢[ ∞ ][ i ]⟨ e ⟩∞ ⌝ᵒ×  ⸨ Q ⸩
  ↪⟨⟩∞ᵒ-use =  ∑-case λ R → ∑ᴵ-case $ ∑-case λ _ → ∑-case λ P∗R∗S⊢⟨e⟩∞ →
    ∗ᵒ-monoʳ Ind-use › ⇛ᵍᶠ-eatˡ › ⇛ᵍᶠ-mono $
    ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {R}) › (P∗R∗S⊢⟨e⟩∞ ,_) › -,_
