--------------------------------------------------------------------------------
-- Super update on the indirection modality and the precursors
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Ind where

open import Base.Level using (Level; _⊔ᴸ_; 1ᴸ)
open import Base.Size using (∞)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Eq using (_≡_; refl; _≡˙_; _◇˙_)
open import Base.Dec using (upd˙; upd˙²; upd˙-self)
open import Base.Option using (¿_)
open import Base.Prod using (_×_; _,_; -,_; -ᴵ,_; ∑-case; ∑ᴵ-case)
open import Base.Sum using (ĩ₀_; ĩ₁_; ⨿-case)
open import Base.Nat using (ℕ)
open import Syho.Lang.Expr using (Type; Expr∞)
open import Syho.Lang.Reduce using (Mem)
open import Syho.Logic.Prop using (WpKind; Prop∞; _∗_)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_)
open import Syho.Logic.Hor using (_⊢[_][_]ᵃ⟨_⟩_; _⊢[_]⟨_⟩[_]_)
open import Syho.Model.ERA.Ind using (Envᴵⁿᵈˣ; εᴵⁿᵈˣ; Envᴵⁿᵈᵖ; Envᴵⁿᵈ;
  indˣ-alloc; indˣ-use; indᵖ-alloc; indᵖ-use; )
open import Syho.Model.ERA.Glob using (Envᴵⁿᴳ; jᴵⁿᵈˣ; jᴵⁿᵈᵖ; empᴵⁿᴳ;
  upd˙-out-envᴳ)
open import Syho.Model.Prop.Base using (Propᵒ; _⊨_; ⊨_; ∃ᵒ-syntax; ⌜_⌝ᵒ×_; _∗ᵒ_;
  _-∗ᵒ_; □ᵒ_; ∗ᵒ-mono; ∗ᵒ-monoˡ; ∗ᵒ-monoʳ; ∗ᵒ-mono✓ˡ; ∗ᵒ-mono✓ʳ; ∗ᵒ-assocˡ;
  ∗ᵒ-assocʳ; ∗ᵒ-elimˡ; ∗ᵒ-elimʳ; ?∗ᵒ-intro; ∗ᵒ?-intro; ∃ᵒ∗ᵒ-out; -∗ᵒ-monoˡ;
  -∗ᵒ-apply; ⤇ᴱ-mono; ⤇ᴱ-mono✓; ⤇ᴱ-respᴱʳ; ⤇ᴱ-param; ⤇ᴱ-eatʳ; □ᵒ-Mono; □ᵒ-elim;
  dup-□ᵒ; □ᵒ-∗ᵒ-in; ◎-Mono; ◎⟨⟩-⌞⌟≡-□ᵒ; ↝-◎⟨⟩-⤇ᴱ; ε↝-◎⟨⟩-⤇ᴱ)
open import Syho.Model.Prop.Smry using (Smry; Smry-Mono; Smry-0; Smry-add-š;
  Smry-rem-<)
open import Syho.Model.Prop.Ind using (Indˣ; Indᵖ; Ind; ○ᵒ_; _↪[_]⇛ᵒ_;
  _↪[_]ᵃ⟨_⟩ᵒ_; _↪⟨_⟩ᵒ_; Ind⇒○ᵒ)
open import Syho.Model.Prop.Interp using (⸨_⸩; ⸨⸩-Mono; ⸨⸩-ᴮ⇒)
open import Syho.Model.Prop.Sound using (⊢-sem)
open import Syho.Model.Supd.Base using (⟨_⟩[_]⇛ᵍ⟨_⟩_; ⇛ᵍ-mono✓; ⇛ᵍ-mono;
  ⇛ᵍ-make; ⇛ᵍ-intro; ⇛ᵍ-join2; ⇛ᵍ-eatˡ)

private variable
  ł ł' :  Level
  i j m n :  ℕ
  P Q :  Prop∞
  X :  Set ł
  Q˙ :  X →  Prop∞
  Pˇ˙ Qˇ˙ :  X →  ¿ Prop∞
  Pˇ :  ¿ Prop∞
  Pᵒ Qᵒ Rᵒ Sᵒ :  Propᵒ ł
  Pᵒ˙ :  X → Propᵒ ł
  κ :  WpKind
  T :  Type
  e :  Expr∞ T
  E :  Envᴵⁿᴳ
  M M' :  Mem

--------------------------------------------------------------------------------
-- On Indˣᴱᴿᴬ

-- Invariant for Indˣᴱᴿᴬ

Invᴵⁿᵈˣ :  Envᴵⁿᵈˣ →  Propᵒ 1ᴸ
Invᴵⁿᵈˣ (P˙ , n) =  Smry ⸨_⸩ P˙ n

-- Super update on Indˣᴱᴿᴬ

infix 3 ⟨_⟩⇛ᴵⁿᵈˣ⟨_⟩_
⟨_⟩⇛ᴵⁿᵈˣ⟨_⟩_ :  Mem →  Mem →  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⟨ M ⟩⇛ᴵⁿᵈˣ⟨ M' ⟩ Pᵒ =
  ⟨ M ⟩[ (_$ jᴵⁿᵈˣ) , upd˙ jᴵⁿᵈˣ , Invᴵⁿᵈˣ ]⇛ᵍ⟨ M' ⟩ Pᵒ

abstract

  -- Get Invᴵⁿᵈˣ (empᴵⁿᴳ jᴵⁿᵈˣ) for free

  Invᴵⁿᵈˣ-emp :  ⊨ Invᴵⁿᵈˣ (empᴵⁿᴳ jᴵⁿᵈˣ)
  Invᴵⁿᵈˣ-emp =  Smry-0

  -- Allocate P to get Indˣ P

  Indˣ-alloc :  ⸨ P ⸩  ⊨  ⟨ M ⟩⇛ᴵⁿᵈˣ⟨ M ⟩  Indˣ P
  Indˣ-alloc =  ⇛ᵍ-make $ ?∗ᵒ-intro (ε↝-◎⟨⟩-⤇ᴱ indˣ-alloc) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ _ → ∗ᵒ-mono (-,_) Smry-add-š) › ⤇ᴱ-respᴱʳ upd˙-out-envᴳ ›
    ⤇ᴱ-param

  -- Consume Indˣ P to get P

  Indˣ-use :  Indˣ P  ⊨  ⟨ M ⟩⇛ᴵⁿᵈˣ⟨ M ⟩  ⸨ P ⸩
  Indˣ-use =  ⇛ᵍ-make $ ∃ᵒ∗ᵒ-out › ∑-case λ _ →
    ∗ᵒ-monoˡ (↝-◎⟨⟩-⤇ᴱ {bⁱ˙ = λ _ → εᴵⁿᵈˣ} indˣ-use) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ{ (≡šP , i<n) → ∗ᵒ-elimʳ Smry-Mono › Smry-rem-< ≡šP i<n }) ›
    ⤇ᴱ-respᴱʳ upd˙-out-envᴳ › ⤇ᴱ-param

--------------------------------------------------------------------------------
-- On Indᵖᴱᴿᴬ

-- Invariant for Indᵖᴱᴿᴬ

Invᴵⁿᵈᵖ :  Envᴵⁿᵈᵖ →  Propᵒ 1ᴸ
Invᴵⁿᵈᵖ (P˙ , n) =  □ᵒ Smry ⸨_⸩ P˙ n

-- Super update on Indᵖᴱᴿᴬ

infix 3 ⟨_⟩⇛ᴵⁿᵈᵖ⟨_⟩_
⟨_⟩⇛ᴵⁿᵈᵖ⟨_⟩_ :  Mem →  Mem →  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⟨ M ⟩⇛ᴵⁿᵈᵖ⟨ M' ⟩ Pᵒ =
  ⟨ M ⟩[ (_$ jᴵⁿᵈᵖ) , upd˙ jᴵⁿᵈᵖ , Invᴵⁿᵈᵖ ]⇛ᵍ⟨ M' ⟩ Pᵒ

abstract

  -- Get Invᴵⁿᵈᵖ (empᴵⁿᴳ jᴵⁿᵈᵖ) for free

  Invᴵⁿᵈᵖ-emp :  ⊨ Invᴵⁿᵈᵖ (empᴵⁿᴳ jᴵⁿᵈᵖ)
  Invᴵⁿᵈᵖ-emp =  Smry-0

  -- Allocate □ P to get □ᵒ Indᵖ P

  □ᵒIndᵖ-alloc-rec :  □ᵒ Indᵖ P -∗ᵒ □ᵒ ⸨ P ⸩  ⊨  ⟨ M ⟩⇛ᴵⁿᵈᵖ⟨ M ⟩  □ᵒ Indᵖ P
  □ᵒIndᵖ-alloc-rec {P} =  ⇛ᵍ-make $ ?∗ᵒ-intro (ε↝-◎⟨⟩-⤇ᴱ indᵖ-alloc) ›
    ⤇ᴱ-eatʳ › ⤇ᴱ-mono✓ (λ _ ✓∙ →
      ∗ᵒ-monoˡ (◎⟨⟩-⌞⌟≡-□ᵒ refl › dup-□ᵒ ◎-Mono › ∗ᵒ-mono (-,_) (-,_)) ›
      ∗ᵒ-assocˡ › ∗ᵒ-mono✓ʳ (λ ✓∙ → ∗ᵒ-assocʳ ›
        ∗ᵒ-mono✓ˡ (-∗ᵒ-apply $ □ᵒ-Mono $ ⸨⸩-Mono {P}) ✓∙ › □ᵒ-∗ᵒ-in ›
        Smry-add-š) ✓∙) › ⤇ᴱ-respᴱʳ upd˙-out-envᴳ › ⤇ᴱ-param

  -- Use Indᵖ P to get P

  Indᵖ-use :  Indᵖ P  ⊨  ⟨ M ⟩⇛ᴵⁿᵈᵖ⟨ M ⟩  ⸨ P ⸩
  Indᵖ-use {P} =  ⇛ᵍ-make $ ∃ᵒ∗ᵒ-out › ∑-case λ _ →
    ∗ᵒ-monoˡ (↝-◎⟨⟩-⤇ᴱ indᵖ-use) › ⤇ᴱ-eatʳ › ⤇ᴱ-mono (λ{ (≡šP , i<n) →
      ∗ᵒ-elimʳ (□ᵒ-Mono Smry-Mono) › dup-□ᵒ Smry-Mono › ∗ᵒ-monoˡ $
      □ᵒ-elim Smry-Mono › Smry-rem-< ≡šP i<n › ∗ᵒ-elimˡ (⸨⸩-Mono {P}) }) ›
    ⤇ᴱ-respᴱʳ upd˙-out-envᴳ › ⤇ᴱ-param

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

infix 8 ⟨_⟩⇛ᴵⁿᵈ⟨_⟩_
⟨_⟩⇛ᴵⁿᵈ⟨_⟩_ :  Mem →  Mem →  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⟨ M ⟩⇛ᴵⁿᵈ⟨ M' ⟩ Pᵒ =  ⟨ M ⟩[ envᴵⁿᵈ , updᴱᴵⁿᵈ , Invᴵⁿᵈ ]⇛ᵍ⟨ M' ⟩ Pᵒ

abstract

  -- Get Invᴵⁿᵈ (envᴵⁿᵈ empᴵⁿᴳ) for free

  Invᴵⁿᵈ-emp :  ⊨ Invᴵⁿᵈ (envᴵⁿᵈ empᴵⁿᴳ)
  Invᴵⁿᵈ-emp =  Invᴵⁿᵈˣ-emp ▷ ∗ᵒ?-intro Invᴵⁿᵈᵖ-emp

  -- ⇛ᴵⁿᵈˣ into ⇛ᴵⁿᵈ

  ⇛ᴵⁿᵈˣ⇒⇛ᴵⁿᵈ :  ⟨ M ⟩⇛ᴵⁿᵈˣ⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᴵⁿᵈ⟨ M' ⟩ Pᵒ
  ⇛ᴵⁿᵈˣ⇒⇛ᴵⁿᵈ =  ⇛ᵍ-mono (⇛ᵍ-intro {set = upd˙ jᴵⁿᵈᵖ} upd˙-self) › ⇛ᵍ-join2 refl

  -- ⊨⇛ᴵⁿᵈᵖ into ⊨⇛ᴵⁿᵈ

  ⇛ᴵⁿᵈᵖ⇒⇛ᴵⁿᵈ :  ⟨ M ⟩⇛ᴵⁿᵈᵖ⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᴵⁿᵈ⟨ M' ⟩ Pᵒ
  ⇛ᴵⁿᵈᵖ⇒⇛ᴵⁿᵈ =  ⇛ᵍ-intro {set = upd˙ jᴵⁿᵈˣ} upd˙-self › ⇛ᵍ-join2 refl

  -- Allocate P to get Ind P

  Ind-alloc :  ⸨ P ⸩  ⊨  ⟨ M ⟩⇛ᴵⁿᵈ⟨ M ⟩  Ind P
  Ind-alloc =  Indˣ-alloc › ⇛ᴵⁿᵈˣ⇒⇛ᴵⁿᵈ › ⇛ᵍ-mono ĩ₀_

  -- Allocate □ P to get □ᵒ Ind P

  □ᵒInd-alloc-rec :  □ᵒ Ind P -∗ᵒ □ᵒ ⸨ P ⸩  ⊨  ⟨ M ⟩⇛ᴵⁿᵈ⟨ M ⟩  □ᵒ Ind P
  □ᵒInd-alloc-rec =  -∗ᵒ-monoˡ ĩ₁_ › □ᵒIndᵖ-alloc-rec › ⇛ᴵⁿᵈᵖ⇒⇛ᴵⁿᵈ › ⇛ᵍ-mono ĩ₁_

  -- Consume Ind P to get P

  Ind-use :  Ind P  ⊨  ⟨ M ⟩⇛ᴵⁿᵈ⟨ M ⟩  ⸨ P ⸩
  Ind-use =  ⨿-case (Indˣ-use › ⇛ᴵⁿᵈˣ⇒⇛ᴵⁿᵈ) (Indᵖ-use › ⇛ᴵⁿᵈᵖ⇒⇛ᴵⁿᵈ)

--------------------------------------------------------------------------------
-- On ○ᵒ

abstract

  ○ᵒ-alloc :  ⸨ P ⸩  ⊨  ⟨ M ⟩⇛ᴵⁿᵈ⟨ M ⟩  ○ᵒ P
  ○ᵒ-alloc =  Ind-alloc › ⇛ᵍ-mono Ind⇒○ᵒ

  □ᵒ○ᵒ-alloc-rec :  □ᵒ ○ᵒ P -∗ᵒ □ᵒ ⸨ P ⸩  ⊨  ⟨ M ⟩⇛ᴵⁿᵈ⟨ M ⟩  □ᵒ ○ᵒ P
  □ᵒ○ᵒ-alloc-rec =  -∗ᵒ-monoˡ Ind⇒○ᵒ › □ᵒInd-alloc-rec › ⇛ᵍ-mono Ind⇒○ᵒ

  ○ᵒ-use :  ○ᵒ P  ⊨  ⟨ M ⟩⇛ᴵⁿᵈ⟨ M ⟩  ⸨ P ⸩
  ○ᵒ-use =  ∑-case λ Q → ∑ᴵ-case $ ∑-case λ _ → ∑-case λ Q∗R⊢P →
    ∗ᵒ-monoʳ Ind-use › ⇛ᵍ-eatˡ › ⇛ᵍ-mono✓ λ ✓∙ →
    ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {Q}) › ⊢-sem Q∗R⊢P ✓∙

--------------------------------------------------------------------------------
-- On ↪⇛ᵒ, ↪ᵃ⟨ ⟩ᵒ and ↪⟨ ⟩ᵒ

  ↪⇛ᵒ-use :  P ↪[ i ]⇛ᵒ Q  ⊨  ⟨ M ⟩⇛ᴵⁿᵈ⟨ M ⟩
               (∃ᵒ R ,  ⌜ P ∗ R ⊢[ ∞ ][ i ]⇛ Q ⌝ᵒ×  ⸨ R ⸩)
  ↪⇛ᵒ-use =  ∑-case λ S → ∑ᴵ-case $ ∑-case λ _ → ∑-case λ P∗S∗T⊢⇛Q →
    ∗ᵒ-monoʳ Ind-use › ⇛ᵍ-eatˡ › ⇛ᵍ-mono $
    ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {S}) › (P∗S∗T⊢⇛Q ,_) › -,_

  ↪ᵃ⟨⟩ᵒ-use :  P ↪[ i ]ᵃ⟨ e ⟩ᵒ Q˙  ⊨  ⟨ M ⟩⇛ᴵⁿᵈ⟨ M ⟩
                 (∃ᵒ R ,  ⌜ P ∗ R ⊢[ ∞ ][ i ]ᵃ⟨ e ⟩ Q˙ ⌝ᵒ×  ⸨ R ⸩)
  ↪ᵃ⟨⟩ᵒ-use =  ∑-case λ S → ∑ᴵ-case $ ∑-case λ _ → ∑-case λ P∗S∗T⊢⟨e⟩Q →
    ∗ᵒ-monoʳ Ind-use › ⇛ᵍ-eatˡ › ⇛ᵍ-mono $
    ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {S}) › (P∗S∗T⊢⟨e⟩Q ,_) › -,_

  ↪⟨⟩ᵒ-use :  P ↪⟨ e ⟩[ κ ]ᵒ Q˙  ⊨  ⟨ M ⟩⇛ᴵⁿᵈ⟨ M ⟩
                 (∃ᵒ R ,  ⌜ P ∗ R ⊢[ ∞ ]⟨ e ⟩[ κ ] Q˙ ⌝ᵒ×  ⸨ R ⸩)
  ↪⟨⟩ᵒ-use =  ∑-case λ S → ∑ᴵ-case $ ∑-case λ _ → ∑-case λ P∗S∗T⊢⟨e⟩Q →
    ∗ᵒ-monoʳ Ind-use › ⇛ᵍ-eatˡ › ⇛ᵍ-mono $
    ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {S}) › (P∗S∗T⊢⟨e⟩Q ,_) › -,_
