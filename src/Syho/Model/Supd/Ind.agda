--------------------------------------------------------------------------------
-- Super update on Ind, ○ᵒ, ↪⇛ᵒ, ↪⟨ ⟩ᴾᵒ, and ↪⟨ ⟩ᵀᵒ
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Ind where

open import Base.Level using (Level; _⊔ᴸ_; 2ᴸ)
open import Base.Size using (∞)
open import Base.Func using (_$_; _∘_; _›_)
open import Base.Few using (absurd)
open import Base.Eq using (_≡_; refl; _≡˙_; _◇˙_)
open import Base.Prod using (_×_; _,_; -,_; -ᴵ,_; ∑-case; ∑ᴵ-case)
open import Base.Sum using (ĩ₀_; ĩ₁_; ⊎-case)
open import Base.Dec using (yes; no)
open import Base.Nat using (ℕ; ṡ_; _≥_; _<_; _<ᵈ_; _≡?_; ≤-refl; <⇒≤; <-irrefl;
  ≤ᵈ-refl; ≤ᵈṡ; ≤ᵈ⇒≤; ≤⇒≤ᵈ; ≡?-refl)
open import Base.Natmap using (updᴺᴹ)
open import Syho.Lang.Expr using (Type; Expr)
open import Syho.Logic.Prop using (Prop'; ⊤'; _∗_)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_)
open import Syho.Logic.Hor using (_⊢[_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ[_]_)
open import Syho.Model.ERA.Ind using (alloc-indˣ; use-indˣ; alloc-ind□;
  use-ind□; Env-indˣ; Env-ind□; Env-ind)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ; Envᴳ; updᴱᴳ; indˣ; ind□;
  updᴱᴳ-cong; updᴱᴳ-self; updᴱᴳ-2; updᴱᴳ-swap)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨_; ∃ᵒ-syntax;
  ∃ᵒ∈-syntax; ⊤ᵒ; _∗ᵒ_; _-∗ᵒ_; □ᵒ_; ∗ᵒ-Mono; ∗ᵒ-mono; ∗ᵒ-monoˡ; ∗ᵒ-monoʳ;
  ∗ᵒ-mono✓ˡ; ∗ᵒ-mono✓ʳ; ∗ᵒ-assocˡ; ∗ᵒ-assocʳ; pullʳˡᵒ; ∗ᵒ-elimˡ; ∗ᵒ-elimʳ;
  ?∗ᵒ-intro; ∃ᵒ∗ᵒ-out; -∗ᵒ-monoˡ; -∗ᵒ-apply; ⤇ᴱ-mono; ⤇ᴱ-mono✓; ⤇ᴱ-param;
  ⤇ᴱ-eatʳ; □ᵒ-Mono; □ᵒ-elim; dup-□ᵒ; □ᵒ-∗ᵒ-in; ●-Mono; ●-injᴳ-⌞⌟≡-□ᵒ;
  ↝-●-injᴳ-⤇ᴱ; ε↝-●-injᴳ-⤇ᴱ)
open import Syho.Model.Prop.Ind using (Indˣ; Ind□; Ind; ○ᵒ_; _↪[_]⇛ᵒ_; _↪⟨_⟩ᴾᵒ_;
  _↪⟨_⟩ᵀ[_]ᵒ_; Ind⇒○ᵒ)
open import Syho.Model.Prop.Interp using (⸨_⸩; ⸨⸩-Mono; ⸨⸩-ᴮ⇒)
open import Syho.Model.Prop.Sound using (⊢⇒⊨✓)
open import Syho.Model.Supd.Base using ([_]⇛ᵍ_; ⇛ᵍ-mono✓; ⇛ᵍ-mono; ⇛ᵍ-make;
  ⇛ᵍ-intro; ⇛ᵍ-join2; ⇛ᵍ-eatˡ)

private variable
  ł ł' :  Level
  i j m n :  ℕ
  P Q :  Prop' ∞
  X :  Set ł
  P˙ Q˙ :  X → Prop' ∞
  Pᵒ Qᵒ Rᵒ Sᵒ :  Propᵒ ł
  Pᵒ˙ :  X → Propᵒ ł
  T :  Type
  e :  Expr ∞ T
  E :  Envᴳ

--------------------------------------------------------------------------------
-- Interpret a map ℕ → Prop' ∞ with a bound

⸨_⸩ᴺᴹ :  (ℕ → Prop' ∞) × ℕ →  Propᵒ 2ᴸ
⸨ P˙ , 0 ⸩ᴺᴹ =  ⊤ᵒ
⸨ P˙ , ṡ n ⸩ᴺᴹ =  ⸨ P˙ n ⸩ ∗ᵒ ⸨ P˙ , n ⸩ᴺᴹ

abstract
  -- Monoᵒ for ⸨ ⸩ᴺᴹ

  ⸨⸩ᴺᴹ-Mono :  Monoᵒ ⸨ P˙ , n ⸩ᴺᴹ
  ⸨⸩ᴺᴹ-Mono {n = 0} =  _
  ⸨⸩ᴺᴹ-Mono {n = ṡ _} =  ∗ᵒ-Mono

  -- Update an element out of the bound

  ⸨⸩ᴺᴹ-⇒upd-≥ :  i ≥ n →  ⸨ Q˙ , n ⸩ᴺᴹ  ⊨ ⸨ updᴺᴹ i P Q˙ , n ⸩ᴺᴹ
  ⸨⸩ᴺᴹ-⇒upd-≥ {_} {0} =  _
  ⸨⸩ᴺᴹ-⇒upd-≥ {i} {ṡ n'} i>n'  with n' ≡? i
  … | yes refl =  absurd $ <-irrefl i>n'
  … | no _ =  ∗ᵒ-monoʳ $ ⸨⸩ᴺᴹ-⇒upd-≥ $ <⇒≤ i>n'

  -- Add a proposition at the bound

  ⸨⸩ᴺᴹ-add :  ⸨ P ⸩ ∗ᵒ ⸨ Q˙ , n ⸩ᴺᴹ  ⊨ ⸨ updᴺᴹ n P Q˙ , ṡ n ⸩ᴺᴹ
  ⸨⸩ᴺᴹ-add {n = n}  rewrite ≡?-refl {n} =  ∗ᵒ-monoʳ $ ⸨⸩ᴺᴹ-⇒upd-≥ $ ≤-refl {n}

  ⸨⸩ᴺᴹ-add⊤ :  ⸨ P˙ , n ⸩ᴺᴹ  ⊨  ⸨ updᴺᴹ n ⊤' P˙ , ṡ n ⸩ᴺᴹ
  ⸨⸩ᴺᴹ-add⊤ {n = n} =  ?∗ᵒ-intro absurd › ⸨⸩ᴺᴹ-add {n = n}

  -- Remove an element within the bound to get the element's interpretation

  ⸨⸩ᴺᴹ-rem-<ᵈ :  i <ᵈ n →  ⸨ P˙ , n ⸩ᴺᴹ ⊨ ⸨ P˙ i ⸩ ∗ᵒ ⸨ updᴺᴹ i ⊤' P˙ , n ⸩ᴺᴹ
  ⸨⸩ᴺᴹ-rem-<ᵈ {i} ≤ᵈ-refl =  ∗ᵒ-monoʳ (⸨⸩ᴺᴹ-add⊤ {n = i})
  ⸨⸩ᴺᴹ-rem-<ᵈ {i} (≤ᵈṡ {n = n'} i<ᵈn')  with n' ≡? i
  … | yes refl =  absurd $ <-irrefl $ ≤ᵈ⇒≤ i<ᵈn'
  … | no _ =  ∗ᵒ-monoʳ (⸨⸩ᴺᴹ-rem-<ᵈ i<ᵈn') › pullʳˡᵒ

  ⸨⸩ᴺᴹ-rem-< :  i < n →  ⸨ P˙ , n ⸩ᴺᴹ ⊨ ⸨ P˙ i ⸩ ∗ᵒ ⸨ updᴺᴹ i ⊤' P˙ , n ⸩ᴺᴹ
  ⸨⸩ᴺᴹ-rem-< =  ⸨⸩ᴺᴹ-rem-<ᵈ ∘ ≤⇒≤ᵈ

--------------------------------------------------------------------------------
-- On Indˣᴱᴿᴬ

-- Invariant for Indˣᴱᴿᴬ

Inv-indˣ :  Env-indˣ →  Propᵒ 2ᴸ
Inv-indˣ Eˣ =  ⸨ Eˣ ⸩ᴺᴹ

-- Super update on Indˣᴱᴿᴬ

infix 8 ⇛indˣ_
⇛indˣ_ :  Propᵒ ł →  Propᵒ (2ᴸ ⊔ᴸ ł)
⇛indˣ Pᵒ =  [ (λ E → E indˣ) , updᴱᴳ indˣ , Inv-indˣ ]⇛ᵍ Pᵒ

abstract

  -- Allocate P to get Indˣ P

  Indˣ-alloc :  ⸨ P ⸩  ⊨  ⇛indˣ  Indˣ P
  Indˣ-alloc =  ⇛ᵍ-make λ E _ → let (_ , n) = E indˣ in
    ?∗ᵒ-intro (ε↝-●-injᴳ-⤇ᴱ alloc-indˣ) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ _ → ∗ᵒ-mono (_ ,_) $ ⸨⸩ᴺᴹ-add {n = n}) › ⤇ᴱ-param

  -- Consume Indˣ P to get P

  Indˣ-use :  Indˣ P  ⊨  ⇛indˣ  ⸨ P ⸩
  Indˣ-use =  ⇛ᵍ-make λ E _ → let (_ , n) = E indˣ in
    ∃ᵒ∗ᵒ-out › ∑-case λ _ → ∗ᵒ-monoˡ (↝-●-injᴳ-⤇ᴱ use-indˣ) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ{ (refl , i<n) → ∗ᵒ-elimʳ (⸨⸩ᴺᴹ-Mono {n = n}) › ⸨⸩ᴺᴹ-rem-< i<n })
    › ⤇ᴱ-param

--------------------------------------------------------------------------------
-- On Ind□ᴱᴿᴬ

-- Invariant for Ind□ᴱᴿᴬ

Inv-ind□ :  Env-ind□ →  Propᵒ 2ᴸ
Inv-ind□ E□ =  □ᵒ ⸨ E□ ⸩ᴺᴹ

-- Super update on Ind□ᴱᴿᴬ

infix 8 ⇛ind□_
⇛ind□_ :  Propᵒ ł →  Propᵒ (2ᴸ ⊔ᴸ ł)
⇛ind□ Pᵒ =  [ (λ E → E ind□) , updᴱᴳ ind□ , Inv-ind□ ]⇛ᵍ Pᵒ

abstract

  -- Allocate □ P to get □ᵒ Ind□ P

  □ᵒInd□-alloc-rec :  □ᵒ Ind□ P -∗ᵒ □ᵒ ⸨ P ⸩  ⊨  ⇛ind□  □ᵒ Ind□ P
  □ᵒInd□-alloc-rec {P} =  ⇛ᵍ-make λ E _ → let (_ , n) = E ind□ in
    ?∗ᵒ-intro (ε↝-●-injᴳ-⤇ᴱ alloc-ind□) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono✓ (λ _ ✓∙ →
      ∗ᵒ-monoˡ (●-injᴳ-⌞⌟≡-□ᵒ refl › dup-□ᵒ ●-Mono › ∗ᵒ-mono (_ ,_) (_ ,_)) ›
      ∗ᵒ-assocˡ › ∗ᵒ-mono✓ʳ (λ ✓∙ → ∗ᵒ-assocʳ ›
        ∗ᵒ-mono✓ˡ (-∗ᵒ-apply $ □ᵒ-Mono $ ⸨⸩-Mono {P}) ✓∙ › □ᵒ-∗ᵒ-in ›
        ⸨⸩ᴺᴹ-add {P} {n = n}) ✓∙) › ⤇ᴱ-param

  -- Use Ind□ P to get P

  Ind□-use :  Ind□ P  ⊨  ⇛ind□  ⸨ P ⸩
  Ind□-use {P} =  ⇛ᵍ-make λ E _ → let (_ , n) = E ind□ in
    ∃ᵒ∗ᵒ-out › ∑-case λ _ → ∗ᵒ-monoˡ (↝-●-injᴳ-⤇ᴱ use-ind□) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ{ (refl , i<n) → ∗ᵒ-elimʳ (□ᵒ-Mono $ ⸨⸩ᴺᴹ-Mono {n = n}) ›
      dup-□ᵒ (⸨⸩ᴺᴹ-Mono {n = n}) › ∗ᵒ-monoˡ $ □ᵒ-elim (⸨⸩ᴺᴹ-Mono {n = n}) ›
      ⸨⸩ᴺᴹ-rem-< i<n › ∗ᵒ-elimˡ (⸨⸩-Mono {P}) }) › ⤇ᴱ-param

--------------------------------------------------------------------------------
-- On Indˣᴱᴿᴬ and Ind□ᴱᴿᴬ

-- Invariant for Indˣᴱᴿᴬ and Ind□ᴱᴿᴬ

Inv-ind :  Env-ind →  Propᵒ 2ᴸ
Inv-ind (Eˣ , E□) =  Inv-indˣ Eˣ ∗ᵒ Inv-ind□ E□

-- Get Env-ind out of Envᴳ

env-ind :  Envᴳ →  Env-ind
env-ind E =  E indˣ , E ind□

-- Update Envᴳ with Env-ind

updᴱ-ind :  Env-ind →  Envᴳ →  Envᴳ
updᴱ-ind (Fˣ , F□) =  updᴱᴳ indˣ Fˣ › updᴱᴳ ind□ F□

-- Super update for Indˣᴱᴿᴬ and Ind□ᴱᴿᴬ

infix 8 ⇛ind_
⇛ind_ :  Propᵒ ł →  Propᵒ (2ᴸ ⊔ᴸ ł)
⇛ind Pᵒ =  [ env-ind , updᴱ-ind , Inv-ind ]⇛ᵍ Pᵒ

private variable
  Fˣ□ Gˣ□ :  Env-ind

abstract

  -- Self updᴱ-ind

  updᴱ-ind-self :  updᴱ-ind (env-ind E) E  ≡˙  E
  updᴱ-ind-self =  updᴱᴳ-self ◇˙ updᴱᴳ-self

  -- Double updᴱ-ind

  updᴱ-ind-2 :  updᴱ-ind Gˣ□ (updᴱ-ind Fˣ□ E)  ≡˙  updᴱ-ind Gˣ□ E
  updᴱ-ind-2 =  updᴱᴳ-cong (updᴱᴳ-swap λ ()) ◇˙ updᴱᴳ-2 ◇˙ updᴱᴳ-cong updᴱᴳ-2

  -- ⇛indˣ into ⇛ind

  ⇛indˣ⇒⇛ind :  ⇛indˣ Pᵒ  ⊨  ⇛ind Pᵒ
  ⇛indˣ⇒⇛ind =  ⇛ᵍ-mono (⇛ᵍ-intro {set = updᴱᴳ ind□} updᴱᴳ-self) › ⇛ᵍ-join2 refl

  -- ⊨⇛ind□ into ⊨⇛ind

  ⇛ind□⇒⇛ind :  ⇛ind□ Pᵒ  ⊨  ⇛ind Pᵒ
  ⇛ind□⇒⇛ind =  ⇛ᵍ-intro {set = updᴱᴳ indˣ} updᴱᴳ-self › ⇛ᵍ-join2 refl

  -- Allocate P to get Ind P

  Ind-alloc :  ⸨ P ⸩  ⊨  ⇛ind  Ind P
  Ind-alloc =  Indˣ-alloc › ⇛indˣ⇒⇛ind › ⇛ᵍ-mono ĩ₀_

  -- Allocate □ P to get □ᵒ Ind P

  □ᵒInd-alloc-rec :  □ᵒ Ind P -∗ᵒ □ᵒ ⸨ P ⸩  ⊨  ⇛ind  □ᵒ Ind P
  □ᵒInd-alloc-rec =  -∗ᵒ-monoˡ ĩ₁_ › □ᵒInd□-alloc-rec › ⇛ind□⇒⇛ind › ⇛ᵍ-mono ĩ₁_

  -- Consume Ind P to get P

  Ind-use :  Ind P  ⊨  ⇛ind  ⸨ P ⸩
  Ind-use =  ⊎-case (Indˣ-use › ⇛indˣ⇒⇛ind) (Ind□-use › ⇛ind□⇒⇛ind)

--------------------------------------------------------------------------------
-- On ○ᵒ

abstract

  ○ᵒ-alloc :  ⸨ P ⸩  ⊨  ⇛ind  ○ᵒ P
  ○ᵒ-alloc =  Ind-alloc › ⇛ᵍ-mono Ind⇒○ᵒ

  □ᵒ○ᵒ-alloc-rec :  □ᵒ ○ᵒ P -∗ᵒ □ᵒ ⸨ P ⸩  ⊨  ⇛ind  □ᵒ ○ᵒ P
  □ᵒ○ᵒ-alloc-rec =  -∗ᵒ-monoˡ Ind⇒○ᵒ › □ᵒInd-alloc-rec › ⇛ᵍ-mono Ind⇒○ᵒ

  ○ᵒ-use :  ○ᵒ P  ⊨  ⇛ind  ⸨ P ⸩
  ○ᵒ-use =  ∑-case λ Q → ∑ᴵ-case $ ∑-case λ _ → ∑-case λ Q∗R⊢P →
    ∗ᵒ-monoʳ Ind-use › ⇛ᵍ-eatˡ › ⇛ᵍ-mono✓ λ ✓∙ →
    ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {Q}) › ⊢⇒⊨✓ Q∗R⊢P ✓∙

--------------------------------------------------------------------------------
-- On ↪⇛ᵒ, ↪⟨ ⟩ᴾᵒ, and ↪⟨ ⟩ᵀᵒ

  ↪⇛ᵒ-use :  P ↪[ i ]⇛ᵒ Q  ⊨  ⇛ind
               (∃ᵒ R , ∃ᵒ _ ∈ (P ∗ R ⊢[ ∞ ][ i ]⇛ Q) , ⸨ R ⸩)
  ↪⇛ᵒ-use =  ∑-case λ S → ∑ᴵ-case $ ∑-case λ _ → ∑-case λ P∗S∗T⊢⇛Q →
    ∗ᵒ-monoʳ Ind-use › ⇛ᵍ-eatˡ › ⇛ᵍ-mono $
    ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {S}) › (P∗S∗T⊢⇛Q ,_) › -,_

  ↪⟨⟩ᴾᵒ-use :  P ↪⟨ e ⟩ᴾᵒ Q˙  ⊨  ⇛ind
                 (∃ᵒ R , ∃ᵒ _ ∈ (P ∗ R ⊢[ ∞ ]⟨ e ⟩ᴾ Q˙) , ⸨ R ⸩)
  ↪⟨⟩ᴾᵒ-use =  ∑-case λ S → ∑ᴵ-case $ ∑-case λ _ → ∑-case λ P∗S∗T⊢⟨e⟩Q →
    ∗ᵒ-monoʳ Ind-use › ⇛ᵍ-eatˡ › ⇛ᵍ-mono $
    ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {S}) › (P∗S∗T⊢⟨e⟩Q ,_) › -,_

  ↪⟨⟩ᵀᵒ-use :  P ↪⟨ e ⟩ᵀ[ i ]ᵒ Q˙ ⊨  ⇛ind
                 (∃ᵒ R , ∃ᵒ _ ∈ (P ∗ R ⊢[ ∞ ]⟨ e ⟩ᵀ[ i ] Q˙) , ⸨ R ⸩)
  ↪⟨⟩ᵀᵒ-use =  ∑-case λ S → ∑ᴵ-case $ ∑-case λ _ → ∑-case λ P∗S∗T⊢⟨e⟩Q →
    ∗ᵒ-monoʳ Ind-use › ⇛ᵍ-eatˡ › ⇛ᵍ-mono $
    ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {S}) › (P∗S∗T⊢⟨e⟩Q ,_) › -,_
