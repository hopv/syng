--------------------------------------------------------------------------------
-- Super update on Ind, ○ᵒ, ↪⇛ᵒ, ↪⟨ ⟩ᴾᵒ, and ↪⟨ ⟩ᵀᵒ
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Ind where

open import Base.Level using (Level; _⊔ᴸ_; 2ᴸ)
open import Base.Size using (∞)
open import Base.Func using (_$_; _▷_; _›_; _∘_; id)
open import Base.Few using (absurd)
open import Base.Eq using (_≡_; refl)
open import Base.Prod using (_×_; _,_; -,_; -ᴵ,_; ∑-case; ∑ᴵ-case)
open import Base.Sum using (inj₀; inj₁; ⊎-case)
open import Base.Bool using (tt; ff)
open import Base.Nat using (ℕ; ṡ_; _≥_; _<_; _<ᵈ_; _≡ᵇ_; ≤-refl; <⇒≤; <-irrefl;
  ≤ᵈ-refl; ≤ᵈṡ; ≤ᵈ⇒≤; ≤⇒≤ᵈ; ᵇ⇒≡; ≡ᵇ-refl; ≢-≡ᵇ-ff)
open import Base.Natmap using (updᴺᴹ)
open import Syho.Lang.Expr using (Type; Expr)
open import Syho.Logic.Prop using (Prop'; ⊤'; _∗_)
open import Syho.Logic.Core using (∗-elimʳ)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_)
open import Syho.Logic.Hor using (_⊢[_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ[_]_)
open import Syho.Model.ERA.Ind using (alloc-indˣ; use-indˣ; alloc-ind□;
  use-ind□; Env-indˣ; Env-ind□; Env-ind)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ; Envᴳ; updᴱᴳ; indˣ; ind□;
  updᴱᴳ-self)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨_; _⊨✓_; ∃ᵒ˙; ∃ᵒ-syntax;
  ∃ᵒ∈-syntax; ∃ᴵ˙; ⊤ᵒ; _∗ᵒ_; _-∗ᵒ_; _⤇ᴱ_; □ᵒ_; ⊨⇒⊨✓; ∗ᵒ-Mono; ∗ᵒ-mono; ∗ᵒ-monoˡ;
  ∗ᵒ-monoʳ; ∗ᵒ-mono✓ˡ; ∗ᵒ-mono✓ʳ; ∗ᵒ-comm; ∗ᵒ-assocˡ; ∗ᵒ-assocʳ; pullʳˡᵒ;
  ∗ᵒ-elimˡ; ∗ᵒ-elimʳ; ?∗ᵒ-intro; ∃ᵒ∗ᵒ-out; ∃ᴵ∗ᵒ-out; ⊎ᵒ∗ᵒ-out; -∗ᵒ-monoˡ;
  -∗ᵒ-apply; ⤇ᴱ-mono; ⤇ᴱ-mono✓; ⤇ᴱ-respᴱ; ⤇ᴱ-param; ⤇ᴱ-intro; ⤇ᴱ-join; ⤇ᴱ-eatˡ;
  ⤇ᴱ-eatʳ; □ᵒ-Mono; □ᵒ-elim; dup-□ᵒ; □ᵒ-∗ᵒ-in; ●-Mono; ●-injᴳ-⌞⌟≡-□ᵒ;
  ↝-●-injᴳ-⤇ᴱ; ε↝-●-injᴳ-⤇ᴱ)
open import Syho.Model.Prop.Ind using (Indˣ; Ind□; Ind; ○ᵒ_; _↪[_]⇛ᵒ_; _↪⟨_⟩ᴾᵒ_;
  _↪⟨_⟩ᵀ[_]ᵒ_)
open import Syho.Model.Prop.Interp using (⸨_⸩; ⸨⸩-Mono; ⸨⸩-ᴮ⇒)
open import Syho.Model.Prop.Pure using (⊢⇒⊨✓)

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
  ⸨⸩ᴺᴹ-⇒upd-≥ {i} {ṡ n'} i>n'  with n' ≡ᵇ i | ᵇ⇒≡ {n'} {i}
  … | tt | ⇒n'≡i  rewrite ⇒n'≡i _ =  absurd $ <-irrefl i>n'
  … | ff | _ =  ∗ᵒ-monoʳ $ ⸨⸩ᴺᴹ-⇒upd-≥ $ <⇒≤ i>n'

  -- Add a proposition at the bound

  ⸨⸩ᴺᴹ-add :  ⸨ P ⸩ ∗ᵒ ⸨ Q˙ , n ⸩ᴺᴹ  ⊨ ⸨ updᴺᴹ n P Q˙ , ṡ n ⸩ᴺᴹ
  ⸨⸩ᴺᴹ-add {n = n}  rewrite ≡ᵇ-refl {n} =  ∗ᵒ-monoʳ $ ⸨⸩ᴺᴹ-⇒upd-≥ $ ≤-refl {n}

  ⸨⸩ᴺᴹ-add⊤ :  ⸨ P˙ , n ⸩ᴺᴹ  ⊨  ⸨ updᴺᴹ n ⊤' P˙ , ṡ n ⸩ᴺᴹ
  ⸨⸩ᴺᴹ-add⊤ {n = n} =  ?∗ᵒ-intro absurd › ⸨⸩ᴺᴹ-add {n = n}

  -- Remove an element within the bound to get the element's interpretation

  ⸨⸩ᴺᴹ-rem-<ᵈ :  i <ᵈ n →  ⸨ P˙ , n ⸩ᴺᴹ ⊨ ⸨ P˙ i ⸩ ∗ᵒ ⸨ updᴺᴹ i ⊤' P˙ , n ⸩ᴺᴹ
  ⸨⸩ᴺᴹ-rem-<ᵈ {i} ≤ᵈ-refl =  ∗ᵒ-monoʳ (⸨⸩ᴺᴹ-add⊤ {n = i})
  ⸨⸩ᴺᴹ-rem-<ᵈ {i} (≤ᵈṡ {n = n'} i<ᵈn')
    rewrite ≢-≡ᵇ-ff {n'} {i} λ{ refl → <-irrefl $ ≤ᵈ⇒≤ i<ᵈn'} =
    ∗ᵒ-monoʳ (⸨⸩ᴺᴹ-rem-<ᵈ i<ᵈn') › pullʳˡᵒ

  ⸨⸩ᴺᴹ-rem-< :  i < n →  ⸨ P˙ , n ⸩ᴺᴹ ⊨ ⸨ P˙ i ⸩ ∗ᵒ ⸨ updᴺᴹ i ⊤' P˙ , n ⸩ᴺᴹ
  ⸨⸩ᴺᴹ-rem-< =  ⸨⸩ᴺᴹ-rem-<ᵈ ∘ ≤⇒≤ᵈ

--------------------------------------------------------------------------------
-- On Indˣᴱᴿᴬ

-- Invariant for Indˣᴱᴿᴬ

Inv-indˣ :  Env-indˣ →  Propᵒ 2ᴸ
Inv-indˣ Eˣ =  ⸨ Eˣ ⸩ᴺᴹ

-- Super update entailment on Indˣᴱᴿᴬ

infix 1 _⊨⇛indˣ_
_⊨⇛indˣ_ :  Propᵒ ł →  Propᵒ ł' →  Set (2ᴸ ⊔ᴸ ł ⊔ᴸ ł')
Pᵒ ⊨⇛indˣ Qᵒ =  ∀ E →  Pᵒ ∗ᵒ Inv-indˣ (E indˣ)  ⊨✓
                         E ⤇ᴱ λ Fˣ → updᴱᴳ indˣ Fˣ E , Qᵒ ∗ᵒ Inv-indˣ Fˣ

abstract

  -- Allocate P to get Indˣ P

  Indˣ-alloc :  ⸨ P ⸩  ⊨⇛indˣ  Indˣ P
  Indˣ-alloc E _ =  let (_ , n) = E indˣ in
    ?∗ᵒ-intro (ε↝-●-injᴳ-⤇ᴱ alloc-indˣ) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ _ → ∗ᵒ-mono (_ ,_) $ ⸨⸩ᴺᴹ-add {n = n}) › ⤇ᴱ-param

  -- Consume Indˣ P to get P

  Indˣ-use :  Indˣ P  ⊨⇛indˣ  ⸨ P ⸩
  Indˣ-use E _ =  let (_ , n) = E indˣ in
    ∃ᵒ∗ᵒ-out › ∑-case λ _ → ∗ᵒ-monoˡ (↝-●-injᴳ-⤇ᴱ use-indˣ) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ{ (refl , i<n) → ∗ᵒ-elimʳ (⸨⸩ᴺᴹ-Mono {n = n}) › ⸨⸩ᴺᴹ-rem-< i<n })
    › ⤇ᴱ-param

--------------------------------------------------------------------------------
-- On Ind□ᴱᴿᴬ

-- Invariant for Ind□ᴱᴿᴬ

Inv-ind□ :  Env-ind□ →  Propᵒ 2ᴸ
Inv-ind□ E□ =  □ᵒ ⸨ E□ ⸩ᴺᴹ

-- Super update entailment on Ind□ᴱᴿᴬ

infix 1 _⊨⇛ind□_
_⊨⇛ind□_ :  Propᵒ ł →  Propᵒ ł' →  Set (2ᴸ ⊔ᴸ ł ⊔ᴸ ł')
Pᵒ ⊨⇛ind□ Qᵒ =  ∀ E →  Pᵒ ∗ᵒ Inv-ind□ (E ind□)  ⊨✓
                         E ⤇ᴱ λ F□ → updᴱᴳ ind□ F□ E , Qᵒ ∗ᵒ Inv-ind□ F□

abstract

  -- Allocate □ P to get □ᵒ Ind□ P

  □ᵒInd□-alloc-rec :  □ᵒ Ind□ P -∗ᵒ □ᵒ ⸨ P ⸩  ⊨⇛ind□  □ᵒ Ind□ P
  □ᵒInd□-alloc-rec {P} E _ =  let (_ , n) = E ind□ in
    ?∗ᵒ-intro (ε↝-●-injᴳ-⤇ᴱ alloc-ind□) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono✓ (λ _ ✓∙ →
      ∗ᵒ-monoˡ (●-injᴳ-⌞⌟≡-□ᵒ refl › dup-□ᵒ ●-Mono › ∗ᵒ-mono (_ ,_) (_ ,_)) ›
      ∗ᵒ-assocˡ › ∗ᵒ-mono✓ʳ (λ ✓∙ → ∗ᵒ-assocʳ ›
        ∗ᵒ-mono✓ˡ (-∗ᵒ-apply $ □ᵒ-Mono $ ⸨⸩-Mono {P}) ✓∙ › □ᵒ-∗ᵒ-in ›
        ⸨⸩ᴺᴹ-add {P} {n = n}) ✓∙) › ⤇ᴱ-param

  -- Use Ind□ P to get P

  Ind□-use :  Ind□ P  ⊨⇛ind□  ⸨ P ⸩
  Ind□-use {P} E _ =  let (_ , n) = E ind□ in
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

infix 1 _⊨⇛ind_
_⊨⇛ind_ :  Propᵒ ł →  Propᵒ ł' →  Set (2ᴸ ⊔ᴸ ł ⊔ᴸ ł')
Pᵒ ⊨⇛ind Qᵒ =  ∀ E →  Pᵒ ∗ᵒ Inv-ind (env-ind E)  ⊨✓
                        E ⤇ᴱ λ F → updᴱ-ind F E , Qᵒ ∗ᵒ Inv-ind F

abstract

  -- ⊨⇛indˣ into ⊨⇛ind

  ⊨⇛indˣ⇒⊨⇛ind :  Pᵒ ⊨⇛indˣ Qᵒ →  Pᵒ ⊨⇛ind Qᵒ
  ⊨⇛indˣ⇒⊨⇛ind P⊨⇛indˣQ _ ✓∙ =  ∗ᵒ-assocʳ › ∗ᵒ-mono✓ˡ (P⊨⇛indˣQ _) ✓∙ ›
    ⤇ᴱ-eatʳ › ⤇ᴱ-mono (λ _ → ∗ᵒ-assocˡ › ⤇ᴱ-intro › ⤇ᴱ-respᴱ updᴱᴳ-self) ›
    ⤇ᴱ-join › ⤇ᴱ-param

  -- ⊨⇛ind□ into ⊨⇛ind

  ⊨⇛ind□⇒⊨⇛ind :  Pᵒ ⊨⇛ind□ Qᵒ →  Pᵒ ⊨⇛ind Qᵒ
  ⊨⇛ind□⇒⊨⇛ind P⊨⇛ind□Q _ _ =  ∗ᵒ-monoʳ ∗ᵒ-comm › ∗ᵒ-assocʳ ›
    ∗ᵒ-monoˡ (⤇ᴱ-intro ›
      ⤇ᴱ-respᴱ updᴱᴳ-self › ⤇ᴱ-mono✓ (λ _ → P⊨⇛ind□Q _) › ⤇ᴱ-join) ›
    ⤇ᴱ-eatʳ › ⤇ᴱ-mono (λ _ → ∗ᵒ-assocˡ › ∗ᵒ-monoʳ ∗ᵒ-comm) › ⤇ᴱ-param

  -- Monotonicity of ⊨⇛ind

  ⊨⇛ind-mono✓ˡ :  Pᵒ ⊨✓ Qᵒ →  Qᵒ ⊨⇛ind Rᵒ →  Pᵒ ⊨⇛ind Rᵒ
  ⊨⇛ind-mono✓ˡ P⊨✓Q Q⊨⇛indR _ ✓∙ =  ∗ᵒ-mono✓ˡ P⊨✓Q ✓∙ › Q⊨⇛indR _ ✓∙

  ⊨⇛ind-monoˡ :  Pᵒ ⊨ Qᵒ →  Qᵒ ⊨⇛ind Rᵒ →  Pᵒ ⊨⇛ind Rᵒ
  ⊨⇛ind-monoˡ =  ⊨⇒⊨✓ › ⊨⇛ind-mono✓ˡ

  ⊨⇛ind-mono✓ʳ :  Pᵒ ⊨✓ Qᵒ →  Rᵒ ⊨⇛ind Pᵒ →  Rᵒ ⊨⇛ind Qᵒ
  ⊨⇛ind-mono✓ʳ P⊨✓Q R⊨⇛indP _ ✓∙ =  R⊨⇛indP _ ✓∙ ›
    ⤇ᴱ-mono✓ λ _ ✓∙ → ∗ᵒ-mono✓ˡ P⊨✓Q ✓∙

  ⊨⇛ind-monoʳ :  Pᵒ ⊨ Qᵒ →  Rᵒ ⊨⇛ind Pᵒ →  Rᵒ ⊨⇛ind Qᵒ
  ⊨⇛ind-monoʳ =  ⊨⇒⊨✓ › ⊨⇛ind-mono✓ʳ

  ⊨⇛ind-mono :  Pᵒ ⊨ Qᵒ →  Rᵒ ⊨ Sᵒ →  Qᵒ ⊨⇛ind Rᵒ →  Pᵒ ⊨⇛ind Sᵒ
  ⊨⇛ind-mono P⊨Q R⊨S =  ⊨⇛ind-monoˡ P⊨Q › ⊨⇛ind-monoʳ R⊨S

  -- Frame on ⊨⇛ind

  ⊨⇛ind-frameˡ :  Pᵒ ⊨⇛ind Qᵒ →  Rᵒ ∗ᵒ Pᵒ ⊨⇛ind Rᵒ ∗ᵒ Qᵒ
  ⊨⇛ind-frameˡ P⊨⇛indQ _ ✓∙ =  ∗ᵒ-assocˡ › ∗ᵒ-mono✓ʳ (P⊨⇛indQ _) ✓∙ › ⤇ᴱ-eatˡ ›
    ⤇ᴱ-mono λ _ → ∗ᵒ-assocʳ

  -- ∃ᵒ/∃ᴵ on ⊨⇛ind

  ⊨⇛ind-∃ᵒ :  (∀ x → Pᵒ˙ x ⊨⇛ind Qᵒ) →  ∃ᵒ˙ Pᵒ˙ ⊨⇛ind Qᵒ
  ⊨⇛ind-∃ᵒ Px⊨⇛indQ _ ✓a =  ∃ᵒ∗ᵒ-out › ∑-case λ _ → Px⊨⇛indQ _ _ ✓a

  ⊨⇛ind-∃ᴵ :  (∀{{x}} → Pᵒ˙ x ⊨⇛ind Qᵒ) →  ∃ᴵ˙ Pᵒ˙ ⊨⇛ind Qᵒ
  ⊨⇛ind-∃ᴵ Px⊨⇛indQ _ ✓a =  ∃ᴵ∗ᵒ-out › ∑ᴵ-case $ Px⊨⇛indQ _ ✓a

  -- Allocate P to get Ind P

  Ind-alloc :  ⸨ P ⸩  ⊨⇛ind  Ind P
  Ind-alloc =  ⊨⇛indˣ⇒⊨⇛ind Indˣ-alloc ▷ ⊨⇛ind-monoʳ inj₀

  -- Allocate □ P to get □ᵒ Ind P

  □ᵒInd-alloc-rec :  □ᵒ Ind P -∗ᵒ □ᵒ ⸨ P ⸩  ⊨⇛ind  □ᵒ Ind P
  □ᵒInd-alloc-rec {P} =  ⊨⇛ind□⇒⊨⇛ind □ᵒInd□-alloc-rec ▷
    ⊨⇛ind-mono (-∗ᵒ-monoˡ inj₁) inj₁

  -- Consume Ind P to get P

  Ind-use :  Ind P  ⊨⇛ind  ⸨ P ⸩
  Ind-use _ ✓a =  ⊎ᵒ∗ᵒ-out ›
    ⊎-case (⊨⇛indˣ⇒⊨⇛ind Indˣ-use _ ✓a) (⊨⇛ind□⇒⊨⇛ind Ind□-use _ ✓a)

--------------------------------------------------------------------------------
-- On ○ᵒ

abstract

  Ind⇒○ᵒ :  Ind P ⊨ ○ᵒ P
  Ind⇒○ᵒ IndPa =  ⊤' , -ᴵ, -, ∗-elimʳ , ?∗ᵒ-intro absurd IndPa

  ○ᵒ-alloc :  ⸨ P ⸩ ⊨⇛ind ○ᵒ P
  ○ᵒ-alloc =  Ind-alloc ▷ ⊨⇛ind-monoʳ Ind⇒○ᵒ

  □ᵒ○ᵒ-alloc-rec :  □ᵒ ○ᵒ P -∗ᵒ □ᵒ ⸨ P ⸩  ⊨⇛ind  □ᵒ ○ᵒ P
  □ᵒ○ᵒ-alloc-rec {P} =  □ᵒInd-alloc-rec ▷ ⊨⇛ind-mono (-∗ᵒ-monoˡ Ind⇒○ᵒ) Ind⇒○ᵒ

  ○ᵒ-use :  ○ᵒ P  ⊨⇛ind  ⸨ P ⸩
  ○ᵒ-use =  ⊨⇛ind-∃ᵒ λ Q → ⊨⇛ind-∃ᴵ $ ⊨⇛ind-∃ᵒ λ _ → ⊨⇛ind-∃ᵒ λ Q∗R⊢P →
    Ind-use ▷ ⊨⇛ind-frameˡ ▷
    ⊨⇛ind-mono✓ʳ λ ✓∙ → ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {Q}) › ⊢⇒⊨✓ Q∗R⊢P ✓∙

--------------------------------------------------------------------------------
-- On ↪⇛ᵒ, ↪⟨ ⟩ᴾᵒ, and ↪⟨ ⟩ᵀᵒ

  ↪⇛ᵒ-use :  P ↪[ i ]⇛ᵒ Q  ⊨⇛ind  ∃ᵒ R , ∃ᵒ _ ∈ (P ∗ R ⊢[ ∞ ][ i ]⇛ Q) , ⸨ R ⸩
  ↪⇛ᵒ-use =  ⊨⇛ind-∃ᵒ λ S → ⊨⇛ind-∃ᴵ $ ⊨⇛ind-∃ᵒ λ _ → ⊨⇛ind-∃ᵒ λ P∗S∗T⊢⇛Q →
    Ind-use ▷ ⊨⇛ind-frameˡ ▷
    ⊨⇛ind-monoʳ (∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {S}) › (P∗S∗T⊢⇛Q ,_) › -,_)

  ↪⟨⟩ᴾᵒ-use :  P ↪⟨ e ⟩ᴾᵒ Q˙  ⊨⇛ind
                 ∃ᵒ R , ∃ᵒ _ ∈ (P ∗ R ⊢[ ∞ ]⟨ e ⟩ᴾ Q˙) , ⸨ R ⸩
  ↪⟨⟩ᴾᵒ-use =  ⊨⇛ind-∃ᵒ λ S → ⊨⇛ind-∃ᴵ $ ⊨⇛ind-∃ᵒ λ _ → ⊨⇛ind-∃ᵒ λ P∗S∗T⊢⟨e⟩Q →
    Ind-use ▷ ⊨⇛ind-frameˡ ▷
    ⊨⇛ind-monoʳ (∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {S}) › (P∗S∗T⊢⟨e⟩Q ,_) › -,_)

  ↪⟨⟩ᵀᵒ-use :  P ↪⟨ e ⟩ᵀ[ i ]ᵒ Q˙  ⊨⇛ind
                 ∃ᵒ R , ∃ᵒ _ ∈ (P ∗ R ⊢[ ∞ ]⟨ e ⟩ᵀ[ i ] Q˙) , ⸨ R ⸩
  ↪⟨⟩ᵀᵒ-use =  ⊨⇛ind-∃ᵒ λ S → ⊨⇛ind-∃ᴵ $ ⊨⇛ind-∃ᵒ λ _ → ⊨⇛ind-∃ᵒ λ P∗S∗T⊢⟨e⟩Q →
    Ind-use ▷ ⊨⇛ind-frameˡ ▷
    ⊨⇛ind-monoʳ (∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {S}) › (P∗S∗T⊢⟨e⟩Q ,_) › -,_)
