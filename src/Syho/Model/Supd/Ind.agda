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
open import Base.Prod using (_×_; _,_; -,_; -ᴵ,_; ∑-case; ∑ᴵ-case; uncurry)
open import Base.Sum using (ĩ₀_; ĩ₁_; ⊎-case)
open import Base.Option using (¿_; š_; ň)
open import Base.Dec using (yes; no; _≡?_; ≡?-refl; upd˙; upd˙²; upd˙-self)
open import Base.Nat using (ℕ; ṡ_; _≥_; _<_; _<ᵈ_; ≤-refl; <⇒≤; <-irrefl;
  ≤ᵈ-refl; ≤ᵈṡ; ≤ᵈ⇒≤; ≤⇒≤ᵈ)
open import Syho.Lang.Expr using (Type; Expr)
open import Syho.Logic.Prop using (Prop'; _∗_)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_)
open import Syho.Logic.Hor using (_⊢[_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ[_]_)
open import Syho.Model.ERA.Ind using (alloc-indˣ; use-indˣ; alloc-ind□;
  use-ind□; Env-indˣ; Env-ind□; Env-ind)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ; Envᴳ; indˣ; ind□)
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
  Q˙ :  X →  Prop' ∞
  Pˇ˙ Qˇ˙ :  X →  ¿ Prop' ∞
  Pˇ :  ¿ Prop' ∞
  Pᵒ Qᵒ Rᵒ Sᵒ :  Propᵒ ł
  Pᵒ˙ :  X → Propᵒ ł
  T :  Type
  e :  Expr ∞ T
  E :  Envᴳ

--------------------------------------------------------------------------------
-- Interpret a map ℕ → ¿ Prop' ∞ with a bound

Invᴺᵐ :  (ℕ → ¿ Prop' ∞) →  ℕ →  Propᵒ 2ᴸ
Invᴺᵐ Pˇ˙ 0 =  ⊤ᵒ
Invᴺᵐ Pˇ˙ (ṡ n)  with Pˇ˙ n
… | ň =  Invᴺᵐ Pˇ˙ n
… | š Q =  ⸨ Q ⸩ ∗ᵒ Invᴺᵐ Pˇ˙ n

abstract
  -- Monoᵒ for ⸨ ⸩ᴺᵐ

  Invᴺᵐ-Mono :  Monoᵒ (Invᴺᵐ Pˇ˙ n)
  Invᴺᵐ-Mono {n = 0} =  _
  Invᴺᵐ-Mono {Pˇ˙} {n = ṡ n'}  with Pˇ˙ n'
  … | ň =  Invᴺᵐ-Mono {n = n'}
  … | š _ =  ∗ᵒ-Mono

  -- Update an element out of the bound

  Invᴺᵐ-⇒upd-≥ :  i ≥ n →  Invᴺᵐ Qˇ˙ n  ⊨  Invᴺᵐ (upd˙ i Pˇ Qˇ˙) n
  Invᴺᵐ-⇒upd-≥ {_} {0} =  _
  Invᴺᵐ-⇒upd-≥ {i} {ṡ n'} {Qˇ˙} i>n'  with n' ≡? i
  … | yes refl =  absurd $ <-irrefl i>n'
  … | no _  with Qˇ˙ n'
  …   | š _ =  ∗ᵒ-monoʳ $ Invᴺᵐ-⇒upd-≥ $ <⇒≤ i>n'
  …   | ň =  Invᴺᵐ-⇒upd-≥ $ <⇒≤ i>n'

  -- Add a proposition at the bound

  Invᴺᵐ-add-š :  ⸨ P ⸩ ∗ᵒ Invᴺᵐ Qˇ˙ n  ⊨  Invᴺᵐ (upd˙ n (š P) Qˇ˙) (ṡ n)
  Invᴺᵐ-add-š {n = n}  rewrite ≡?-refl {a = n} =
    ∗ᵒ-monoʳ $ Invᴺᵐ-⇒upd-≥ $ ≤-refl {n}

  Invᴺᵐ-add-ň :  Invᴺᵐ Pˇ˙ n  ⊨  Invᴺᵐ (upd˙ n ň Pˇ˙) (ṡ n)
  Invᴺᵐ-add-ň {n = n}  rewrite ≡?-refl {a = n} =  Invᴺᵐ-⇒upd-≥ $ ≤-refl {n}

  -- Remove an element within the bound to get the element's interpretation

  Invᴺᵐ-rem-<ᵈ :  Pˇ˙ i ≡ š Q →  i <ᵈ n →
    Invᴺᵐ Pˇ˙ n  ⊨  ⸨ Q ⸩ ∗ᵒ Invᴺᵐ (upd˙ i ň Pˇ˙) n
  Invᴺᵐ-rem-<ᵈ {i = i} Pˇi≡šQ ≤ᵈ-refl  rewrite Pˇi≡šQ =
    ∗ᵒ-monoʳ (Invᴺᵐ-add-ň {n = i})
  Invᴺᵐ-rem-<ᵈ {Pˇ˙} {i} Pˇi≡šQ (≤ᵈṡ {n = n'} i<ᵈn')  with n' ≡? i
  … | yes refl =  absurd $ <-irrefl $ ≤ᵈ⇒≤ i<ᵈn'
  … | no _  with Pˇ˙ n'
  …   | ň =  Invᴺᵐ-rem-<ᵈ Pˇi≡šQ i<ᵈn'
  …   | š _ =  ∗ᵒ-monoʳ (Invᴺᵐ-rem-<ᵈ Pˇi≡šQ i<ᵈn') › pullʳˡᵒ

  Invᴺᵐ-rem-< :  Pˇ˙ i ≡ š Q →  i < n →
    Invᴺᵐ Pˇ˙ n  ⊨  ⸨ Q ⸩ ∗ᵒ Invᴺᵐ (upd˙ i ň Pˇ˙) n
  Invᴺᵐ-rem-< Pˇi≡šQ =  Invᴺᵐ-rem-<ᵈ Pˇi≡šQ ∘ ≤⇒≤ᵈ

--------------------------------------------------------------------------------
-- On Indˣᴱᴿᴬ

-- Invariant for Indˣᴱᴿᴬ

Inv-indˣ :  Env-indˣ →  Propᵒ 2ᴸ
Inv-indˣ =  uncurry Invᴺᵐ

-- Super update on Indˣᴱᴿᴬ

infix 8 ⇛indˣ_
⇛indˣ_ :  Propᵒ ł →  Propᵒ (2ᴸ ⊔ᴸ ł)
⇛indˣ Pᵒ =  [ (λ E → E indˣ) , upd˙ indˣ , Inv-indˣ ]⇛ᵍ Pᵒ

abstract

  -- Allocate P to get Indˣ P

  Indˣ-alloc :  ⸨ P ⸩  ⊨  ⇛indˣ  Indˣ P
  Indˣ-alloc =  ⇛ᵍ-make λ E _ → let (_ , n) = E indˣ in
    ?∗ᵒ-intro (ε↝-●-injᴳ-⤇ᴱ alloc-indˣ) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ _ → ∗ᵒ-mono (_ ,_) $ Invᴺᵐ-add-š {n = n}) › ⤇ᴱ-param

  -- Consume Indˣ P to get P

  Indˣ-use :  Indˣ P  ⊨  ⇛indˣ  ⸨ P ⸩
  Indˣ-use =  ⇛ᵍ-make λ E _ → let (_ , n) = E indˣ in
    ∃ᵒ∗ᵒ-out › ∑-case λ _ → ∗ᵒ-monoˡ (↝-●-injᴳ-⤇ᴱ use-indˣ) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ{ (≡šP , i<n) →
      ∗ᵒ-elimʳ (Invᴺᵐ-Mono {n = n}) › Invᴺᵐ-rem-< ≡šP i<n }) › ⤇ᴱ-param

--------------------------------------------------------------------------------
-- On Ind□ᴱᴿᴬ

-- Invariant for Ind□ᴱᴿᴬ

Inv-ind□ :  Env-ind□ →  Propᵒ 2ᴸ
Inv-ind□ =  □ᵒ_ ∘ uncurry Invᴺᵐ

-- Super update on Ind□ᴱᴿᴬ

infix 8 ⇛ind□_
⇛ind□_ :  Propᵒ ł →  Propᵒ (2ᴸ ⊔ᴸ ł)
⇛ind□ Pᵒ =  [ (λ E → E ind□) , upd˙ ind□ , Inv-ind□ ]⇛ᵍ Pᵒ

abstract

  -- Allocate □ P to get □ᵒ Ind□ P

  □ᵒInd□-alloc-rec :  □ᵒ Ind□ P -∗ᵒ □ᵒ ⸨ P ⸩  ⊨  ⇛ind□  □ᵒ Ind□ P
  □ᵒInd□-alloc-rec {P} =  ⇛ᵍ-make λ E _ → let (_ , n) = E ind□ in
    ?∗ᵒ-intro (ε↝-●-injᴳ-⤇ᴱ alloc-ind□) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono✓ (λ _ ✓∙ →
      ∗ᵒ-monoˡ (●-injᴳ-⌞⌟≡-□ᵒ refl › dup-□ᵒ ●-Mono › ∗ᵒ-mono (_ ,_) (_ ,_)) ›
      ∗ᵒ-assocˡ › ∗ᵒ-mono✓ʳ (λ ✓∙ → ∗ᵒ-assocʳ ›
        ∗ᵒ-mono✓ˡ (-∗ᵒ-apply $ □ᵒ-Mono $ ⸨⸩-Mono {P}) ✓∙ › □ᵒ-∗ᵒ-in ›
        Invᴺᵐ-add-š {P} {n = n}) ✓∙) › ⤇ᴱ-param

  -- Use Ind□ P to get P

  Ind□-use :  Ind□ P  ⊨  ⇛ind□  ⸨ P ⸩
  Ind□-use {P} =  ⇛ᵍ-make λ E _ → let (_ , n) = E ind□ in
    ∃ᵒ∗ᵒ-out › ∑-case λ _ → ∗ᵒ-monoˡ (↝-●-injᴳ-⤇ᴱ use-ind□) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ{ (≡šP , i<n) → ∗ᵒ-elimʳ (□ᵒ-Mono $ Invᴺᵐ-Mono {n = n}) ›
      dup-□ᵒ (Invᴺᵐ-Mono {n = n}) › ∗ᵒ-monoˡ $ □ᵒ-elim (Invᴺᵐ-Mono {n = n}) ›
      Invᴺᵐ-rem-< ≡šP i<n › ∗ᵒ-elimˡ (⸨⸩-Mono {P}) }) › ⤇ᴱ-param

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
updᴱ-ind (Fˣ , F□) =  upd˙² indˣ Fˣ ind□ F□

-- Super update for Indˣᴱᴿᴬ and Ind□ᴱᴿᴬ

infix 8 ⇛ind_
⇛ind_ :  Propᵒ ł →  Propᵒ (2ᴸ ⊔ᴸ ł)
⇛ind Pᵒ =  [ env-ind , updᴱ-ind , Inv-ind ]⇛ᵍ Pᵒ

private variable
  Fˣ□ Gˣ□ :  Env-ind

abstract

  -- ⇛indˣ into ⇛ind

  ⇛indˣ⇒⇛ind :  ⇛indˣ Pᵒ  ⊨  ⇛ind Pᵒ
  ⇛indˣ⇒⇛ind =  ⇛ᵍ-mono (⇛ᵍ-intro {set = upd˙ ind□} upd˙-self) › ⇛ᵍ-join2 refl

  -- ⊨⇛ind□ into ⊨⇛ind

  ⇛ind□⇒⇛ind :  ⇛ind□ Pᵒ  ⊨  ⇛ind Pᵒ
  ⇛ind□⇒⇛ind =  ⇛ᵍ-intro {set = upd˙ indˣ} upd˙-self › ⇛ᵍ-join2 refl

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
