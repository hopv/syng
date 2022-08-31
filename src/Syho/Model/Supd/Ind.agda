--------------------------------------------------------------------------------
-- Super update on Ind, ○ᵒ, ↪⇛ᵒ, ↪⟨ ⟩ᴾᵒ, and ↪⟨ ⟩ᵀᵒ
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Ind where

open import Base.Level using (Level; _⊔ᴸ_; 2ᴸ)
open import Base.Size using (∞)
open import Base.Func using (_$_; _›_; _∘_; id)
open import Base.Few using (absurd)
open import Base.Eq using (_≡_; refl)
open import Base.Prod using (_×_; _,_)
open import Base.Sum using (inj₀; inj₁)
open import Base.Bool using (tt; ff)
open import Base.Nat using (ℕ; suc; _≥_; _<_; _<ᵈ_; _≡ᵇ_; ≤-refl; <⇒≤; <-irrefl;
  ≤ᵈ-refl; ≤ᵈsuc; ≤ᵈ⇒≤; ≤⇒≤ᵈ; ᵇ⇒≡; ≡ᵇ-refl; ≢-≡ᵇ-ff)
open import Base.Nmap using (updᴺᴹ)
open import Syho.Logic.Prop using (Prop'; ⊤')
open import Syho.Model.ERA.Ind using (alloc-indˣ; use-indˣ; alloc-ind□;
  use-ind□; Env-indˣ; Env-ind□; Env-ind)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ; Envᴳ; updᴱᴳ; indˣ; ind□)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨_; _⊨✓_; ⊤ᵒ; _∗ᵒ_;
  _-∗ᵒ_; _⤇ᴱ_; □ᵒ_; ∗ᵒ-Mono; ∗ᵒ-mono; ∗ᵒ-monoˡ; ∗ᵒ-monoʳ; ∗ᵒ-mono✓ˡ; ∗ᵒ-mono✓ʳ;
  ∗ᵒ-comm; ∗ᵒ-assocˡ; ∗ᵒ-assocʳ; pullʳˡᵒ; ∗ᵒ-elimˡ; ∗ᵒ-elimʳ; ?∗ᵒ-intro;
  ∃ᵒ∗ᵒ-elim; ⊎ᵒ∗ᵒ-elim✓; -∗ᵒ-monoˡ; -∗ᵒ-apply; ⤇ᴱ-mono; ⤇ᴱ-mono✓; ⤇ᴱ-param;
  ⤇ᴱ-join; ⤇ᴱ-eatʳ; ⤇ᴱ-updᴱᴳ-self-intro; □ᵒ-Mono; □ᵒ-mono; □ᵒ-elim; dup-□ᵒ;
  □ᵒ-∗ᵒ-in; ●-Mono; ●-injᴳ-⌞⌟≡-□ᵒ; ↝-●-injᴳ-⤇ᴱ; ε↝-●-injᴳ-⤇ᴱ)
open import Syho.Model.Prop.Ind using (Indˣ; Ind□; Ind)
open import Syho.Model.Prop.Interp using (⸨_⸩; ⸨⸩-Mono)

private variable
  ł ł' :  Level
  i j m n :  ℕ
  P :  Prop' ∞
  P˙ Q˙ :  ℕ → Prop' ∞
  Pᵒ Qᵒ Rᵒ :  Propᵒ ł

--------------------------------------------------------------------------------
-- Interpret a map ℕ → Prop' ∞ with a bound

⸨_⸩ᴺᴹ :  (ℕ → Prop' ∞) × ℕ →  Propᵒ 2ᴸ
⸨ P˙ , 0 ⸩ᴺᴹ =  ⊤ᵒ
⸨ P˙ , suc n ⸩ᴺᴹ =  ⸨ P˙ n ⸩ ∗ᵒ ⸨ P˙ , n ⸩ᴺᴹ

abstract

  -- Monoᵒ for ⸨ ⸩ᴺᴹ

  ⸨⸩ᴺᴹ-Mono :  Monoᵒ ⸨ P˙ , n ⸩ᴺᴹ
  ⸨⸩ᴺᴹ-Mono {n = 0} =  _
  ⸨⸩ᴺᴹ-Mono {n = suc _} =  ∗ᵒ-Mono

  -- Update an element out of the bound

  ⸨⸩ᴺᴹ-⇒upd-≥ :  i ≥ n →  ⸨ Q˙ , n ⸩ᴺᴹ  ⊨ ⸨ updᴺᴹ i P Q˙ , n ⸩ᴺᴹ
  ⸨⸩ᴺᴹ-⇒upd-≥ {_} {0} =  _
  ⸨⸩ᴺᴹ-⇒upd-≥ {i} {suc n'} i>n'  with n' ≡ᵇ i | ᵇ⇒≡ {n'} {i}
  … | tt | ⇒n'≡i  rewrite ⇒n'≡i _ =  absurd $ <-irrefl i>n'
  … | ff | _ =  ∗ᵒ-monoʳ $ ⸨⸩ᴺᴹ-⇒upd-≥ $ <⇒≤ i>n'

  -- Add a proposition at the bound

  ⸨⸩ᴺᴹ-add :  ⸨ P ⸩ ∗ᵒ ⸨ Q˙ , n ⸩ᴺᴹ  ⊨ ⸨ updᴺᴹ n P Q˙ , suc n ⸩ᴺᴹ
  ⸨⸩ᴺᴹ-add {n = n}  rewrite ≡ᵇ-refl {n} =  ∗ᵒ-monoʳ $ ⸨⸩ᴺᴹ-⇒upd-≥ $ ≤-refl {n}

  ⸨⸩ᴺᴹ-add⊤ :  ⸨ P˙ , n ⸩ᴺᴹ  ⊨  ⸨ updᴺᴹ n ⊤' P˙ , suc n ⸩ᴺᴹ
  ⸨⸩ᴺᴹ-add⊤ {n = n} =  ?∗ᵒ-intro absurd › ⸨⸩ᴺᴹ-add {n = n}

  -- Remove an element within the bound to get the element's interpretation

  ⸨⸩ᴺᴹ-rem-<ᵈ :  i <ᵈ n →  ⸨ P˙ , n ⸩ᴺᴹ ⊨ ⸨ P˙ i ⸩ ∗ᵒ ⸨ updᴺᴹ i ⊤' P˙ , n ⸩ᴺᴹ
  ⸨⸩ᴺᴹ-rem-<ᵈ {i} ≤ᵈ-refl =  ∗ᵒ-monoʳ (⸨⸩ᴺᴹ-add⊤ {n = i})
  ⸨⸩ᴺᴹ-rem-<ᵈ {i} (≤ᵈsuc {n = n'} i<ᵈn')
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

  alloc-Indˣ :  ⸨ P ⸩  ⊨⇛indˣ  Indˣ P
  alloc-Indˣ E _ =  let (_ , n) = E indˣ in
    ?∗ᵒ-intro (ε↝-●-injᴳ-⤇ᴱ alloc-indˣ) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ _ → ∗ᵒ-mono (_ ,_) $ ⸨⸩ᴺᴹ-add {n = n}) › ⤇ᴱ-param

  -- Consume Indˣ P to get P

  use-Indˣ :  Indˣ P  ⊨⇛indˣ  ⸨ P ⸩
  use-Indˣ E _ =  let (_ , n) = E indˣ in
    ∃ᵒ∗ᵒ-elim λ _ → ∗ᵒ-monoˡ (↝-●-injᴳ-⤇ᴱ use-indˣ) › ⤇ᴱ-eatʳ ›
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

  alloc-rec-□Ind□ :  □ᵒ Ind□ P -∗ᵒ □ᵒ ⸨ P ⸩  ⊨⇛ind□  □ᵒ Ind□ P
  alloc-rec-□Ind□ {P} E _ =  let (_ , n) = E ind□ in
    ?∗ᵒ-intro (ε↝-●-injᴳ-⤇ᴱ alloc-ind□) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono✓ (λ _ ✓a →
      ∗ᵒ-monoˡ (●-injᴳ-⌞⌟≡-□ᵒ refl › dup-□ᵒ ●-Mono › ∗ᵒ-mono (_ ,_) (_ ,_)) ›
      ∗ᵒ-assocˡ › ∗ᵒ-mono✓ʳ (λ ✓b → ∗ᵒ-assocʳ ›
        ∗ᵒ-mono✓ˡ (-∗ᵒ-apply $ □ᵒ-Mono $ ⸨⸩-Mono {P}) ✓b › □ᵒ-∗ᵒ-in ›
        □ᵒ-mono {Pᵒ = _ ∗ᵒ _} $ ⸨⸩ᴺᴹ-add {P} {n = n}) ✓a) › ⤇ᴱ-param

  -- Use Ind□ P to get P

  use-Ind□ :  Ind□ P  ⊨⇛ind□  ⸨ P ⸩
  use-Ind□ {P} E _ =  let (_ , n) = E ind□ in
    ∃ᵒ∗ᵒ-elim λ _ → ∗ᵒ-monoˡ (↝-●-injᴳ-⤇ᴱ use-ind□) › ⤇ᴱ-eatʳ ›
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
  ⊨⇛indˣ⇒⊨⇛ind P⊨⇛indˣQ _ ✓a =  ∗ᵒ-assocʳ › ∗ᵒ-mono✓ˡ (P⊨⇛indˣQ _) ✓a › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ _ → ∗ᵒ-assocˡ › ⤇ᴱ-updᴱᴳ-self-intro) › ⤇ᴱ-join › ⤇ᴱ-param

  -- ⊨⇛ind□ into ⊨⇛ind

  ⊨⇛ind□⇒⊨⇛ind :  Pᵒ ⊨⇛ind□ Qᵒ →  Pᵒ ⊨⇛ind Qᵒ
  ⊨⇛ind□⇒⊨⇛ind P⊨⇛ind□Q _ _ =  ∗ᵒ-monoʳ ∗ᵒ-comm › ∗ᵒ-assocʳ ›
    ∗ᵒ-monoˡ (⤇ᴱ-updᴱᴳ-self-intro › ⤇ᴱ-mono✓ (λ _ → P⊨⇛ind□Q _) › ⤇ᴱ-join) ›
    ⤇ᴱ-eatʳ › ⤇ᴱ-mono (λ _ → ∗ᵒ-assocˡ › ∗ᵒ-monoʳ ∗ᵒ-comm) › ⤇ᴱ-param

  -- Monotonicity of ⊨⇛ind

  ⊨⇛ind-mono :  Pᵒ ⊨ Qᵒ →  Rᵒ ⊨⇛ind Pᵒ →  Rᵒ ⊨⇛ind Qᵒ
  ⊨⇛ind-mono P⊨Q R⊨⇛indP _ ✓a =  R⊨⇛indP _ ✓a › ⤇ᴱ-mono λ _ → ∗ᵒ-monoˡ P⊨Q

  -- Allocate P to get Ind P

  alloc-Ind :  ⸨ P ⸩  ⊨⇛ind  Ind P
  alloc-Ind =  ⊨⇛ind-mono inj₀ $ ⊨⇛indˣ⇒⊨⇛ind alloc-Indˣ

  -- Allocate □ P to get □ᵒ Ind P

  alloc-rec-□Ind :  □ᵒ Ind P -∗ᵒ □ᵒ ⸨ P ⸩  ⊨⇛ind  □ᵒ Ind P
  alloc-rec-□Ind {P} E ✓a =
    ∗ᵒ-monoˡ (-∗ᵒ-monoˡ {Qᵒ = □ᵒ ⸨ P ⸩} $ □ᵒ-mono {Qᵒ = Ind P} inj₁) ›
    ⊨⇛ind-mono inj₁ (⊨⇛ind□⇒⊨⇛ind alloc-rec-□Ind□) E ✓a

  -- Consume Ind P to get P

  use-Ind :  Ind P  ⊨⇛ind  ⸨ P ⸩
  use-Ind _ =  ⊎ᵒ∗ᵒ-elim✓ (⊨⇛indˣ⇒⊨⇛ind use-Indˣ _) (⊨⇛ind□⇒⊨⇛ind use-Ind□ _)
