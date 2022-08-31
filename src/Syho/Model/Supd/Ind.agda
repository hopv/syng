--------------------------------------------------------------------------------
-- Super update on ○, ↪⇛, ↪⟨ ⟩ᴾ, and ↪⟨ ⟩ᵀ
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Ind where

open import Base.Level using (2ᴸ)
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
  use-ind□; Env-indˣ; Env-ind□)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ; Envᴳ; updᴱᴳ; indˣ; ind□)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨_; ⊤ᵒ; _∗ᵒ_; _⤇ᴱ_; □ᵒ_;
  ∗ᵒ-Mono; ∗ᵒ-mono; ∗ᵒ-monoˡ; ∗ᵒ-monoʳ; ∗ᵒ-elimˡ; ∗ᵒ-elimʳ; ?∗ᵒ-intro; pullʳˡᵒ;
  ∃ᵒ∗ᵒ-elim; ⤇ᴱ-mono; ⤇ᴱ-param; ⤇ᴱ-eatʳ; □ᵒ-Mono; □ᵒ-mono; □ᵒ-elim; dup-□ᵒ;
  □ᵒ-∗ᵒ-in; ●-injᴳ-⌞⌟≡-□ᵒ; ↝-●-injᴳ-⤇ᴱ; ε↝-●-injᴳ-⤇ᴱ)
open import Syho.Model.Prop.Ind using (Indˣ; Ind□)
open import Syho.Model.Prop.Interp using (⸨_⸩; ⸨⸩-Mono)

private variable
  i j m n :  ℕ
  P :  Prop' ∞
  P˙ Q˙ :  ℕ → Prop' ∞
  E :  Envᴳ

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
-- Invariant for the exclusive indirection ERA

Inv-indˣ :  Env-indˣ →  Propᵒ 2ᴸ
Inv-indˣ Eˣ =  ⸨ Eˣ ⸩ᴺᴹ

abstract

  -- Allocate P to get Indˣ P

  alloc-Indˣ :  ⸨ P ⸩ ∗ᵒ Inv-indˣ (E indˣ)  ⊨
                  E ⤇ᴱ λ Fˣ → (updᴱᴳ indˣ Fˣ E , Indˣ P ∗ᵒ Inv-indˣ Fˣ)
  alloc-Indˣ {E = E} =  let (_ , n) = E indˣ in
    ?∗ᵒ-intro (ε↝-●-injᴳ-⤇ᴱ alloc-indˣ) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ _ → ∗ᵒ-mono (_ ,_) $ ⸨⸩ᴺᴹ-add {n = n}) › ⤇ᴱ-param

  -- Consume Indˣ P to get P

  use-Indˣ :  Indˣ P ∗ᵒ Inv-indˣ (E indˣ)  ⊨
                E ⤇ᴱ λ Fˣ → (updᴱᴳ indˣ Fˣ E , ⸨ P ⸩ ∗ᵒ Inv-indˣ Fˣ)
  use-Indˣ {E = E} =  let (_ , n) = E indˣ in
    ∃ᵒ∗ᵒ-elim λ _ → ∗ᵒ-monoˡ (↝-●-injᴳ-⤇ᴱ use-indˣ) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ{ (refl , i<n) → ∗ᵒ-elimʳ (⸨⸩ᴺᴹ-Mono {n = n}) › ⸨⸩ᴺᴹ-rem-< i<n })
    › ⤇ᴱ-param

--------------------------------------------------------------------------------
-- Invariant for the persistent indirection ERA

Inv-ind□ :  Env-ind□ →  Propᵒ 2ᴸ
Inv-ind□ E□ =  □ᵒ ⸨ E□ ⸩ᴺᴹ

abstract

  -- Allocate □ P to get □ᵒ Ind□ P

  alloc-Ind□ :  □ᵒ ⸨ P ⸩ ∗ᵒ Inv-ind□ (E ind□)  ⊨
                  E ⤇ᴱ λ F□ → (updᴱᴳ ind□ F□ E , □ᵒ Ind□ P ∗ᵒ Inv-ind□ F□)
  alloc-Ind□ {P} {E} =  let (_ , n) = E ind□ in
    □ᵒ-∗ᵒ-in › ?∗ᵒ-intro (ε↝-●-injᴳ-⤇ᴱ alloc-ind□) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ _ → ∗ᵒ-mono (●-injᴳ-⌞⌟≡-□ᵒ refl › (_ ,_)) $
      □ᵒ-mono {Pᵒ = _ ∗ᵒ _} $ ⸨⸩ᴺᴹ-add {P} {n = n}) › ⤇ᴱ-param

  -- Use Ind□ P to get P

  use-Ind□ :  Ind□ P ∗ᵒ Inv-ind□ (E ind□)  ⊨
                E ⤇ᴱ λ F□ → (updᴱᴳ ind□ F□ E , ⸨ P ⸩ ∗ᵒ Inv-ind□ F□)
  use-Ind□ {P} {E} =  let (_ , n) = E ind□ in
    ∃ᵒ∗ᵒ-elim λ _ → ∗ᵒ-monoˡ (↝-●-injᴳ-⤇ᴱ use-ind□) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ{ (refl , i<n) → ∗ᵒ-elimʳ (□ᵒ-Mono $ ⸨⸩ᴺᴹ-Mono {n = n}) ›
      dup-□ᵒ (⸨⸩ᴺᴹ-Mono {n = n}) › ∗ᵒ-monoˡ $ □ᵒ-elim (⸨⸩ᴺᴹ-Mono {n = n}) ›
      ⸨⸩ᴺᴹ-rem-< i<n › ∗ᵒ-elimˡ (⸨⸩-Mono {P}) }) › ⤇ᴱ-param
