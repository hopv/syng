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
open import Base.Nmap using (updⁿᵐ)
open import Syho.Logic.Prop using (Prop'; ⊤')
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Ind using (add-indˣ; rem-indˣ)
open import Syho.Model.ERA.Glob using (updᴱᴳ; indˣ; Globᴱᴿᴬ)
open ERA Globᴱᴿᴬ using (Env)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨_; ⊤ᵒ; _∗ᵒ_; □ᵒ_; _⤇ᴱ_;
  ∗ᵒ-Mono; ∗ᵒ-mono; ∗ᵒ-monoˡ; ∗ᵒ-monoʳ; ∗ᵒ-elimʳ; ?∗ᵒ-intro; pullʳˡᵒ; ∃ᵒ∗ᵒ-elim;
  ⤇ᴱ-mono; ⤇ᴱ-param; ⤇ᴱ-eatʳ; ↝-●-injᴳ-⤇ᴱ; ε↝-●-injᴳ-⤇ᴱ)
open import Syho.Model.Prop.Ind using (Indˣ)
open import Syho.Model.Prop.Interp using (⸨_⸩)

private variable
  i j m n :  ℕ
  P :  Prop' ∞
  P˙ Q˙ :  ℕ → Prop' ∞
  E :  Env

--------------------------------------------------------------------------------
-- Interpret a map ℕ → Prop' ∞ with a bound

⸨_⸩ⁿᵐ :  (ℕ → Prop' ∞) × ℕ →  Propᵒ 2ᴸ
⸨ P˙ , 0 ⸩ⁿᵐ =  ⊤ᵒ
⸨ P˙ , suc n ⸩ⁿᵐ =  ⸨ P˙ n ⸩ ∗ᵒ ⸨ P˙ , n ⸩ⁿᵐ

abstract

  -- Monoᵒ for ⸨ ⸩ⁿᵐ

  ⸨⸩ⁿᵐ-Mono :  Monoᵒ ⸨ P˙ , n ⸩ⁿᵐ
  ⸨⸩ⁿᵐ-Mono {n = 0} =  _
  ⸨⸩ⁿᵐ-Mono {n = suc _} =  ∗ᵒ-Mono

  -- Update an element out of the bound

  ⸨⸩ⁿᵐ-⇒upd-≥ :  i ≥ n →  ⸨ Q˙ , n ⸩ⁿᵐ  ⊨ ⸨ updⁿᵐ i P Q˙ , n ⸩ⁿᵐ
  ⸨⸩ⁿᵐ-⇒upd-≥ {_} {0} =  _
  ⸨⸩ⁿᵐ-⇒upd-≥ {i} {suc n'} i>n'  with n' ≡ᵇ i | ᵇ⇒≡ {n'} {i}
  ... | tt | ⇒n'≡i  rewrite ⇒n'≡i _ =  absurd $ <-irrefl i>n'
  ... | ff | _ =  ∗ᵒ-monoʳ $ ⸨⸩ⁿᵐ-⇒upd-≥ $ <⇒≤ i>n'

  -- Add a proposition at the bound

  ⸨⸩ⁿᵐ-add :  ⸨ P ⸩ ∗ᵒ ⸨ Q˙ , n ⸩ⁿᵐ  ⊨ ⸨ updⁿᵐ n P Q˙ , suc n ⸩ⁿᵐ
  ⸨⸩ⁿᵐ-add {n = n}  rewrite ≡ᵇ-refl {n} =  ∗ᵒ-monoʳ $ ⸨⸩ⁿᵐ-⇒upd-≥ $ ≤-refl {n}

  ⸨⸩ⁿᵐ-add⊤ :  ⸨ P˙ , n ⸩ⁿᵐ  ⊨  ⸨ updⁿᵐ n ⊤' P˙ , suc n ⸩ⁿᵐ
  ⸨⸩ⁿᵐ-add⊤ {n = n} =  ?∗ᵒ-intro absurd › ⸨⸩ⁿᵐ-add {n = n}

  -- Remove an element within the bound to get the element's interpretation

  ⸨⸩ⁿᵐ-rem-<ᵈ :  i <ᵈ n →  ⸨ P˙ , n ⸩ⁿᵐ ⊨ ⸨ P˙ i ⸩ ∗ᵒ ⸨ updⁿᵐ i ⊤' P˙ , n ⸩ⁿᵐ
  ⸨⸩ⁿᵐ-rem-<ᵈ {i} ≤ᵈ-refl =  ∗ᵒ-monoʳ (⸨⸩ⁿᵐ-add⊤ {n = i})
  ⸨⸩ⁿᵐ-rem-<ᵈ {i} (≤ᵈsuc {n = n'} i<ᵈn')
    rewrite ≢-≡ᵇ-ff {n'} {i} λ{ refl → <-irrefl $ ≤ᵈ⇒≤ i<ᵈn'} =
    ∗ᵒ-monoʳ (⸨⸩ⁿᵐ-rem-<ᵈ i<ᵈn') › pullʳˡᵒ

  ⸨⸩ⁿᵐ-rem-< :  i < n →  ⸨ P˙ , n ⸩ⁿᵐ ⊨ ⸨ P˙ i ⸩ ∗ᵒ ⸨ updⁿᵐ i ⊤' P˙ , n ⸩ⁿᵐ
  ⸨⸩ⁿᵐ-rem-< =  ⸨⸩ⁿᵐ-rem-<ᵈ ∘ ≤⇒≤ᵈ

--------------------------------------------------------------------------------
-- Invariant for the exclusive indirection ERA

inv-indˣ :  (ℕ → Prop' ∞) × ℕ →  Propᵒ 2ᴸ
inv-indˣ Eˣ =  ⸨ Eˣ ⸩ⁿᵐ

abstract

  add-Indˣ :  ⸨ P ⸩ ∗ᵒ inv-indˣ (E indˣ)  ⊨
                E ⤇ᴱ λ Fˣ → (updᴱᴳ indˣ Fˣ E , Indˣ P ∗ᵒ inv-indˣ Fˣ)
  add-Indˣ {E = E} =  let (_ , n) = E indˣ in
    ?∗ᵒ-intro (ε↝-●-injᴳ-⤇ᴱ add-indˣ) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ _ → ∗ᵒ-mono (_ ,_) $ ⸨⸩ⁿᵐ-add {n = n}) › ⤇ᴱ-param

  rem-Indˣ :  Indˣ P ∗ᵒ inv-indˣ (E indˣ)  ⊨
                E ⤇ᴱ λ Fˣ → (updᴱᴳ indˣ Fˣ E , ⸨ P ⸩ ∗ᵒ inv-indˣ Fˣ)
  rem-Indˣ {E = E} =  let (Q˙ , n) = E indˣ in
    ∃ᵒ∗ᵒ-elim $ λ i → ∗ᵒ-monoˡ (↝-●-injᴳ-⤇ᴱ rem-indˣ) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ{ (refl , i<n) → ∗ᵒ-elimʳ (⸨⸩ⁿᵐ-Mono {n = n}) › ⸨⸩ⁿᵐ-rem-< i<n })
    › ⤇ᴱ-param

--------------------------------------------------------------------------------
-- Invariant for the persistent indirection ERA

inv-ind□ :  (ℕ → Prop' ∞) × ℕ →  Propᵒ 2ᴸ
inv-ind□ E□ =  □ᵒ ⸨ E□ ⸩ⁿᵐ
