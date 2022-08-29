--------------------------------------------------------------------------------
-- Super update on ○, ↪⇛, ↪⟨ ⟩ᴾ, and ↪⟨ ⟩ᵀ
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Ind where

open import Base.Level using (2ᴸ)
open import Base.Size using (∞)
open import Base.Func using (_$_; _›_; _∘_; id)
open import Base.Few using (absurd)
open import Base.Eq using (_≡_; refl; cong₂)
open import Base.Prod using (_,_)
open import Base.Sum using (inj₀; inj₁)
open import Base.Bool using (tt; ff)
open import Base.Nat using (ℕ; suc; _≥_; _<_; _<ᵈ_; _≥ᵈ_; _≡ᵇ_; ≤-refl; <⇒≤;
  <-irrefl; ≤ᵈ-refl; ≤ᵈsuc; ≤ᵈ⇒≤; ≤⇒≤ᵈ; ᵇ⇒≡; ≡ᵇ-refl; ≢-≡ᵇ-ff; suc⊔-<; suc⊔-≥;
  suc⊔-same)
open import Base.Nmap using (updⁿᵐ)
open import Syho.Logic.Prop using (Prop'; ⊤')
open import Base.Finmap (Prop' ∞) (_≡ ⊤') using (Finmap; Finᶠᵐ; _|ᶠᵐ_; !ᶠᵐ;
  updᶠᵐ; bndᶠᵐ)
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Ind using (add-indˣ; rem-indˣ)
open import Syho.Model.ERA.Glob using (updᴱᴳ; indˣ; Globᴱᴿᴬ)
open ERA Globᴱᴿᴬ using (Env)
open import Syho.Model.Prop.Base using (Propᵒ; _⊨_; ⊤ᵒ; _∗ᵒ_; □ᵒ_; _⤇ᴱ_;
  ∗ᵒ-mono; ∗ᵒ-monoʳ; ?∗ᵒ-intro; pullʳˡᵒ; ⤇ᴱ-mono; ⤇ᴱ-param; ⤇ᴱ-eatʳ;
  ε↝-●-injᴳ-⤇ᴱ)
open import Syho.Model.Prop.Ind using (Indˣ)
open import Syho.Model.Prop.Interp using (⸨_⸩)

private variable
  i j m n :  ℕ
  P :  Prop' ∞
  P˙ Q˙ :  ℕ → Prop' ∞
  Pᶠᵐ Qᶠᵐ :  Finmap
  E :  Env

--------------------------------------------------------------------------------
-- Interpret a map ℕ → Prop' ∞ with a bound

⸨_,_⸩ⁿᵐ :  (ℕ → Prop' ∞) →  ℕ →  Propᵒ 2ᴸ
⸨ P˙ , 0 ⸩ⁿᵐ =  ⊤ᵒ
⸨ P˙ , suc n ⸩ⁿᵐ =  ⸨ P˙ n ⸩ ∗ᵒ ⸨ P˙ , n ⸩ⁿᵐ

abstract

  -- Update an element out of the bound

  ⸨⸩ⁿᵐ-⇒upd-≥ :  i ≥ n →  ⸨ Q˙ , n ⸩ⁿᵐ  ⊨ ⸨ updⁿᵐ i P Q˙ , n ⸩ⁿᵐ
  ⸨⸩ⁿᵐ-⇒upd-≥ {_} {0} =  _
  ⸨⸩ⁿᵐ-⇒upd-≥ {i} {suc n'} i>n'  with n' ≡ᵇ i | ᵇ⇒≡ {n'} {i}
  ... | tt | ⇒n'≡i  rewrite ⇒n'≡i _ =  absurd $ <-irrefl i>n'
  ... | ff | _ =  ∗ᵒ-monoʳ $ ⸨⸩ⁿᵐ-⇒upd-≥ $ <⇒≤ i>n'

  -- Add a proposition at the bound

  ⸨⸩ⁿᵐ-add :  ⸨ P ⸩ ∗ᵒ ⸨ Q˙ , i ⸩ⁿᵐ  ⊨ ⸨ updⁿᵐ i P Q˙ , suc i ⸩ⁿᵐ
  ⸨⸩ⁿᵐ-add {i = i}  rewrite ≡ᵇ-refl {i} =  ∗ᵒ-monoʳ $ ⸨⸩ⁿᵐ-⇒upd-≥ $ ≤-refl {i}

  ⸨⸩ⁿᵐ-add⊤ :  ⸨ P˙ , i ⸩ⁿᵐ  ⊨  ⸨ updⁿᵐ i ⊤' P˙ , suc i ⸩ⁿᵐ
  ⸨⸩ⁿᵐ-add⊤ {i = i} =  ?∗ᵒ-intro absurd › ⸨⸩ⁿᵐ-add {i = i}

  -- Remove an element within the bound to get the element's interpretation

  ⸨⸩ⁿᵐ-rem-<ᵈ :  i <ᵈ n →  ⸨ P˙ , n ⸩ⁿᵐ ⊨ ⸨ P˙ i ⸩ ∗ᵒ ⸨ updⁿᵐ i ⊤' P˙ , n ⸩ⁿᵐ
  ⸨⸩ⁿᵐ-rem-<ᵈ {i} ≤ᵈ-refl =  ∗ᵒ-monoʳ (⸨⸩ⁿᵐ-add⊤ {i = i})
  ⸨⸩ⁿᵐ-rem-<ᵈ {i} (≤ᵈsuc {n = n'} i<ᵈn')
    rewrite ≢-≡ᵇ-ff {n'} {i} λ{ refl → <-irrefl $ ≤ᵈ⇒≤ i<ᵈn'} =
    ∗ᵒ-monoʳ (⸨⸩ⁿᵐ-rem-<ᵈ i<ᵈn') › pullʳˡᵒ

  ⸨⸩ⁿᵐ-rem-< :  i < n →  ⸨ P˙ , n ⸩ⁿᵐ ⊨ ⸨ P˙ i ⸩ ∗ᵒ ⸨ updⁿᵐ i ⊤' P˙ , n ⸩ⁿᵐ
  ⸨⸩ⁿᵐ-rem-< =  ⸨⸩ⁿᵐ-rem-<ᵈ ∘ ≤⇒≤ᵈ

--------------------------------------------------------------------------------
-- Interpret Finmap over Prop' ∞

⸨_⸩ᶠᵐ :  Finmap →  Propᵒ 2ᴸ
⸨ P˙ |ᶠᵐ (n , _) ⸩ᶠᵐ =  ⸨ P˙ , n ⸩ⁿᵐ

abstract

  -- Add a proposition at the bound

  ⸨⸩ᶠᵐ-add :  ⸨ P ⸩ ∗ᵒ ⸨ Qᶠᵐ ⸩ᶠᵐ  ⊨  ⸨ updᶠᵐ (bndᶠᵐ Qᶠᵐ) P Qᶠᵐ ⸩ᶠᵐ
  ⸨⸩ᶠᵐ-add {_} {_ |ᶠᵐ (n , _)}  rewrite suc⊔-same {n} =  ⸨⸩ⁿᵐ-add {i = n}

  -- Remove a proposition

  ⸨⸩ᶠᵐ-rem :  i < bndᶠᵐ Pᶠᵐ →
              ⸨ Pᶠᵐ ⸩ᶠᵐ  ⊨  ⸨ Pᶠᵐ .!ᶠᵐ i ⸩ ∗ᵒ ⸨ updᶠᵐ i ⊤' Pᶠᵐ ⸩ᶠᵐ
  ⸨⸩ᶠᵐ-rem i<n  rewrite suc⊔-< i<n =  ⸨⸩ⁿᵐ-rem-< i<n

--------------------------------------------------------------------------------
-- Invariant for the exclusive indirection ERA

inv-indˣ :  Finmap →  Propᵒ 2ᴸ
inv-indˣ Pᶠᵐ =  ⸨ Pᶠᵐ ⸩ᶠᵐ

abstract

  add-Indˣ :  ⸨ P ⸩ ∗ᵒ inv-indˣ (E indˣ)  ⊨
              E ⤇ᴱ λ Rᶠᵐ → (updᴱᴳ indˣ Rᶠᵐ E , Indˣ P ∗ᵒ inv-indˣ Rᶠᵐ)
  add-Indˣ {P} {E} =  let Qᶠᵐ = E indˣ in
    ?∗ᵒ-intro (ε↝-●-injᴳ-⤇ᴱ $ add-indˣ {Qᶠᵐ}) › ⤇ᴱ-eatʳ ›
    ⤇ᴱ-mono (λ _ → ∗ᵒ-mono (_ ,_) $ ⸨⸩ᶠᵐ-add {P} {Qᶠᵐ}) ›
    ⤇ᴱ-param {f = λ _ → updᶠᵐ _ _ Qᶠᵐ}

--------------------------------------------------------------------------------
-- Invariant for the persistent indirection ERA

inv-ind□ :  Finmap →  Propᵒ 2ᴸ
inv-ind□ Pᶠᵐ =  □ᵒ ⸨ Pᶠᵐ ⸩ᶠᵐ
