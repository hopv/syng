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
open import Syho.Model.Prop.Base using (Propᵒ; _⊨_; ⊤ᵒ; _∗ᵒ_; □ᵒ_; ∗ᵒ-monoʳ;
  ?∗ᵒ-intro; pullʳˡᵒ)
open import Syho.Model.Prop.Interp using (⸨_⸩)

private variable
  i j m n :  ℕ
  P˙ Q˙ :  ℕ → Prop' ∞
  Q :  Prop' ∞
  Pᶠᵐ :  Finmap

--------------------------------------------------------------------------------
-- Interpret a map ℕ → Prop' ∞ with a bound

⸨_,_⸩ⁿᵐ :  (ℕ → Prop' ∞) →  ℕ →  Propᵒ 2ᴸ
⸨ P˙ , 0 ⸩ⁿᵐ =  ⊤ᵒ
⸨ P˙ , suc n ⸩ⁿᵐ =  ⸨ P˙ n ⸩ ∗ᵒ ⸨ P˙ , n ⸩ⁿᵐ

abstract

  -- Congruence on ⸨⸩ⁿᵐ

  ⸨⸩ⁿᵐ-cong :  (∀{i} → P˙ i ≡ Q˙ i) →  ⸨ P˙ , n ⸩ⁿᵐ ≡ ⸨ Q˙ , n ⸩ⁿᵐ
  ⸨⸩ⁿᵐ-cong {n = 0} _ =  refl
  ⸨⸩ⁿᵐ-cong {P˙} {Q˙} {suc n'} Pi≡Qi
    rewrite Pi≡Qi {n'} | ⸨⸩ⁿᵐ-cong {P˙} {Q˙} {n'} Pi≡Qi =  refl

  -- Update an element out of the bound

  ⸨⸩ⁿᵐ-⇒upd-≥ :  i ≥ n →  ⸨ P˙ , n ⸩ⁿᵐ  ⊨ ⸨ updⁿᵐ i Q P˙ , n ⸩ⁿᵐ
  ⸨⸩ⁿᵐ-⇒upd-≥ {_} {0} =  _
  ⸨⸩ⁿᵐ-⇒upd-≥ {i} {suc n'} i>n'  with n' ≡ᵇ i | ᵇ⇒≡ {n'} {i}
  ... | tt | ⇒n'≡i  rewrite ⇒n'≡i _ =  absurd $ <-irrefl i>n'
  ... | ff | _ =  ∗ᵒ-monoʳ $ ⸨⸩ⁿᵐ-⇒upd-≥ $ <⇒≤ i>n'

  -- Add a proposition at the bound

  ⸨⸩ⁿᵐ-add :  ⸨ Q ⸩ ∗ᵒ ⸨ P˙ , i ⸩ⁿᵐ  ⊨ ⸨ updⁿᵐ i Q P˙ , suc i ⸩ⁿᵐ
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

  ⸨⸩ᶠᵐ-add :  ⸨ Q ⸩ ∗ᵒ ⸨ Pᶠᵐ ⸩ᶠᵐ  ⊨  ⸨ updᶠᵐ (bndᶠᵐ Pᶠᵐ) Q Pᶠᵐ ⸩ᶠᵐ
  ⸨⸩ᶠᵐ-add {Pᶠᵐ = _ |ᶠᵐ (n , _)}  rewrite suc⊔-same {n} =  ⸨⸩ⁿᵐ-add {i = n}

  -- Remove a proposition

  ⸨⸩ᶠᵐ-rem :  i < bndᶠᵐ Pᶠᵐ →
              ⸨ Pᶠᵐ ⸩ᶠᵐ  ⊨  ⸨ Pᶠᵐ .!ᶠᵐ i ⸩ ∗ᵒ ⸨ updᶠᵐ i ⊤' Pᶠᵐ ⸩ᶠᵐ
  ⸨⸩ᶠᵐ-rem i<n  rewrite suc⊔-< i<n =  ⸨⸩ⁿᵐ-rem-< i<n

--------------------------------------------------------------------------------
-- Invariant for the exclusive indirection ERA

inv-indˣ :  Finmap →  Propᵒ 2ᴸ
inv-indˣ Pᶠᵐ =  ⸨ Pᶠᵐ ⸩ᶠᵐ

--------------------------------------------------------------------------------
-- Invariant for the persistent indirection ERA

inv-ind□ :  Finmap →  Propᵒ 2ᴸ
inv-ind□ Pᶠᵐ =  □ᵒ ⸨ Pᶠᵐ ⸩ᶠᵐ
