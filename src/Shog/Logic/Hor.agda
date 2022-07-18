--------------------------------------------------------------------------------
-- Hoare triple
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Logic.Hor (ℓ : Level) where

open import Base.Level using (↑_)
open import Base.Size using (Size; ∞)
open import Base.Func using (_$_)
open import Base.Prod using (_,_)
open import Base.Sum using (inj₀; inj₁)
open import Shog.Logic.Prop ℓ using (Prop')
open import Shog.Logic.Core ℓ using (_⊢[_]_)
open import Shog.Logic.Supd ℓ using (_⊢[_]=>>_; ⇒=>>; =>>-refl)
open import Shog.Lang.Expr ℓ using (Type; Expr; Val; let˙)
open import Shog.Lang.Ktx ℓ using (ndᴿ; Ktx; •ᴷ; _◁ᴷʳ_; Val/Ktxred)

-- Import and re-export
open import Shog.Logic.Judg ℓ public using (WpK; par; tot; Wp'; _⊢[_]'⟨_⟩[_]_;
  _⊢[_]'⟨_⟩ᴾ_; _⊢[_]'⟨_⟩ᵀ_; _⊢[_]⟨_⟩[_]_; _⊢[_]⟨_⟩ᴾ_; _⊢[<_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ_;
  hor-ᵀ⇒ᴾ; hor-monoˡᵘ; hor-monoʳᵘ; hor-frame; hor-bind; hor-valᵘ; hor-ndᵘ;
  horᴾ-▶; horᵀ-▶; hor-◁)

private variable
  ι :  Size
  A :  Set ℓ
  T U :  Type
  κ :  WpK
  P P' :  Prop' ∞
  Qᵛ Q'ᵛ Rᵛ :  Val T → Prop' ∞
  vc :  Val/Ktxred T
  ktx :  Ktx U T
  e₀ :  Expr ∞ T
  e˙ :  A → Expr ∞ T

abstract

  -- Monotonicity

  hor-monoˡ :  ∀{Qᵛ : Val T → _} →  P' ⊢[ ι ] P →
               P ⊢[ ι ]'⟨ vc ⟩[ κ ] Qᵛ →  P' ⊢[ ι ]'⟨ vc ⟩[ κ ] Qᵛ
  hor-monoˡ P'⊢P =  hor-monoˡᵘ $ ⇒=>> P'⊢P

  hor-monoʳ :  ∀{Qᵛ : Val T → _} →  (∀ v → Qᵛ v ⊢[ ι ] Q'ᵛ v) →
               P ⊢[ ι ]'⟨ vc ⟩[ κ ] Qᵛ →  P ⊢[ ι ]'⟨ vc ⟩[ κ ] Q'ᵛ
  hor-monoʳ ∀vQ⊢Q' =  hor-monoʳᵘ $ λ _ → ⇒=>> $ ∀vQ⊢Q' _

  -- Non-deterministic value

  hor-nd :  (∀ a → P ⊢[ ι ] Qᵛ (↑ a)) →
            P ⊢[ ι ]'⟨ inj₁ $ _ , ktx , ndᴿ ⟩[ κ ] Qᵛ
  hor-nd ∀aP⊢Q =  hor-ndᵘ $ λ _ → ⇒=>> $ ∀aP⊢Q _

  -- Let binding

  hor-let :  ∀{Rᵛ : _ → _} →  P ⊢[ ι ]⟨ e₀ ⟩[ κ ] Qᵛ →
              (∀ a → Qᵛ (↑ a) ⊢[ ι ]⟨ e˙ a ⟩[ κ ] Rᵛ) →
              P ⊢[ ι ]⟨ let˙ e₀ e˙ ⟩[ κ ] Rᵛ
  hor-let P⊢⟨e₀⟩Q ∀aQ⊢⟨e˙⟩R =
    hor-bind {ktx = _ ◁ᴷʳ •ᴷ} P⊢⟨e₀⟩Q $ λ (↑ a) → hor-◁ $ ∀aQ⊢⟨e˙⟩R a

  -- Value

  hor-val :  ∀{v : Val T} →  P ⊢[ ι ] Qᵛ v →  P ⊢[ ι ]'⟨ inj₀ v ⟩[ κ ] Qᵛ
  hor-val P⊢Q =  hor-valᵘ $ ⇒=>> P⊢Q
