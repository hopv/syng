--------------------------------------------------------------------------------
-- Hoare triple
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Logic.Hor (ℓ : Level) where

open import Base.Size using (Size; ∞)
open import Base.Func using (_$_)
open import Shog.Logic.Prop ℓ using (Prop')
open import Shog.Logic.Core ℓ using (_⊢[_]_)
open import Shog.Logic.Supd ℓ using (_⊢[_]=>>_; ⇒=>>; =>>-refl)
open import Shog.Lang.Expr ℓ using (Type; Val)
open import Shog.Lang.Reduce ℓ using (Val/Ctxred)

-- Import and re-export
open import Shog.Logic.Judg ℓ public using (WpK; par; tot; wp;
  _⊢[_]'⟨_⟩[_]_; _⊢[_]'⟨_⟩_; _⊢[_]'⟨_⟩ᵀ_; _⊢[_]⟨_⟩[_]_; _⊢[_]⟨_⟩_; _⊢[<_]⟨_⟩_;
  _⊢[_]⟨_⟩ᵀ_; hor-monoˡᵘ; hor-monoʳᵘ; hor-ᵀ⇒; hor-val; hor-▶; hor-◁)

private variable
  ι :  Size
  T :  Type
  κ :  WpK
  P P' :  Prop' ∞
  Qᵛ Q'ᵛ :  Val T → Prop' ∞
  vc :  Val/Ctxred T

hor-monoˡ :  ∀{Qᵛ : Val T → _} →
  P' ⊢[ ι ] P →  P ⊢[ ι ]'⟨ vc ⟩[ κ ] Qᵛ →  P' ⊢[ ι ]'⟨ vc ⟩[ κ ] Qᵛ
hor-monoˡ P'⊢P =  hor-monoˡᵘ $ ⇒=>> P'⊢P

hor-monoʳ :  ∀{Qᵛ : Val T → _} →  (∀ v → Qᵛ v ⊢[ ι ] Q'ᵛ v) →
  P ⊢[ ι ]'⟨ vc ⟩[ κ ] Qᵛ →  P ⊢[ ι ]'⟨ vc ⟩[ κ ] Q'ᵛ
hor-monoʳ ∀vQ⊢Q' =  hor-monoʳᵘ (λ _ → ⇒=>> $ ∀vQ⊢Q' _)
