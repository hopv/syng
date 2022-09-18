--------------------------------------------------------------------------------
-- Language-specific lemmas on the weakest preconditions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Hor.Lang where

open import Base.Level using (Level)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Eq using (refl)
open import Base.Size using (Size; ∞; !; §_)
open import Base.Prod using (_,_; -,_)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Syho.Lang.Expr using (Type; Expr; Val; V⇒E)
open import Syho.Lang.Ktxred using (Ktx; _ᴷ◁_; _ᴷ∘ᴷ_; _ᴷ|_; val/ktxred; ᴷ∘ᴷ-ᴷ◁;
  val/ktxred-ĩ₀; val/ktxred-ktx)
open import Syho.Lang.Reduce using (redᴷᴿ)
open import Syho.Model.Prop.Base using (Propᵒ; _⊨_)
open import Syho.Model.Supd.Interp using (⇛ᵒ-mono)
open import Syho.Model.Hor.Wp using (⟨_⟩ᴾᵒ[_]_; ⟨_⟩ᵀᵒ[_]_; ⟨_⟩ᴾᵒ[<_]_;
  ⟨_⟩ᵀᵒ[<_]_; ⁺⟨⟩ᴾᵒ-val⁻¹; ⁺⟨⟩ᵀᵒ-val⁻¹; ⁺⟨⟩ᴾᵒ-kr; ⁺⟨⟩ᵀᵒ-kr; ⁺⟨⟩ᴾᵒ-kr⁻¹;
  ⁺⟨⟩ᵀᵒ-kr⁻¹; ⇛ᵒ-⁺⟨⟩ᴾᵒ; ⇛ᵒ-⁺⟨⟩ᵀᵒ)

private variable
  ł :  Level
  ι ι' :  Size
  T U :  Type
  Pᵒ˙ :  Val T →  Propᵒ ł
  e e' :  Expr ∞ T
  K :  Ktx T U

--------------------------------------------------------------------------------
-- Language-specific lemmas on the weakest preconditions

abstract

  -- Bind for ⟨⟩ᴾᵒ / ⟨⟩ᵀᵒ

  ⟨⟩ᴾᵒ-bind :  ⟨ e ⟩ᴾᵒ[ ι ] (λ v → ⟨ K ᴷ◁ V⇒E v ⟩ᴾᵒ[ ∞ ] Pᵒ˙)  ⊨
               ⟨ K ᴷ◁ e ⟩ᴾᵒ[ ι ] Pᵒ˙
  ⟨⟩ᴾᵒ-bind {e = e} {K = K} big  with val/ktxred e | val/ktxred-ĩ₀ {e = e} |
    val/ktxred-ktx {e = e}
  … | ĩ₀ _ | ⇒e≡v | _  rewrite ⇒e≡v refl =  big ▷ ⁺⟨⟩ᴾᵒ-val⁻¹ ▷ ⇛ᵒ-⁺⟨⟩ᴾᵒ
  … | ĩ₁ (K' ᴷ| _) | _ | ⇒Ke≡KK'red  rewrite ⇒Ke≡KK'red {K = K} refl =
    ⁺⟨⟩ᴾᵒ-kr λ M → ⁺⟨⟩ᴾᵒ-kr⁻¹ big M ▷ ⇛ᵒ-mono λ{ ((-, redᴷᴿ redM⇒) , big) →
    (-, redᴷᴿ redM⇒) , λ{ _ M' (redᴷᴿ redM⇒e'M') → big _ M' (redᴷᴿ redM⇒e'M') ▷
    ⇛ᵒ-mono go }}
   where
    go :  ⟨ K' ᴷ◁ e' ⟩ᴾᵒ[< ι ] (λ v → ⟨ K ᴷ◁ V⇒E v ⟩ᴾᵒ[ ∞ ] Pᵒ˙)  ⊨
          ⟨ (K ᴷ∘ᴷ K') ᴷ◁ e' ⟩ᴾᵒ[< ι ] Pᵒ˙
    go {e'} big .!  rewrite ᴷ∘ᴷ-ᴷ◁ {K = K} {K' = K'} {e'} =  big .! ▷ ⟨⟩ᴾᵒ-bind

  ⟨⟩ᵀᵒ-bind :  ⟨ e ⟩ᵀᵒ[ ι ] (λ v → ⟨ K ᴷ◁ V⇒E v ⟩ᵀᵒ[ ι' ] Pᵒ˙)  ⊨
               ⟨ K ᴷ◁ e ⟩ᵀᵒ[ ∞ ] Pᵒ˙
  ⟨⟩ᵀᵒ-bind {e = e} {K = K} big  with val/ktxred e | val/ktxred-ĩ₀ {e = e} |
    val/ktxred-ktx {e = e}
  … | ĩ₀ _ | ⇒e≡v | _  rewrite ⇒e≡v refl =  big ▷ ⁺⟨⟩ᵀᵒ-val⁻¹ ▷ ⇛ᵒ-⁺⟨⟩ᵀᵒ
  … | ĩ₁ (K' ᴷ| _) | _ | ⇒Ke≡KK'red  rewrite ⇒Ke≡KK'red {K = K} refl =
    ⁺⟨⟩ᵀᵒ-kr λ M → ⁺⟨⟩ᵀᵒ-kr⁻¹ big M ▷ ⇛ᵒ-mono λ{ ((-, redᴷᴿ redM⇒) , big) →
    (-, redᴷᴿ redM⇒) , λ{ _ M' (redᴷᴿ redM⇒e'M') → big _ M' (redᴷᴿ redM⇒e'M') ▷
    ⇛ᵒ-mono go }}
   where
    go :  ⟨ K' ᴷ◁ e' ⟩ᵀᵒ[< ι ] (λ v → ⟨ K ᴷ◁ V⇒E v ⟩ᵀᵒ[ ι' ] Pᵒ˙)  ⊨
          ⟨ (K ᴷ∘ᴷ K') ᴷ◁ e' ⟩ᵀᵒ[< ∞ ] Pᵒ˙
    go {e'} (§ big)  rewrite ᴷ∘ᴷ-ᴷ◁ {K = K} {K' = K'} {e'} =  § ⟨⟩ᵀᵒ-bind big
