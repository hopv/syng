--------------------------------------------------------------------------------
-- Language-specific lemmas on the weakest preconditions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Hor.Lang where

open import Base.Level using (Level)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Eq using (refl; ◠_)
open import Base.Size using (Size; ∞; !; §_)
open import Base.Prod using (_,_; -,_)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Base.Inh using (Inh; any)
open import Syho.Lang.Expr using (Type; Expr; Expr˂; ∇_; Val; V⇒E)
open import Syho.Lang.Ktxred using (Ktx; _ᴷ◁_; _ᴷ∘ᴷ_; ndᴿ; ▶ᴿ_; _◁ᴿ_; _⁏ᴿ_;
  _ᴷ|_; val/ktxred; ᴷ∘ᴷ-ᴷ◁; val/ktxred-ĩ₀; val/ktxred-ktx)
open import Syho.Lang.Reduce using (nd⇒; ▶⇒; ◁⇒; ⁏⇒; redᴷᴿ)
open import Syho.Model.Prop.Base using (Propᵒ; substᵒ; _⊨_; ∀ᵒ∈-syntax)
open import Syho.Model.Supd.Interp using (⇛ᵒ-mono; ⇛ᵒ-intro; ⇛ᵒ-join)
open import Syho.Model.Hor.Wp using (⁺⟨_⟩ᴾᵒ[_]_; ⁺⟨_⟩ᵀᵒ[_]_; ⟨_⟩ᴾᵒ[_]_;
  ⟨_⟩ᵀᵒ[_]_; ⟨_⟩ᴾᵒ[<_]_; ⟨_⟩ᵀᵒ[<_]_; ⁺⟨⟩ᴾᵒ-val⁻¹; ⁺⟨⟩ᵀᵒ-val⁻¹; ⁺⟨⟩ᴾᵒ-kr;
  ⁺⟨⟩ᵀᵒ-kr; ⁺⟨⟩ᴾᵒ-kr⁻¹; ⁺⟨⟩ᵀᵒ-kr⁻¹; ⁺⟨⟩ᴾᵒ-mono; ⁺⟨⟩ᴾᵒ-size; ⇛ᵒ-⁺⟨⟩ᴾᵒ; ⇛ᵒ-⁺⟨⟩ᵀᵒ)

private variable
  ł :  Level
  ι ι' :  Size
  X :  Set ł
  x :  X
  T U :  Type
  Pᵒ˙ :  Val T →  Propᵒ ł
  e :  Expr ∞ T
  e˂ :  Expr˂ ∞ T
  e˙ :  X →  Expr ∞ T
  K :  Ktx T U
  v :  Val T

--------------------------------------------------------------------------------
-- Language-specific lemmas on the weakest preconditions

abstract

  -- Bind for ⟨⟩ᴾᵒ / ⟨⟩ᵀᵒ

  ⟨⟩ᴾᵒ-bind :  ⟨ e ⟩ᴾᵒ[ ι ] (λ v → ⟨ K ᴷ◁ V⇒E v ⟩ᴾᵒ[ ι ] Pᵒ˙)  ⊨
               ⟨ K ᴷ◁ e ⟩ᴾᵒ[ ι ] Pᵒ˙
  ⟨⟩ᴾᵒ-bind {e = e} {K = K} big  with val/ktxred e | val/ktxred-ĩ₀ {e = e} |
    val/ktxred-ktx {e = e}
  … | ĩ₀ _ | ⇒e≡v | _  rewrite ⇒e≡v refl =  big ▷ ⁺⟨⟩ᴾᵒ-val⁻¹ ▷ ⇛ᵒ-⁺⟨⟩ᴾᵒ
  … | ĩ₁ (K' ᴷ| _) | _ | ⇒Ke≡KK'red  rewrite ⇒Ke≡KK'red {K = K} refl =
    ⁺⟨⟩ᴾᵒ-kr λ M → ⁺⟨⟩ᴾᵒ-kr⁻¹ big M ▷ ⇛ᵒ-mono λ{ ((-, redᴷᴿ redM⇒) , big) →
    (-, redᴷᴿ redM⇒) , λ{ _ M' (redᴷᴿ redM⇒e'M') → big _ M' (redᴷᴿ redM⇒e'M') ▷
    ⇛ᵒ-mono λ big → λ{ .! {ι'} → big .! ▷ ⁺⟨⟩ᴾᵒ-mono (λ _ → ⁺⟨⟩ᴾᵒ-size) ▷
    ⟨⟩ᴾᵒ-bind ▷ substᵒ (⟨_⟩ᴾᵒ[ ι' ] _) (◠ ᴷ∘ᴷ-ᴷ◁ {K = K}) }}}

  ⟨⟩ᵀᵒ-bind :  ⟨ e ⟩ᵀᵒ[ ι ] (λ v → ⟨ K ᴷ◁ V⇒E v ⟩ᵀᵒ[ ι' ] Pᵒ˙)  ⊨
               ⟨ K ᴷ◁ e ⟩ᵀᵒ[ ∞ ] Pᵒ˙
  ⟨⟩ᵀᵒ-bind {e = e} {K = K} big  with val/ktxred e | val/ktxred-ĩ₀ {e = e} |
    val/ktxred-ktx {e = e}
  … | ĩ₀ _ | ⇒e≡v | _  rewrite ⇒e≡v refl =  big ▷ ⁺⟨⟩ᵀᵒ-val⁻¹ ▷ ⇛ᵒ-⁺⟨⟩ᵀᵒ
  … | ĩ₁ (K' ᴷ| _) | _ | ⇒Ke≡KK'red  rewrite ⇒Ke≡KK'red {K = K} refl =
    ⁺⟨⟩ᵀᵒ-kr λ M → ⁺⟨⟩ᵀᵒ-kr⁻¹ big M ▷ ⇛ᵒ-mono λ{ ((-, redᴷᴿ redM⇒) , big) →
    (-, redᴷᴿ redM⇒) , λ{ _ M' (redᴷᴿ redM⇒e'M') → big _ M' (redᴷᴿ redM⇒e'M') ▷
    ⇛ᵒ-mono λ{ (§ big) → § ⟨⟩ᵀᵒ-bind big ▷
    substᵒ (⟨_⟩ᵀᵒ[< ∞ ] _) (◠ ᴷ∘ᴷ-ᴷ◁ {K = K}) }}}

  -- nd and ⁺⟨⟩ᴾᵒ / ⁺⟨⟩ᵀᵒ

  ⁺⟨⟩ᴾᵒ-nd :  {{Inh X}} →
    ∀ᵒ x ∈ X , ⟨ K ᴷ◁ ∇ x ⟩ᴾᵒ[ ι ] Pᵒ˙  ⊨  ⁺⟨ ĩ₁ (K ᴷ| ndᴿ) ⟩ᴾᵒ[ ι ] Pᵒ˙
  ⁺⟨⟩ᴾᵒ-nd big =  ⁺⟨⟩ᴾᵒ-kr λ M → ⇛ᵒ-intro ((-, redᴷᴿ $ nd⇒ any) ,
    λ{ _ _ (redᴷᴿ (nd⇒ x)) → ⇛ᵒ-intro λ{ .! → big x }})

  ⁺⟨⟩ᵀᵒ-nd :  {{Inh X}} →
    ∀ᵒ x ∈ X , ⟨ K ᴷ◁ ∇ x ⟩ᵀᵒ[ ι ] Pᵒ˙  ⊨  ⁺⟨ ĩ₁ (K ᴷ| ndᴿ) ⟩ᵀᵒ[ ∞ ] Pᵒ˙
  ⁺⟨⟩ᵀᵒ-nd big =  ⁺⟨⟩ᵀᵒ-kr λ M → ⇛ᵒ-intro ((-, redᴷᴿ $ nd⇒ any) ,
    λ{ _ _ (redᴷᴿ (nd⇒ x)) → ⇛ᵒ-intro $ § big x })

  -- ▶ and ⁺⟨⟩ᴾᵒ / ⁺⟨⟩ᵀᵒ
  -- The premise is under the thunk for ⁺⟨⟩ᴾᵒ

  ⁺⟨⟩ᴾᵒ-▶ :  ⟨ K ᴷ◁ e˂ .! ⟩ᴾᵒ[< ι ] Pᵒ˙  ⊨  ⁺⟨ ĩ₁ (K ᴷ| ▶ᴿ e˂) ⟩ᴾᵒ[ ι ] Pᵒ˙
  ⁺⟨⟩ᴾᵒ-▶ big =  ⁺⟨⟩ᴾᵒ-kr λ M → ⇛ᵒ-intro ((-, redᴷᴿ ▶⇒) ,
    λ{ _ _ (redᴷᴿ ▶⇒) → ⇛ᵒ-intro big })

  ⁺⟨⟩ᵀᵒ-▶ :  ⟨ K ᴷ◁ e˂ .! ⟩ᵀᵒ[ ι ] Pᵒ˙  ⊨  ⁺⟨ ĩ₁ (K ᴷ| ▶ᴿ e˂) ⟩ᵀᵒ[ ∞ ] Pᵒ˙
  ⁺⟨⟩ᵀᵒ-▶ big =  ⁺⟨⟩ᵀᵒ-kr λ M → ⇛ᵒ-intro ((-, redᴷᴿ ▶⇒) ,
    λ{ _ _ (redᴷᴿ ▶⇒) → ⇛ᵒ-intro $ § big })

  -- ◁ and ⁺⟨⟩ᴾᵒ / ⁺⟨⟩ᵀᵒ

  ⁺⟨⟩ᴾᵒ-◁ :  ⟨ K ᴷ◁ e˙ x ⟩ᴾᵒ[ ι ] Pᵒ˙  ⊨  ⁺⟨ ĩ₁ (K ᴷ| e˙ ◁ᴿ x) ⟩ᴾᵒ[ ι ] Pᵒ˙
  ⁺⟨⟩ᴾᵒ-◁ big =  ⁺⟨⟩ᴾᵒ-kr λ M → ⇛ᵒ-intro ((-, redᴷᴿ ◁⇒) ,
    λ{ _ _ (redᴷᴿ ◁⇒) → ⇛ᵒ-intro λ{ .! → big }})

  ⁺⟨⟩ᵀᵒ-◁ :  ⟨ K ᴷ◁ e˙ x ⟩ᵀᵒ[ ι ] Pᵒ˙  ⊨  ⁺⟨ ĩ₁ (K ᴷ| e˙ ◁ᴿ x) ⟩ᵀᵒ[ ∞ ] Pᵒ˙
  ⁺⟨⟩ᵀᵒ-◁ big =  ⁺⟨⟩ᵀᵒ-kr λ M → ⇛ᵒ-intro ((-, redᴷᴿ ◁⇒) ,
    λ{ _ _ (redᴷᴿ ◁⇒) → ⇛ᵒ-intro $ § big })

  -- ⁏ and ⁺⟨⟩ᴾᵒ / ⁺⟨⟩ᵀᵒ

  ⁺⟨⟩ᴾᵒ-⁏ :  ⟨ K ᴷ◁ e ⟩ᴾᵒ[ ι ] Pᵒ˙  ⊨  ⁺⟨ ĩ₁ (K ᴷ| v ⁏ᴿ e) ⟩ᴾᵒ[ ι ] Pᵒ˙
  ⁺⟨⟩ᴾᵒ-⁏ big =  ⁺⟨⟩ᴾᵒ-kr λ M → ⇛ᵒ-intro ((-, redᴷᴿ ⁏⇒) ,
    λ{ _ _ (redᴷᴿ ⁏⇒) → ⇛ᵒ-intro λ{ .! → big }})

  ⁺⟨⟩ᵀᵒ-⁏ :  ⟨ K ᴷ◁ e ⟩ᵀᵒ[ ι ] Pᵒ˙  ⊨  ⁺⟨ ĩ₁ (K ᴷ| v ⁏ᴿ e) ⟩ᵀᵒ[ ∞ ] Pᵒ˙
  ⁺⟨⟩ᵀᵒ-⁏ big =  ⁺⟨⟩ᵀᵒ-kr λ M → ⇛ᵒ-intro ((-, redᴷᴿ ⁏⇒) ,
    λ{ _ _ (redᴷᴿ ⁏⇒) → ⇛ᵒ-intro $ § big })
