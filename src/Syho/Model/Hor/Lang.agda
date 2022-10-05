--------------------------------------------------------------------------------
-- Language-specific lemmas on the weakest preconditions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Hor.Lang where

open import Base.Level using (Level)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Eq using (refl; ◠_)
open import Base.Dec using (Inh; auto)
open import Base.Size using (Size; ∞; !; §_)
open import Base.Prod using (_,_; -,_)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Base.Sety using (Setʸ; ⸨_⸩ʸ)
open import Syho.Lang.Expr using (Type; Expr∞; Expr˂∞; ∇_; Val; V⇒E)
open import Syho.Lang.Ktxred using (Redex; ndᴿ; ▶ᴿ_; _◁ᴿ_; _⁏ᴿ_; forkᴿ; Ktx;
  _ᴷ◁_; _ᴷ∘ᴷ_; val/ktxred; ᴷ∘ᴷ-ᴷ◁; val/ktxred-ĩ₀; val/ktxred-ktx)
open import Syho.Lang.Reduce using (nd⇒; ▶⇒; ◁⇒; ⁏⇒; fork⇒; redᴷᴿ)
open import Syho.Model.Prop.Base using (Propᵒ; substᵒ; _⊨_; ∀ᵒ∈-syntax; _∗ᵒ_;
  _-∗ᵒ_; ∗ᵒ-mono; ∗ᵒ-monoˡ; ∗ᵒ-monoʳ; ?∗ᵒ-intro; ∗ᵒ?-intro; -∗ᵒ-monoʳ)
open import Syho.Model.Prop.Names using ([⊤]ᴺᵒ)
open import Syho.Model.Supd.Interp using (⇛ᵒ-mono; ⇛ᵒ-intro; ⇛ᵒ-join)
open import Syho.Model.Hor.Wp using (ᵃ⟨_⟩ᵒ_; ⁺⟨_⟩ᴾᵒ[_]_; ⁺⟨_⟩ᵀᵒ[_]_; ⟨_⟩ᴾᵒ[_]_;
  ⟨_⟩ᵀᵒ[_]_; ⟨_⟩ᴾᵒ[<_]_; ⟨_⟩ᵀᵒ[<_]_; ⟨_⟩ᴾᵒ⊤[_]; ⟨_⟩ᵀᵒ⊤[_]; ⁺⟨⟩ᴾᵒ-val⁻¹;
  ⁺⟨⟩ᵀᵒ-val⁻¹; ⁺⟨⟩ᴾᵒ-kr; ⁺⟨⟩ᵀᵒ-kr; ⁺⟨⟩ᴾᵒ-kr⁻¹; ⁺⟨⟩ᵀᵒ-kr⁻¹; ⁺⟨⟩ᴾᵒ-mono;
  ⁺⟨⟩ᴾᵒ-size; ¿⁺⟨⟩ᵀᵒ⊤<-size; ⇛ᵒᶠ-⁺⟨⟩ᴾᵒ; ⇛ᵒᶠ-⁺⟨⟩ᵀᵒ)

private variable
  ł :  Level
  ι ι' :  Size
  Xʸ :  Setʸ
  X :  Set₀
  v x :  X
  T U :  Type
  Pᵒ :  Propᵒ ł
  Pᵒ˙ :  X →  Propᵒ ł
  e :  Expr∞ T
  e˂ :  Expr˂∞ T
  e˙ :  X →  Expr∞ T
  red :  Redex T
  K :  Ktx T U

--------------------------------------------------------------------------------
-- Language-specific lemmas on the weakest preconditions

abstract

  -- Get ⁺⟨⟩ᴾ/ᵀᵒ out of ⟨⟩ᴾ/ᵀᵒ under ᵃ⟨⟩ᵒ with [⊤]ᴺᵒ

  ᵃ⟨⟩ᵒ-⟨⟩ᴾᵒ :
    [⊤]ᴺᵒ -∗ᵒ (ᵃ⟨ red ⟩ᵒ λ v → (⟨ K ᴷ◁ V⇒E v ⟩ᴾᵒ[ ι ] Pᵒ˙) ∗ᵒ [⊤]ᴺᵒ)  ⊨
      ⁺⟨ ĩ₁ (-, K , red) ⟩ᴾᵒ[ ι ] Pᵒ˙
  ᵃ⟨⟩ᵒ-⟨⟩ᴾᵒ =  -∗ᵒ-monoʳ (λ big M → big M ▷ ⇛ᵒ-mono λ ((-, redM⇒) , big) →
    (-, redᴷᴿ redM⇒) , λ{ _ _ _ (redᴷᴿ e'eˇM'⇐) → big _ _ _ e'eˇM'⇐ ▷
    λ{ (-, (refl , refl) , big) → big ▷
    ⇛ᵒ-mono (∗ᵒ-mono (λ big → λ{ .! → big }) (?∗ᵒ-intro _)) }}) › ⁺⟨⟩ᴾᵒ-kr

  ᵃ⟨⟩ᵒ-⟨⟩ᵀᵒ :
    [⊤]ᴺᵒ -∗ᵒ (ᵃ⟨ red ⟩ᵒ λ v → (⟨ K ᴷ◁ V⇒E v ⟩ᵀᵒ[ ∞ ] Pᵒ˙) ∗ᵒ [⊤]ᴺᵒ)  ⊨
      ⁺⟨ ĩ₁ (-, K , red) ⟩ᵀᵒ[ ∞ ] Pᵒ˙
  ᵃ⟨⟩ᵒ-⟨⟩ᵀᵒ =  -∗ᵒ-monoʳ (λ big M → big M ▷ ⇛ᵒ-mono λ ((-, redM⇒) , big) →
    (-, redᴷᴿ redM⇒) , λ{ _ _ _ (redᴷᴿ e'eˇM'⇐) → big _ _ _ e'eˇM'⇐ ▷
    λ{ (-, (refl , refl) , big) → big ▷ ⇛ᵒ-mono (∗ᵒ-mono §_ (?∗ᵒ-intro _)) }}) ›
    ⁺⟨⟩ᵀᵒ-kr

  -- Bind for ⟨⟩ᴾ/ᵀᵒ

  ⟨⟩ᴾᵒ-bind :  ⟨ e ⟩ᴾᵒ[ ι ] (λ v → ⟨ K ᴷ◁ V⇒E v ⟩ᴾᵒ[ ι ] Pᵒ˙)  ⊨
               ⟨ K ᴷ◁ e ⟩ᴾᵒ[ ι ] Pᵒ˙
  ⟨⟩ᴾᵒ-bind {e = e} {K = K}  with val/ktxred e | val/ktxred-ĩ₀ {e = e} |
    val/ktxred-ktx {e = e}
  … | ĩ₀ _ | ⇒e≡v | _  rewrite ⇒e≡v refl =  ⁺⟨⟩ᴾᵒ-val⁻¹ › ⇛ᵒᶠ-⁺⟨⟩ᴾᵒ
  … | ĩ₁ (-, K' , _) | _ | ⇒Ke≡KK'red  rewrite ⇒Ke≡KK'red {K = K} refl =
    ⁺⟨⟩ᴾᵒ-kr⁻¹ › -∗ᵒ-monoʳ (λ big M → big M ▷ ⇛ᵒ-mono λ{
    ((-, redᴷᴿ redM⇒) , big) → (-, redᴷᴿ redM⇒) , λ{ _ _ _ (redᴷᴿ e'eˇM'⇐) →
    big _ _ _ (redᴷᴿ e'eˇM'⇐) ▷ ⇛ᵒ-mono (∗ᵒ-monoˡ λ big → λ{ .! {ι'} → big .! ▷
    ⁺⟨⟩ᴾᵒ-mono (λ _ → ⁺⟨⟩ᴾᵒ-size) ▷ ⟨⟩ᴾᵒ-bind ▷
    substᵒ (⟨_⟩ᴾᵒ[ ι' ] _) (◠ ᴷ∘ᴷ-ᴷ◁ {K = K}) }) }}) › ⁺⟨⟩ᴾᵒ-kr

  ⟨⟩ᵀᵒ-bind :  ⟨ e ⟩ᵀᵒ[ ι ] (λ v → ⟨ K ᴷ◁ V⇒E v ⟩ᵀᵒ[ ∞ ] Pᵒ˙)  ⊨
               ⟨ K ᴷ◁ e ⟩ᵀᵒ[ ∞ ] Pᵒ˙
  ⟨⟩ᵀᵒ-bind {e = e} {K = K}  with val/ktxred e | val/ktxred-ĩ₀ {e = e} |
    val/ktxred-ktx {e = e}
  … | ĩ₀ _ | ⇒e≡v | _  rewrite ⇒e≡v refl =  ⁺⟨⟩ᵀᵒ-val⁻¹ › ⇛ᵒᶠ-⁺⟨⟩ᵀᵒ
  … | ĩ₁ (-, K' , _) | _ | ⇒Ke≡KK'red  rewrite ⇒Ke≡KK'red {K = K} refl =
    ⁺⟨⟩ᵀᵒ-kr⁻¹ › -∗ᵒ-monoʳ (λ big M → big M ▷ ⇛ᵒ-mono λ{
    ((-, redᴷᴿ redM⇒) , big) → (-, redᴷᴿ redM⇒) , λ{ _ eˇ _ (redᴷᴿ e'eˇM'⇐) →
    big _ _ _ (redᴷᴿ e'eˇM'⇐) ▷ ⇛ᵒ-mono (∗ᵒ-monoʳ (∗ᵒ-monoˡ $
    ¿⁺⟨⟩ᵀᵒ⊤<-size {ι = ∞} {eˇ = eˇ}) › ∗ᵒ-monoˡ λ{ (§ big) → § ⟨⟩ᵀᵒ-bind big ▷
    substᵒ (⟨_⟩ᵀᵒ[< ∞ ] _) (◠ ᴷ∘ᴷ-ᴷ◁ {K = K}) }) }}) › ⁺⟨⟩ᵀᵒ-kr

  -- nd and ᵃ⟨⟩ᵒ

  ᵃ⟨⟩ᵒ-nd :  {{Inh ⸨ Xʸ ⸩ʸ}} →  Pᵒ ⊨ ᵃ⟨ ndᴿ {Xʸ} ⟩ᵒ λ _ → Pᵒ
  ᵃ⟨⟩ᵒ-nd {{InhX}} Pa M =  ⇛ᵒ-intro ((-, nd⇒ $ auto {{InhX}}) ,
    λ{ _ _ _ (nd⇒ _) → -, (refl , refl) , ⇛ᵒ-intro Pa })

{-
  -- ▶ and ⁺⟨⟩ᴾ/ᵀᵒ
  -- The premise is under the thunk for ⁺⟨⟩ᴾᵒ

  ⁺⟨⟩ᴾᵒ-▶ :  ⟨ K ᴷ◁ e˂ .! ⟩ᴾᵒ[< ι ] Pᵒ˙  ⊨  ⁺⟨ ĩ₁ (-, K , ▶ᴿ e˂) ⟩ᴾᵒ[ ι ] Pᵒ˙
  ⁺⟨⟩ᴾᵒ-▶ big =  ⁺⟨⟩ᴾᵒ-kr λ M → ⇛ᵒ-intro ((-, redᴷᴿ ▶⇒) ,
    λ{ _ _ _ (redᴷᴿ ▶⇒) → ⇛ᵒ-intro $ ∗ᵒ?-intro _ big })

  ⁺⟨⟩ᵀᵒ-▶ :  ⟨ K ᴷ◁ e˂ .! ⟩ᵀᵒ[ ι ] Pᵒ˙  ⊨  ⁺⟨ ĩ₁ (-, K , ▶ᴿ e˂) ⟩ᵀᵒ[ ∞ ] Pᵒ˙
  ⁺⟨⟩ᵀᵒ-▶ big =  ⁺⟨⟩ᵀᵒ-kr λ M → ⇛ᵒ-intro ((-, redᴷᴿ ▶⇒) ,
    λ{ _ _ _ (redᴷᴿ ▶⇒) → ⇛ᵒ-intro $ ∗ᵒ?-intro _ $ § big })

  -- ◁ and ⁺⟨⟩ᴾ/ᵀᵒ

  ⁺⟨⟩ᴾᵒ-◁ :  ⟨ K ᴷ◁ e˙ x ⟩ᴾᵒ[ ι ] Pᵒ˙  ⊨  ⁺⟨ ĩ₁ (-, K , e˙ ◁ᴿ x) ⟩ᴾᵒ[ ι ] Pᵒ˙
  ⁺⟨⟩ᴾᵒ-◁ big =  ⁺⟨⟩ᴾᵒ-kr λ M → ⇛ᵒ-intro ((-, redᴷᴿ ◁⇒) ,
    λ{ _ _ _ (redᴷᴿ ◁⇒) → ⇛ᵒ-intro $ ∗ᵒ?-intro _ λ{ .! → big }})

  ⁺⟨⟩ᵀᵒ-◁ :  ⟨ K ᴷ◁ e˙ x ⟩ᵀᵒ[ ι ] Pᵒ˙  ⊨  ⁺⟨ ĩ₁ (-, K , e˙ ◁ᴿ x) ⟩ᵀᵒ[ ∞ ] Pᵒ˙
  ⁺⟨⟩ᵀᵒ-◁ big =  ⁺⟨⟩ᵀᵒ-kr λ M → ⇛ᵒ-intro ((-, redᴷᴿ ◁⇒) ,
    λ{ _ _ _ (redᴷᴿ ◁⇒) → ⇛ᵒ-intro $ ∗ᵒ?-intro _ $ § big })

  -- ⁏ and ⁺⟨⟩ᴾ/ᵀᵒ

  ⁺⟨⟩ᴾᵒ-⁏ :  ⟨ K ᴷ◁ e ⟩ᴾᵒ[ ι ] Pᵒ˙  ⊨  ⁺⟨ ĩ₁ (-, K , v ⁏ᴿ e) ⟩ᴾᵒ[ ι ] Pᵒ˙
  ⁺⟨⟩ᴾᵒ-⁏ big =  ⁺⟨⟩ᴾᵒ-kr λ M → ⇛ᵒ-intro ((-, redᴷᴿ ⁏⇒) ,
    λ{ _ _ _ (redᴷᴿ ⁏⇒) → ⇛ᵒ-intro $ ∗ᵒ?-intro _ λ{ .! → big }})

  ⁺⟨⟩ᵀᵒ-⁏ :  ⟨ K ᴷ◁ e ⟩ᵀᵒ[ ι ] Pᵒ˙  ⊨  ⁺⟨ ĩ₁ (-, K , v ⁏ᴿ e) ⟩ᵀᵒ[ ∞ ] Pᵒ˙
  ⁺⟨⟩ᵀᵒ-⁏ big =  ⁺⟨⟩ᵀᵒ-kr λ M → ⇛ᵒ-intro ((-, redᴷᴿ ⁏⇒) ,
    λ{ _ _ _ (redᴷᴿ ⁏⇒) → ⇛ᵒ-intro $ ∗ᵒ?-intro _ $ § big })

  -- fork and ⁺⟨⟩ᴾ/ᵀᵒ

  ⁺⟨⟩ᴾᵒ-fork :  (⟨ K ᴷ◁ ∇ _ ⟩ᴾᵒ[ ι ] Pᵒ˙)  ∗ᵒ  ⟨ e ⟩ᴾᵒ⊤[ ι ]  ⊨
                ⁺⟨ ĩ₁ (-, K , forkᴿ e) ⟩ᴾᵒ[ ι ] Pᵒ˙
  ⁺⟨⟩ᴾᵒ-fork big =  ⁺⟨⟩ᴾᵒ-kr λ M → ⇛ᵒ-intro ((-, redᴷᴿ fork⇒) ,
    λ{ _ _ _ (redᴷᴿ fork⇒) → ⇛ᵒ-intro $ big ▷
      ∗ᵒ-mono (λ big → λ{ .! → big }) (λ big → λ{ .! → big }) })

  ⁺⟨⟩ᵀᵒ-fork :  (⟨ K ᴷ◁ ∇ _ ⟩ᵀᵒ[ ι ] Pᵒ˙)  ∗ᵒ  ⟨ e ⟩ᵀᵒ⊤[ ι' ]  ⊨
                ⁺⟨ ĩ₁ (-, K , forkᴿ e) ⟩ᵀᵒ[ ∞ ] Pᵒ˙
  ⁺⟨⟩ᵀᵒ-fork big =  ⁺⟨⟩ᵀᵒ-kr λ M → ⇛ᵒ-intro ((-, redᴷᴿ fork⇒) ,
    λ{ _ _ _ (redᴷᴿ fork⇒) → ⇛ᵒ-intro $ big ▷
      ∗ᵒ-mono (λ big → § big) (λ big → §_ {ι = ∞} big) })
-}