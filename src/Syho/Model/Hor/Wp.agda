--------------------------------------------------------------------------------
-- Semantic partial and total weakest preconditions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Hor.Wp where

open import Base.Level using (Level; _⊔ᴸ_; 2ᴸ; 3ᴸ)
open import Base.Func using (_$_; _▷_; _∘_; _›_)
open import Base.Size using (Size; ∞; !; §_)
open import Base.Prod using (π₀; π₁; _,_)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Syho.Lang.Expr using (Type; Expr; Val)
open import Syho.Lang.Ktxred using (Ktxred; Val/Ktxred; val/ktxred)
open import Syho.Lang.Reduce using (Mem; _⇒ᴷᴿ_; _⇒ᴷᴿ∑)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; ∀ᵒ-syntax;
  ⌜_⌝ᵒ×_; ⌜_⌝ᵒ→_; _∗ᵒ_; Thunkᵒ; Shrunkᵒ; ⊨⇒⊨✓; ∀ᵒ-Mono; ∗ᵒ-monoʳ; ∗ᵒ∃ᵒ-out;
  ∗ᵒThunkᵒ-out; ∗ᵒShrunkᵒ-out)
open import Syho.Model.Supd.Interp using (⟨_⟩⇛ᵒ⟨_⟩_; ⟨_⟩⇛ᵒ'⟨_⟩_; ⇛ᵒ⇒⇛ᵒ'; ⇛ᵒ'⇒⇛ᵒ;
  ⇛ᵒ-Mono; ⇛ᵒ-mono✓; ⇛ᵒ-mono; ⇛ᵒ-join; ⇛ᵒ-eatˡ)

private variable
  ł :  Level
  ι ι' :  Size
  T :  Type
  Pᵒ˙ Qᵒ˙ :  Val T → Propᵒ ł
  Qᵒ :  Propᵒ ł
  v :  Val T
  kr :  Ktxred T
  vk :  Val/Ktxred T
  e :  Expr ∞ T

--------------------------------------------------------------------------------
-- Semantic partial weakest precondition

infix 3 ⁺⟨_⟩[_]ᴾᵒ_ ⟨_⟩[_]ᴾᵒ_ ⟨_⟩[<_]ᴾᵒ_

-- Wpᴾ :  ⁺⟨ ⟩[ ]ᴾᵒ with the arguments re-ordered

data  Wpᴾ (Pᵒ˙ : Val T → Propᵒ ł) (ι : Size) :  Val/Ktxred T →  Propᵒ (2ᴸ ⊔ᴸ ł)

-- ⁺⟨ ⟩[ ]ᴾᵒ :  Semantic partial weakest precondition on Val/Ktxred
-- ⟨ ⟩[ ]ᴾᵒ :  Semantic partial weakest precondition on Expr
-- ⟨ ⟩[< ]ᴾᵒ :  ⟨ ⟩[ ]ᴾᵒ under Thunk

⁺⟨_⟩[_]ᴾᵒ_ :  Val/Ktxred T →  Size →  (Val T → Propᵒ ł) →  Propᵒ (2ᴸ ⊔ᴸ ł)
⁺⟨ kr ⟩[ ι ]ᴾᵒ Pᵒ˙ =  Wpᴾ Pᵒ˙ ι kr

⟨_⟩[_]ᴾᵒ_ ⟨_⟩[<_]ᴾᵒ_ :  Expr ∞ T →  Size →  (Val T → Propᵒ ł) →  Propᵒ (2ᴸ ⊔ᴸ ł)
⟨ e ⟩[ ι ]ᴾᵒ Pᵒ˙ =  ⁺⟨ val/ktxred e ⟩[ ι ]ᴾᵒ Pᵒ˙
⟨ e ⟩[< ι ]ᴾᵒ Pᵒ˙ =  Thunkᵒ (⟨ e ⟩[_]ᴾᵒ Pᵒ˙) ι

-- Define Wpᴾ

data  Wpᴾ Pᵒ˙ ι  where
  ⁺⟨⟩ᴾᵒ-val :  (∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ˙ v)  ⊨  ⁺⟨ ĩ₀ v ⟩[ ι ]ᴾᵒ Pᵒ˙
  ⁺⟨⟩ᴾᵒ-kr' :  ∀ᵒ M , ⟨ M ⟩⇛ᵒ'⟨ M ⟩ ⌜ (kr , M) ⇒ᴷᴿ∑ ⌝ᵒ×
                 ∀ᵒ e , ∀ᵒ M' , ⌜ (kr , M) ⇒ᴷᴿ (e , M') ⌝ᵒ→
                   ⟨ M ⟩⇛ᵒ'⟨ M' ⟩ ⟨ e ⟩[< ι ]ᴾᵒ Pᵒ˙  ⊨
               ⁺⟨ ĩ₁ kr ⟩[ ι ]ᴾᵒ Pᵒ˙

abstract

  -- Invert ⁺⟨⟩ᴾᵒ-val

  ⁺⟨⟩ᴾᵒ-val⁻¹ :  ⁺⟨ ĩ₀ v ⟩[ ι ]ᴾᵒ Pᵒ˙  ⊨  ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ˙ v
  ⁺⟨⟩ᴾᵒ-val⁻¹ (⁺⟨⟩ᴾᵒ-val M⇛MPv) =  M⇛MPv

  -- Modified ⁺⟨⟩ᴾᵒ-kr'

  ⁺⟨⟩ᴾᵒ-kr :  ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⌜ (kr , M) ⇒ᴷᴿ∑ ⌝ᵒ×
                ∀ᵒ e , ∀ᵒ M' , ⌜ (kr , M) ⇒ᴷᴿ (e , M') ⌝ᵒ→
                  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ ⟨ e ⟩[< ι ]ᴾᵒ Pᵒ˙  ⊨
              ⁺⟨ ĩ₁ kr ⟩[ ι ]ᴾᵒ Pᵒ˙
  ⁺⟨⟩ᴾᵒ-kr big =  ⁺⟨⟩ᴾᵒ-kr' λ M → big M ▷ (⇛ᵒ-mono λ (krM⇒ , big) → krM⇒ ,
    λ e M' krM⇒eM' → big e M' krM⇒eM' ▷ ⇛ᵒ⇒⇛ᵒ') ▷ ⇛ᵒ⇒⇛ᵒ'

  -- Invert ⁺⟨⟩ᴾᵒ-kr

  ⁺⟨⟩ᴾᵒ-kr⁻¹ :  ⁺⟨ ĩ₁ kr ⟩[ ι ]ᴾᵒ Pᵒ˙  ⊨
                ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⌜ (kr , M) ⇒ᴷᴿ∑ ⌝ᵒ×
                  (∀ᵒ e , ∀ᵒ M' , ⌜ (kr , M) ⇒ᴷᴿ (e , M') ⌝ᵒ→
                    ⟨ M ⟩⇛ᵒ⟨ M' ⟩ ⟨ e ⟩[< ι ]ᴾᵒ Pᵒ˙)
  ⁺⟨⟩ᴾᵒ-kr⁻¹ (⁺⟨⟩ᴾᵒ-kr' big) =  λ M → big M ▷ ⇛ᵒ'⇒⇛ᵒ ▷ (⇛ᵒ-mono λ (krM⇒ , big) →
    krM⇒ , λ e M' krM⇒eM' → big e M' krM⇒eM' ▷ ⇛ᵒ'⇒⇛ᵒ)

  -- Monoᵒ for ⁺⟨⟩ᴾᵒ

  ⁺⟨⟩ᴾᵒ-Mono :  Monoᵒ $ ⁺⟨ vk ⟩[ ι ]ᴾᵒ Pᵒ˙
  ⁺⟨⟩ᴾᵒ-Mono {vk = ĩ₀ _} a⊑b =
    ⁺⟨⟩ᴾᵒ-val⁻¹ › ∀ᵒ-Mono (λ _ → ⇛ᵒ-Mono) a⊑b › ⁺⟨⟩ᴾᵒ-val
  ⁺⟨⟩ᴾᵒ-Mono {vk = ĩ₁ _} a⊑b =
    ⁺⟨⟩ᴾᵒ-kr⁻¹ › ∀ᵒ-Mono (λ _ → ⇛ᵒ-Mono) a⊑b › ⁺⟨⟩ᴾᵒ-kr

  -- Monotonicity of ⁺⟨⟩ᴾᵒ

  ⁺⟨⟩ᴾᵒ-mono✓ :  (∀ v → Pᵒ˙ v ⊨✓ Qᵒ˙ v) →
                 ⁺⟨ vk ⟩[ ι ]ᴾᵒ Pᵒ˙ ⊨ ⁺⟨ vk ⟩[ ι ]ᴾᵒ Qᵒ˙
  ⁺⟨⟩ᴾᵒ-mono✓ {vk = ĩ₀ _} Pv⊨✓Qv ⟨v⟩P =  ⁺⟨⟩ᴾᵒ-val λ M → ⁺⟨⟩ᴾᵒ-val⁻¹ ⟨v⟩P M ▷
    ⇛ᵒ-mono✓ (Pv⊨✓Qv _)
  ⁺⟨⟩ᴾᵒ-mono✓ {vk = ĩ₁ _} Pv⊨✓Qv ⟨kr⟩P =  ⁺⟨⟩ᴾᵒ-kr λ M → ⁺⟨⟩ᴾᵒ-kr⁻¹ ⟨kr⟩P M ▷
    ⇛ᵒ-mono λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' → big e M' krM⇒eM' ▷
    ⇛ᵒ-mono (go Pv⊨✓Qv)
   where
    go :  (∀ v → Pᵒ˙ v ⊨✓ Qᵒ˙ v) →  ⟨ e ⟩[< ι ]ᴾᵒ Pᵒ˙ ⊨ ⟨ e ⟩[< ι ]ᴾᵒ Qᵒ˙
    go Pv⊨✓Qv big .! =  ⁺⟨⟩ᴾᵒ-mono✓ Pv⊨✓Qv $ big .!

  ⁺⟨⟩ᴾᵒ-mono :  (∀ v → Pᵒ˙ v ⊨ Qᵒ˙ v) →  ⁺⟨ vk ⟩[ ι ]ᴾᵒ Pᵒ˙ ⊨ ⁺⟨ vk ⟩[ ι ]ᴾᵒ Qᵒ˙
  ⁺⟨⟩ᴾᵒ-mono =  (⊨⇒⊨✓ ∘_) › ⁺⟨⟩ᴾᵒ-mono✓

  -- ⁺⟨⟩ᴾᵒ absorbs ⇛ᵒ outside itself

  ⇛ᵒ-⁺⟨⟩ᴾᵒ :  ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⁺⟨ vk ⟩[ ι ]ᴾᵒ Pᵒ˙  ⊨  ⁺⟨ vk ⟩[ ι ]ᴾᵒ Pᵒ˙
  ⇛ᵒ-⁺⟨⟩ᴾᵒ {vk = ĩ₀ _} ⇛⟨v⟩P =  ⁺⟨⟩ᴾᵒ-val λ M → ⇛⟨v⟩P M ▷
    ⇛ᵒ-mono (⁺⟨⟩ᴾᵒ-val⁻¹ › _$ M) ▷ ⇛ᵒ-join
  ⇛ᵒ-⁺⟨⟩ᴾᵒ {vk = ĩ₁ _} ⇛⟨kr⟩P =  ⁺⟨⟩ᴾᵒ-kr λ M → ⇛⟨kr⟩P M ▷
    ⇛ᵒ-mono (⁺⟨⟩ᴾᵒ-kr⁻¹ › _$ M) ▷ ⇛ᵒ-join

  -- ⁺⟨⟩ᴾᵒ absorbs ⇛ᵒ inside itself

  ⁺⟨⟩ᴾᵒ-⇛ᵒ :  ⁺⟨ vk ⟩[ ι ]ᴾᵒ (λ v → ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ˙ v)  ⊨
              ⁺⟨ vk ⟩[ ι ]ᴾᵒ Pᵒ˙
  ⁺⟨⟩ᴾᵒ-⇛ᵒ {vk = ĩ₀ _} ⟨v⟩⇛P =  ⁺⟨⟩ᴾᵒ-val λ M → ⁺⟨⟩ᴾᵒ-val⁻¹ ⟨v⟩⇛P M ▷
    ⇛ᵒ-mono (_$ M) ▷ ⇛ᵒ-join
  ⁺⟨⟩ᴾᵒ-⇛ᵒ {vk = ĩ₁ _} ⟨kr⟩⇛P =  ⁺⟨⟩ᴾᵒ-kr λ M → ⁺⟨⟩ᴾᵒ-kr⁻¹ ⟨kr⟩⇛P M ▷ ⇛ᵒ-mono
    λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' → big e M' krM⇒eM' ▷ ⇛ᵒ-mono go
   where
    go :  ⟨ e ⟩[< ι ]ᴾᵒ (λ v → ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ˙ v)  ⊨  ⟨ e ⟩[< ι ]ᴾᵒ Pᵒ˙
    go big .! =  ⁺⟨⟩ᴾᵒ-⇛ᵒ $ big .!

  -- ⁺⟨⟩ᴾᵒ can eat a proposition

  ⁺⟨⟩ᴾᵒ-eatˡ :  Qᵒ ∗ᵒ (⁺⟨ vk ⟩[ ι ]ᴾᵒ Pᵒ˙)  ⊨  ⁺⟨ vk ⟩[ ι ]ᴾᵒ λ v → Qᵒ ∗ᵒ Pᵒ˙ v
  ⁺⟨⟩ᴾᵒ-eatˡ {vk = ĩ₀ _} Q∗⟨v⟩P =  ⁺⟨⟩ᴾᵒ-val λ M → Q∗⟨v⟩P ▷
    ∗ᵒ-monoʳ (⁺⟨⟩ᴾᵒ-val⁻¹ › _$ M) ▷ ⇛ᵒ-eatˡ
  ⁺⟨⟩ᴾᵒ-eatˡ {vk = ĩ₁ _} Q∗⟨kr⟩P =  ⁺⟨⟩ᴾᵒ-kr λ M → Q∗⟨kr⟩P ▷
    ∗ᵒ-monoʳ (⁺⟨⟩ᴾᵒ-kr⁻¹ › _$ M) ▷ ⇛ᵒ-eatˡ ▷ (⇛ᵒ-mono $ ∗ᵒ∃ᵒ-out ›
    λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' → big ▷
    ∗ᵒ-monoʳ (λ big → big e M' krM⇒eM') ▷ ⇛ᵒ-eatˡ ▷ ⇛ᵒ-mono go)
   where
    go :  Qᵒ ∗ᵒ (⟨ e ⟩[< ι ]ᴾᵒ Pᵒ˙)  ⊨  ⟨ e ⟩[< ι ]ᴾᵒ λ v → Qᵒ ∗ᵒ Pᵒ˙ v
    go =  ∗ᵒThunkᵒ-out › λ{ big .! → big .! ▷ ⁺⟨⟩ᴾᵒ-eatˡ }

--------------------------------------------------------------------------------
-- Semantic total weakest precondition

infix 3 ⁺⟨_⟩[_]ᵀᵒ_ ⟨_⟩[_]ᵀᵒ_ ⟨_⟩[<_]ᵀᵒ_

-- Wpᵀ :  ⁺⟨ ⟩[ ]ᵀᵒ with the arguments re-ordered

data  Wpᵀ (Pᵒ˙ : Val T → Propᵒ ł) (ι : Size) :  Val/Ktxred T →  Propᵒ (2ᴸ ⊔ᴸ ł)

-- ⁺⟨ ⟩[ ]ᵀᵒ :  Semantic partial weakest precondition on Val/Ktxred
-- ⟨ ⟩[ ]ᵀᵒ :  Semantic total weakest precondition on Expr
-- ⟨ ⟩[< ]ᵀᵒ :  ⟨ ⟩[ ]ᵀᵒ under Thunk

⁺⟨_⟩[_]ᵀᵒ_ :  Val/Ktxred T →  Size →  (Val T → Propᵒ ł) →  Propᵒ (2ᴸ ⊔ᴸ ł)
⁺⟨ kr ⟩[ ι ]ᵀᵒ Pᵒ˙ =  Wpᵀ Pᵒ˙ ι kr

⟨_⟩[_]ᵀᵒ_ ⟨_⟩[<_]ᵀᵒ_ :  Expr ∞ T →  Size →  (Val T → Propᵒ ł) →  Propᵒ (2ᴸ ⊔ᴸ ł)
⟨ e ⟩[ ι ]ᵀᵒ Pᵒ˙ =  ⁺⟨ val/ktxred e ⟩[ ι ]ᵀᵒ Pᵒ˙
⟨ e ⟩[< ι ]ᵀᵒ Pᵒ˙ =  Shrunkᵒ (⟨ e ⟩[_]ᵀᵒ Pᵒ˙) ι

-- Define Wpᵀ

data  Wpᵀ Pᵒ˙ ι  where
  ⁺⟨⟩ᵀᵒ-val :  (∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ˙ v)  ⊨  ⁺⟨ ĩ₀ v ⟩[ ι ]ᵀᵒ Pᵒ˙
  ⁺⟨⟩ᵀᵒ-kr' :  ∀ᵒ M , ⟨ M ⟩⇛ᵒ'⟨ M ⟩ ⌜ (kr , M) ⇒ᴷᴿ∑ ⌝ᵒ×
                 ∀ᵒ e , ∀ᵒ M' , ⌜ (kr , M) ⇒ᴷᴿ (e , M') ⌝ᵒ→
                   ⟨ M ⟩⇛ᵒ'⟨ M' ⟩ ⟨ e ⟩[< ι ]ᵀᵒ Pᵒ˙  ⊨
               ⁺⟨ ĩ₁ kr ⟩[ ι ]ᵀᵒ Pᵒ˙

abstract

  -- Invert ⁺⟨⟩ᵀᵒ-val

  ⁺⟨⟩ᵀᵒ-val⁻¹ :  ⁺⟨ ĩ₀ v ⟩[ ι ]ᵀᵒ Pᵒ˙  ⊨  ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ˙ v
  ⁺⟨⟩ᵀᵒ-val⁻¹ (⁺⟨⟩ᵀᵒ-val M⇛MPv) =  M⇛MPv

  -- Modified ⁺⟨⟩ᵀᵒ-kr

  ⁺⟨⟩ᵀᵒ-kr :  ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⌜ (kr , M) ⇒ᴷᴿ∑ ⌝ᵒ×
                ∀ᵒ e , ∀ᵒ M' , ⌜ (kr , M) ⇒ᴷᴿ (e , M') ⌝ᵒ→
                  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ ⟨ e ⟩[< ι ]ᵀᵒ Pᵒ˙  ⊨
              ⁺⟨ ĩ₁ kr ⟩[ ι ]ᵀᵒ Pᵒ˙
  ⁺⟨⟩ᵀᵒ-kr big =  ⁺⟨⟩ᵀᵒ-kr' λ M → big M ▷ (⇛ᵒ-mono λ (krM⇒ , big) → krM⇒ ,
    λ e M' krM⇒eM' → big e M' krM⇒eM' ▷ ⇛ᵒ⇒⇛ᵒ') ▷ ⇛ᵒ⇒⇛ᵒ'

  -- Invert ⁺⟨⟩ᵀᵒ-kr

  ⁺⟨⟩ᵀᵒ-kr⁻¹ :  ⁺⟨ ĩ₁ kr ⟩[ ι ]ᵀᵒ Pᵒ˙  ⊨
                ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⌜ (kr , M) ⇒ᴷᴿ∑ ⌝ᵒ×
                  (∀ᵒ e , ∀ᵒ M' , ⌜ (kr , M) ⇒ᴷᴿ (e , M') ⌝ᵒ→
                    ⟨ M ⟩⇛ᵒ⟨ M' ⟩ ⟨ e ⟩[< ι ]ᵀᵒ Pᵒ˙)
  ⁺⟨⟩ᵀᵒ-kr⁻¹ (⁺⟨⟩ᵀᵒ-kr' big) =  λ M → big M ▷ ⇛ᵒ'⇒⇛ᵒ ▷ (⇛ᵒ-mono λ (krM⇒ , big) →
    krM⇒ , λ e M' krM⇒eM' → big e M' krM⇒eM' ▷ ⇛ᵒ'⇒⇛ᵒ)

  -- Monoᵒ for ⁺⟨⟩ᵀᵒ

  ⁺⟨⟩ᵀᵒ-Mono :  Monoᵒ $ ⁺⟨ vk ⟩[ ι ]ᵀᵒ Pᵒ˙
  ⁺⟨⟩ᵀᵒ-Mono {vk = ĩ₀ _} a⊑b =
    ⁺⟨⟩ᵀᵒ-val⁻¹ › ∀ᵒ-Mono (λ _ → ⇛ᵒ-Mono) a⊑b › ⁺⟨⟩ᵀᵒ-val
  ⁺⟨⟩ᵀᵒ-Mono {vk = ĩ₁ _} a⊑b =
    ⁺⟨⟩ᵀᵒ-kr⁻¹ › ∀ᵒ-Mono (λ _ → ⇛ᵒ-Mono) a⊑b › ⁺⟨⟩ᵀᵒ-kr

  -- Monotonicity of ⁺⟨⟩ᵀᵒ

  ⁺⟨⟩ᵀᵒ-mono✓ :  (∀ v → Pᵒ˙ v ⊨✓ Qᵒ˙ v) →
                 ⁺⟨ vk ⟩[ ι ]ᵀᵒ Pᵒ˙ ⊨ ⁺⟨ vk ⟩[ ι ]ᵀᵒ Qᵒ˙
  ⁺⟨⟩ᵀᵒ-mono✓ {vk = ĩ₀ _} Pv⊨✓Qv ⟨v⟩P =  ⁺⟨⟩ᵀᵒ-val λ M → ⁺⟨⟩ᵀᵒ-val⁻¹ ⟨v⟩P M ▷
    ⇛ᵒ-mono✓ (Pv⊨✓Qv _)
  ⁺⟨⟩ᵀᵒ-mono✓ {vk = ĩ₁ _} Pv⊨✓Qv ⟨kr⟩P =  ⁺⟨⟩ᵀᵒ-kr λ M → ⁺⟨⟩ᵀᵒ-kr⁻¹ ⟨kr⟩P M ▷
    ⇛ᵒ-mono λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' → big e M' krM⇒eM' ▷
    ⇛ᵒ-mono (go Pv⊨✓Qv)
   where
    go :  (∀ v → Pᵒ˙ v ⊨✓ Qᵒ˙ v) →  ⟨ e ⟩[< ι ]ᵀᵒ Pᵒ˙ ⊨ ⟨ e ⟩[< ι ]ᵀᵒ Qᵒ˙
    go Pv⊨✓Qv (§ big) =  § ⁺⟨⟩ᵀᵒ-mono✓ Pv⊨✓Qv big

  ⁺⟨⟩ᵀᵒ-mono :  (∀ v → Pᵒ˙ v ⊨ Qᵒ˙ v) →  ⁺⟨ vk ⟩[ ι ]ᵀᵒ Pᵒ˙ ⊨ ⁺⟨ vk ⟩[ ι ]ᵀᵒ Qᵒ˙
  ⁺⟨⟩ᵀᵒ-mono =  (⊨⇒⊨✓ ∘_) › ⁺⟨⟩ᵀᵒ-mono✓

  -- Convert ⁺⟨⟩ᵀᵒ into ⁺⟨⟩ᴾᵒ

  ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ :  ⁺⟨ vk ⟩[ ι ]ᵀᵒ Pᵒ˙  ⊨  ⁺⟨ vk ⟩[ ι' ]ᴾᵒ Pᵒ˙
  ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ {vk = ĩ₀ _} ⟨v⟩P =  ⁺⟨⟩ᴾᵒ-val $ ⁺⟨⟩ᵀᵒ-val⁻¹ ⟨v⟩P
  ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ {vk = ĩ₁ _} ⟨kr⟩P =  ⁺⟨⟩ᴾᵒ-kr λ M → ⁺⟨⟩ᵀᵒ-kr⁻¹ ⟨kr⟩P M ▷ ⇛ᵒ-mono
    λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' → big e M' krM⇒eM' ▷ ⇛ᵒ-mono go
   where
    go :  ⟨ e ⟩[< ι ]ᵀᵒ Pᵒ˙  ⊨  ⟨ e ⟩[< ι' ]ᴾᵒ Pᵒ˙
    go (§ big) .! =  ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ big

  -- ⁺⟨⟩ᵀᵒ absorbs ⇛ᵒ outside itself

  ⇛ᵒ-⁺⟨⟩ᵀᵒ :  ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⁺⟨ vk ⟩[ ι ]ᵀᵒ Pᵒ˙  ⊨  ⁺⟨ vk ⟩[ ι ]ᵀᵒ Pᵒ˙
  ⇛ᵒ-⁺⟨⟩ᵀᵒ {vk = ĩ₀ _} ⇛⟨v⟩P =  ⁺⟨⟩ᵀᵒ-val λ M → ⇛⟨v⟩P M ▷
    ⇛ᵒ-mono (⁺⟨⟩ᵀᵒ-val⁻¹ › _$ M) ▷ ⇛ᵒ-join
  ⇛ᵒ-⁺⟨⟩ᵀᵒ {vk = ĩ₁ _} ⇛⟨kr⟩P =  ⁺⟨⟩ᵀᵒ-kr λ M → ⇛⟨kr⟩P M ▷
    ⇛ᵒ-mono (⁺⟨⟩ᵀᵒ-kr⁻¹ › _$ M) ▷ ⇛ᵒ-join

  -- ⁺⟨⟩ᵀᵒ absorbs ⇛ᵒ inside itself

  ⁺⟨⟩ᵀᵒ-⇛ᵒ :  ⁺⟨ vk ⟩[ ι ]ᵀᵒ (λ v → ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ˙ v)  ⊨
              ⁺⟨ vk ⟩[ ι ]ᵀᵒ Pᵒ˙
  ⁺⟨⟩ᵀᵒ-⇛ᵒ {vk = ĩ₀ _} ⟨v⟩⇛P =  ⁺⟨⟩ᵀᵒ-val λ M → ⁺⟨⟩ᵀᵒ-val⁻¹ ⟨v⟩⇛P M ▷
    ⇛ᵒ-mono (_$ M) ▷ ⇛ᵒ-join
  ⁺⟨⟩ᵀᵒ-⇛ᵒ {vk = ĩ₁ _} ⟨kr⟩⇛P =  ⁺⟨⟩ᵀᵒ-kr λ M → ⁺⟨⟩ᵀᵒ-kr⁻¹ ⟨kr⟩⇛P M ▷ ⇛ᵒ-mono
    λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' → big e M' krM⇒eM' ▷ ⇛ᵒ-mono go
   where
    go :  ⟨ e ⟩[< ι ]ᵀᵒ (λ v → ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ˙ v)  ⊨  ⟨ e ⟩[< ι ]ᵀᵒ Pᵒ˙
    go (§ big) =  § ⁺⟨⟩ᵀᵒ-⇛ᵒ big

  -- ⁺⟨⟩ᵀᵒ can eat a proposition

  ⁺⟨⟩ᵀᵒ-eatˡ :  Qᵒ ∗ᵒ (⁺⟨ vk ⟩[ ι ]ᵀᵒ Pᵒ˙)  ⊨  ⁺⟨ vk ⟩[ ι ]ᵀᵒ λ v → Qᵒ ∗ᵒ Pᵒ˙ v
  ⁺⟨⟩ᵀᵒ-eatˡ {vk = ĩ₀ _} Q∗⟨v⟩P =  ⁺⟨⟩ᵀᵒ-val λ M → Q∗⟨v⟩P ▷
    ∗ᵒ-monoʳ (⁺⟨⟩ᵀᵒ-val⁻¹ › _$ M) ▷ ⇛ᵒ-eatˡ
  ⁺⟨⟩ᵀᵒ-eatˡ {vk = ĩ₁ _} Q∗⟨kr⟩P =  ⁺⟨⟩ᵀᵒ-kr λ M → Q∗⟨kr⟩P ▷
    ∗ᵒ-monoʳ (⁺⟨⟩ᵀᵒ-kr⁻¹ › _$ M) ▷ ⇛ᵒ-eatˡ ▷ (⇛ᵒ-mono $ ∗ᵒ∃ᵒ-out ›
    λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' → big ▷
    ∗ᵒ-monoʳ (λ big → big e M' krM⇒eM') ▷ ⇛ᵒ-eatˡ ▷ ⇛ᵒ-mono go)
   where
    go :  Qᵒ ∗ᵒ (⟨ e ⟩[< ι ]ᵀᵒ Pᵒ˙)  ⊨  ⟨ e ⟩[< ι ]ᵀᵒ λ v → Qᵒ ∗ᵒ Pᵒ˙ v
    go =  ∗ᵒShrunkᵒ-out › λ{ (§ big) → § ⁺⟨⟩ᵀᵒ-eatˡ big }
