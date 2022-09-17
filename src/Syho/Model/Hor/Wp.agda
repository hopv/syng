--------------------------------------------------------------------------------
-- Semantic partial and total weakest preconditions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Hor.Wp where

open import Base.Level using (2ᴸ; 3ᴸ)
open import Base.Size using (Size; ∞; Thunk; !; Shrunk; §_)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Prod using (π₀; π₁; _,_; -,_)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Syho.Lang.Expr using (Type; Expr; Val)
open import Syho.Lang.Ktxred using (Ktxred; Val/Ktxred; val/ktxred)
open import Syho.Lang.Reduce using (Mem; _⇒ᴷᴿ_; _⇒ᴷᴿ∑)
open import Syho.Model.Prop.Base using (Propᵒ; _⊨_; ∀ᵒ-syntax; ⌜_⌝ᵒ×_; ⌜_⌝ᵒ→_;
  _∗ᵒ_; ∗ᵒ-monoʳ; ∗ᵒ∃ᵒ-out)
open import Syho.Model.Supd.Base using (⇛ᵍ-mono; ⇛ᵍ-eatˡ)
open import Syho.Model.Supd.Sound using (⟨_⟩⇛ᵒ⟨_⟩_; ⟨_⟩⇛ᵒ'⟨_⟩_; ⇛ᵒ⇒⇛ᵒ'; ⇛ᵒ'⇒⇛ᵒ;
  ⇛ᵒ-join)

private variable
  ι ι' :  Size
  M :  Mem
  T U :  Type
  Pᵒ˙ :  Val T →  Propᵒ 2ᴸ
  Qᵒ :  Propᵒ 2ᴸ
  v :  Val T
  kr :  Ktxred T
  vk :  Val/Ktxred T
  e :  Expr ∞ T

--------------------------------------------------------------------------------
-- Semantic partial weakest precondition

infix 3 ⁺⟨_⟩[_]ᴾᵒ_ ⟨_⟩[_]ᴾᵒ_ ⟨_⟩[<_]ᴾᵒ_

-- Declare ⁺⟨ ⟩[ ]ᴾᵒ

data  ⁺⟨_⟩[_]ᴾᵒ_ :  Val/Ktxred T →  Size →  (Val T →  Propᵒ 2ᴸ) →  Propᵒ 3ᴸ

-- ⟨ ⟩[ ]ᴾᵒ :  Semantic partial weakest precondition on Expr
-- ⟨ ⟩[< ]ᴾᵒ :  ⟨ ⟩[ ]ᴾᵒ under Thunk

⟨_⟩[_]ᴾᵒ_ ⟨_⟩[<_]ᴾᵒ_ :  Expr ∞ T →  Size →  (Val T →  Propᵒ 2ᴸ) →  Propᵒ 3ᴸ
⟨ e ⟩[ ι ]ᴾᵒ Pᵒ˙ =  ⁺⟨ val/ktxred e ⟩[ ι ]ᴾᵒ Pᵒ˙
(⟨ e ⟩[< ι ]ᴾᵒ Pᵒ˙) a =  Thunk (λ ι → (⟨ e ⟩[ ι ]ᴾᵒ Pᵒ˙) a) ι

-- ⁺⟨ ⟩[ ]ᴾᵒ :  Semantic partial weakest precondition on Val/Ktxred

data  ⁺⟨_⟩[_]ᴾᵒ_  where
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
  ⁺⟨⟩ᴾᵒ-kr big =  ⁺⟨⟩ᴾᵒ-kr' λ M → big M ▷ (⇛ᵍ-mono λ (krM⇒ , big) → krM⇒ ,
    λ e M' krM⇒eM' → big e M' krM⇒eM' ▷ ⇛ᵒ⇒⇛ᵒ') ▷ ⇛ᵒ⇒⇛ᵒ'

  -- Invert ⁺⟨⟩ᴾᵒ-kr

  ⁺⟨⟩ᴾᵒ-kr⁻¹ :  ⁺⟨ ĩ₁ kr ⟩[ ι ]ᴾᵒ Pᵒ˙  ⊨
                ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⌜ (kr , M) ⇒ᴷᴿ∑ ⌝ᵒ×
                  (∀ᵒ e , ∀ᵒ M' , ⌜ (kr , M) ⇒ᴷᴿ (e , M') ⌝ᵒ→
                    ⟨ M ⟩⇛ᵒ⟨ M' ⟩ ⟨ e ⟩[< ι ]ᴾᵒ Pᵒ˙)
  ⁺⟨⟩ᴾᵒ-kr⁻¹ (⁺⟨⟩ᴾᵒ-kr' big) =  λ M → big M ▷ ⇛ᵒ'⇒⇛ᵒ ▷ (⇛ᵍ-mono λ (krM⇒ , big) →
    krM⇒ , λ e M' krM⇒eM' → big e M' krM⇒eM' ▷ ⇛ᵒ'⇒⇛ᵒ)

  -- ⁺⟨⟩ᴾᵒ absorbs ⇛ᵒ outside itself

  ⇛ᵒ-⁺⟨⟩ᴾᵒ :  ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⁺⟨ vk ⟩[ ι ]ᴾᵒ Pᵒ˙  ⊨  ⁺⟨ vk ⟩[ ι ]ᴾᵒ Pᵒ˙
  ⇛ᵒ-⁺⟨⟩ᴾᵒ {vk = ĩ₀ _} ⇛⟨v⟩P =  ⁺⟨⟩ᴾᵒ-val λ M → ⇛⟨v⟩P M ▷
    ⇛ᵍ-mono (⁺⟨⟩ᴾᵒ-val⁻¹ › _$ M) ▷ ⇛ᵒ-join
  ⇛ᵒ-⁺⟨⟩ᴾᵒ {vk = ĩ₁ _} ⇛⟨kr⟩P =  ⁺⟨⟩ᴾᵒ-kr λ M → ⇛⟨kr⟩P M ▷
    ⇛ᵍ-mono (⁺⟨⟩ᴾᵒ-kr⁻¹ › _$ M) ▷ ⇛ᵒ-join

  -- ⁺⟨⟩ᴾᵒ absorbs ⇛ᵒ inside itself

  ⁺⟨⟩ᴾᵒ-⇛ᵒ :  ⁺⟨ vk ⟩[ ι ]ᴾᵒ (λ v → ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ˙ v)  ⊨
              ⁺⟨ vk ⟩[ ι ]ᴾᵒ Pᵒ˙
  ⁺⟨⟩ᴾᵒ-⇛ᵒ {vk = ĩ₀ _} ⟨v⟩⇛P =  ⁺⟨⟩ᴾᵒ-val λ M → ⁺⟨⟩ᴾᵒ-val⁻¹ ⟨v⟩⇛P M ▷
    ⇛ᵍ-mono (_$ M) ▷ ⇛ᵒ-join
  ⁺⟨⟩ᴾᵒ-⇛ᵒ {vk = ĩ₁ _} ⟨kr⟩⇛P =  ⁺⟨⟩ᴾᵒ-kr λ M → ⁺⟨⟩ᴾᵒ-kr⁻¹ ⟨kr⟩⇛P M ▷ ⇛ᵍ-mono
    λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' → big e M' krM⇒eM' ▷ ⇛ᵍ-mono go
   where
    go :  ⟨ e ⟩[< ι ]ᴾᵒ (λ v → ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ˙ v)  ⊨  ⟨ e ⟩[< ι ]ᴾᵒ Pᵒ˙
    go big .! =  ⁺⟨⟩ᴾᵒ-⇛ᵒ (big .!)

  -- ⁺⟨⟩ᴾᵒ can eat a proposition

  ⁺⟨⟩ᴾᵒ-eatˡ :  Qᵒ ∗ᵒ (⁺⟨ vk ⟩[ ι ]ᴾᵒ Pᵒ˙)  ⊨  ⁺⟨ vk ⟩[ ι ]ᴾᵒ λ v → Qᵒ ∗ᵒ Pᵒ˙ v
  ⁺⟨⟩ᴾᵒ-eatˡ {vk = ĩ₀ _} Q∗⟨v⟩P =  ⁺⟨⟩ᴾᵒ-val λ M → Q∗⟨v⟩P ▷
    ∗ᵒ-monoʳ (⁺⟨⟩ᴾᵒ-val⁻¹ › _$ M) ▷ ⇛ᵍ-eatˡ
  ⁺⟨⟩ᴾᵒ-eatˡ {vk = ĩ₁ _} Q∗⟨kr⟩P =  ⁺⟨⟩ᴾᵒ-kr λ M → Q∗⟨kr⟩P ▷
    ∗ᵒ-monoʳ (⁺⟨⟩ᴾᵒ-kr⁻¹ › _$ M) ▷ ⇛ᵍ-eatˡ ▷ (⇛ᵍ-mono $ ∗ᵒ∃ᵒ-out ›
    λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' → big ▷
    ∗ᵒ-monoʳ (λ big → big e M' krM⇒eM') ▷ ⇛ᵍ-eatˡ ▷ ⇛ᵍ-mono go)
   where
    go :  Qᵒ ∗ᵒ (⟨ e ⟩[< ι ]ᴾᵒ Pᵒ˙)  ⊨  ⟨ e ⟩[< ι ]ᴾᵒ λ v → Qᵒ ∗ᵒ Pᵒ˙ v
    go (-, -, ∙⊑ , Q , big) .! =  ⁺⟨⟩ᴾᵒ-eatˡ (-, -, ∙⊑ , Q , big .!)

--------------------------------------------------------------------------------
-- Semantic total weakest precondition

infix 3 ⁺⟨_⟩[_]ᵀᵒ_ ⟨_⟩[_]ᵀᵒ_ ⟨_⟩[<_]ᵀᵒ_

-- Declare ⁺⟨ ⟩[ ]ᵀᵒ

data  ⁺⟨_⟩[_]ᵀᵒ_ :  Val/Ktxred T →  Size →  (Val T →  Propᵒ 2ᴸ) →  Propᵒ 3ᴸ

-- ⟨ ⟩[ ]ᵀᵒ :  Semantic total weakest precondition on Expr
-- ⟨ ⟩[< ]ᵀᵒ :  ⟨ ⟩[ ]ᵀᵒ under Thunk

⟨_⟩[_]ᵀᵒ_ ⟨_⟩[<_]ᵀᵒ_ :  Expr ∞ T →  Size →  (Val T →  Propᵒ 2ᴸ) →  Propᵒ 3ᴸ
⟨ e ⟩[ ι ]ᵀᵒ Pᵒ˙ =  ⁺⟨ val/ktxred e ⟩[ ι ]ᵀᵒ Pᵒ˙
(⟨ e ⟩[< ι ]ᵀᵒ Pᵒ˙) a =  Shrunk (λ ι → (⟨ e ⟩[ ι ]ᵀᵒ Pᵒ˙) a) ι

-- ⁺⟨ ⟩[ ]ᵀᵒ :  Semantic total weakest precondition on Val/Ktxred

data  ⁺⟨_⟩[_]ᵀᵒ_  where
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
  ⁺⟨⟩ᵀᵒ-kr big =  ⁺⟨⟩ᵀᵒ-kr' λ M → big M ▷ (⇛ᵍ-mono λ (krM⇒ , big) → krM⇒ ,
    λ e M' krM⇒eM' → big e M' krM⇒eM' ▷ ⇛ᵒ⇒⇛ᵒ') ▷ ⇛ᵒ⇒⇛ᵒ'

  -- Invert ⁺⟨⟩ᵀᵒ-kr

  ⁺⟨⟩ᵀᵒ-kr⁻¹ :  ⁺⟨ ĩ₁ kr ⟩[ ι ]ᵀᵒ Pᵒ˙  ⊨
                ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⌜ (kr , M) ⇒ᴷᴿ∑ ⌝ᵒ×
                  (∀ᵒ e , ∀ᵒ M' , ⌜ (kr , M) ⇒ᴷᴿ (e , M') ⌝ᵒ→
                    ⟨ M ⟩⇛ᵒ⟨ M' ⟩ ⟨ e ⟩[< ι ]ᵀᵒ Pᵒ˙)
  ⁺⟨⟩ᵀᵒ-kr⁻¹ (⁺⟨⟩ᵀᵒ-kr' big) =  λ M → big M ▷ ⇛ᵒ'⇒⇛ᵒ ▷ (⇛ᵍ-mono λ (krM⇒ , big) →
    krM⇒ , λ e M' krM⇒eM' → big e M' krM⇒eM' ▷ ⇛ᵒ'⇒⇛ᵒ)

  -- Convert ⁺⟨⟩ᵀᵒ into ⁺⟨⟩ᴾᵒ

  ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ :  ⁺⟨ vk ⟩[ ι ]ᵀᵒ Pᵒ˙  ⊨  ⁺⟨ vk ⟩[ ι' ]ᴾᵒ Pᵒ˙
  ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ {vk = ĩ₀ _} ⟨v⟩P =  ⁺⟨⟩ᴾᵒ-val $ ⁺⟨⟩ᵀᵒ-val⁻¹ ⟨v⟩P
  ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ {vk = ĩ₁ _} ⟨kr⟩P =  ⁺⟨⟩ᴾᵒ-kr λ M → ⁺⟨⟩ᵀᵒ-kr⁻¹ ⟨kr⟩P M ▷ ⇛ᵍ-mono
    λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' → big e M' krM⇒eM' ▷ ⇛ᵍ-mono go
   where
    go :  ⟨ e ⟩[< ι ]ᵀᵒ Pᵒ˙  ⊨  ⟨ e ⟩[< ι' ]ᴾᵒ Pᵒ˙
    go (§ big) .! =  ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ big

  -- ⁺⟨⟩ᵀᵒ absorbs ⇛ᵒ outside itself

  ⇛ᵒ-⁺⟨⟩ᵀᵒ :  ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⁺⟨ vk ⟩[ ι ]ᵀᵒ Pᵒ˙  ⊨  ⁺⟨ vk ⟩[ ι ]ᵀᵒ Pᵒ˙
  ⇛ᵒ-⁺⟨⟩ᵀᵒ {vk = ĩ₀ _} ⇛⟨v⟩P =  ⁺⟨⟩ᵀᵒ-val λ M → ⇛⟨v⟩P M ▷
    ⇛ᵍ-mono (⁺⟨⟩ᵀᵒ-val⁻¹ › _$ M) ▷ ⇛ᵒ-join
  ⇛ᵒ-⁺⟨⟩ᵀᵒ {vk = ĩ₁ _} ⇛⟨kr⟩P =  ⁺⟨⟩ᵀᵒ-kr λ M → ⇛⟨kr⟩P M ▷
    ⇛ᵍ-mono (⁺⟨⟩ᵀᵒ-kr⁻¹ › _$ M) ▷ ⇛ᵒ-join

  -- ⁺⟨⟩ᵀᵒ absorbs ⇛ᵒ inside itself

  ⁺⟨⟩ᵀᵒ-⇛ᵒ :  ⁺⟨ vk ⟩[ ι ]ᵀᵒ (λ v → ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ˙ v)  ⊨
              ⁺⟨ vk ⟩[ ι ]ᵀᵒ Pᵒ˙
  ⁺⟨⟩ᵀᵒ-⇛ᵒ {vk = ĩ₀ _} ⟨v⟩⇛P =  ⁺⟨⟩ᵀᵒ-val λ M → ⁺⟨⟩ᵀᵒ-val⁻¹ ⟨v⟩⇛P M ▷
    ⇛ᵍ-mono (_$ M) ▷ ⇛ᵒ-join
  ⁺⟨⟩ᵀᵒ-⇛ᵒ {vk = ĩ₁ _} ⟨kr⟩⇛P =  ⁺⟨⟩ᵀᵒ-kr λ M → ⁺⟨⟩ᵀᵒ-kr⁻¹ ⟨kr⟩⇛P M ▷ ⇛ᵍ-mono
    λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' → big e M' krM⇒eM' ▷ ⇛ᵍ-mono go
   where
    go :  ⟨ e ⟩[< ι ]ᵀᵒ (λ v → ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ˙ v)  ⊨  ⟨ e ⟩[< ι ]ᵀᵒ Pᵒ˙
    go (§ big) =  § ⁺⟨⟩ᵀᵒ-⇛ᵒ big

  -- ⁺⟨⟩ᵀᵒ can eat a proposition

  ⁺⟨⟩ᵀᵒ-eatˡ :  Qᵒ ∗ᵒ (⁺⟨ vk ⟩[ ι ]ᵀᵒ Pᵒ˙)  ⊨  ⁺⟨ vk ⟩[ ι ]ᵀᵒ λ v → Qᵒ ∗ᵒ Pᵒ˙ v
  ⁺⟨⟩ᵀᵒ-eatˡ {vk = ĩ₀ _} Q∗⟨v⟩P =  ⁺⟨⟩ᵀᵒ-val λ M → Q∗⟨v⟩P ▷
    ∗ᵒ-monoʳ (⁺⟨⟩ᵀᵒ-val⁻¹ › _$ M) ▷ ⇛ᵍ-eatˡ
  ⁺⟨⟩ᵀᵒ-eatˡ {vk = ĩ₁ _} Q∗⟨kr⟩P =  ⁺⟨⟩ᵀᵒ-kr λ M → Q∗⟨kr⟩P ▷
    ∗ᵒ-monoʳ (⁺⟨⟩ᵀᵒ-kr⁻¹ › _$ M) ▷ ⇛ᵍ-eatˡ ▷ (⇛ᵍ-mono $ ∗ᵒ∃ᵒ-out ›
    λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' → big ▷
    ∗ᵒ-monoʳ (λ big → big e M' krM⇒eM') ▷ ⇛ᵍ-eatˡ ▷ ⇛ᵍ-mono go)
   where
    go :  Qᵒ ∗ᵒ (⟨ e ⟩[< ι ]ᵀᵒ Pᵒ˙)  ⊨  ⟨ e ⟩[< ι ]ᵀᵒ λ v → Qᵒ ∗ᵒ Pᵒ˙ v
    go (-, -, ∙⊑ , Q , § big) =  § ⁺⟨⟩ᵀᵒ-eatˡ (-, -, ∙⊑ , Q , big)
