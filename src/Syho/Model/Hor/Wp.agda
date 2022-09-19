--------------------------------------------------------------------------------
-- Semantic partial and total weakest preconditions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Hor.Wp where

open import Base.Level using (Level; _⊔ᴸ_; 2ᴸ; 3ᴸ)
open import Base.Func using (_$_; _▷_; _∘_; _›_)
open import Base.Size using (Size; Size<; ∞; !; §_)
open import Base.Prod using (π₀; π₁; _,_)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Syho.Lang.Expr using (Type; Expr; Val)
open import Syho.Lang.Ktxred using (Ktxred; Val/Ktxred; val/ktxred)
open import Syho.Lang.Reduce using (Mem; _⇒ᴷᴿ_; _⇒ᴷᴿ∑)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; ∀ᵒ-syntax;
  ⌜_⌝ᵒ×_; ⌜_⌝ᵒ→_; _∗ᵒ_; Thunkᵒ; Shrunkᵒ; ⊨⇒⊨✓; ∀ᵒ-Mono; ∗ᵒ-monoʳ; ∗ᵒ∃ᵒ-out;
  ∗ᵒThunkᵒ-out; ∗ᵒShrunkᵒ-out)
open import Syho.Model.Supd.Interp using (⟨_⟩⇛ᵒ⟨_⟩_; ⟨_⟩⇛ᵒ'⟨_⟩_; ⇛ᵒ⇒⇛ᵒ'; ⇛ᵒ'⇒⇛ᵒ;
  ⇛ᵒ-Mono; ⇛ᵒ-mono✓; ⇛ᵒ-mono; ⊨✓⇒⊨-⇛ᵒ; ⇛ᵒ-intro; ⇛ᵒ-join; ⇛ᵒ-eatˡ)

private variable
  ł :  Level
  ι ι' :  Size
  T :  Type
  Pᵒ Qᵒ :  Propᵒ ł
  Pᵒ˙ Qᵒ˙ :  Val T → Propᵒ ł
  v :  Val T
  kr :  Ktxred T
  vk :  Val/Ktxred T
  e :  Expr ∞ T

--------------------------------------------------------------------------------
-- Semantic partial weakest precondition

infix 3 ⁺⟨_⟩ᴾᵒ[_]_ ⟨_⟩ᴾᵒ[_]_ ⟨_⟩ᴾᵒ[<_]_

-- Wpᴾ :  ⁺⟨ ⟩ᴾᵒ[ ] with the arguments re-ordered

data  Wpᴾ (Pᵒ˙ : Val T → Propᵒ ł) (ι : Size) :  Val/Ktxred T →  Propᵒ (2ᴸ ⊔ᴸ ł)

-- ⁺⟨ ⟩ᴾᵒ[ ] :  Semantic partial weakest precondition on Val/Ktxred
-- ⟨ ⟩ᴾᵒ[ ] :  Semantic partial weakest precondition on Expr
-- ⟨ ⟩ᴾᵒ[< ] :  ⟨ ⟩ᴾᵒ[ ] under Thunk

⁺⟨_⟩ᴾᵒ[_]_ :  Val/Ktxred T →  Size →  (Val T → Propᵒ ł) →  Propᵒ (2ᴸ ⊔ᴸ ł)
⁺⟨ kr ⟩ᴾᵒ[ ι ] Pᵒ˙ =  Wpᴾ Pᵒ˙ ι kr

⟨_⟩ᴾᵒ[_]_ ⟨_⟩ᴾᵒ[<_]_ :  Expr ∞ T →  Size →  (Val T → Propᵒ ł) →  Propᵒ (2ᴸ ⊔ᴸ ł)
⟨ e ⟩ᴾᵒ[ ι ] Pᵒ˙ =  ⁺⟨ val/ktxred e ⟩ᴾᵒ[ ι ] Pᵒ˙
⟨ e ⟩ᴾᵒ[< ι ] Pᵒ˙ =  Thunkᵒ (⟨ e ⟩ᴾᵒ[_] Pᵒ˙) ι

-- Define Wpᴾ

data  Wpᴾ Pᵒ˙ ι  where

  -- For a value, having the postcondition under ⇛ᵒ

  ⁺⟨⟩ᴾᵒ-val :  (∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ˙ v)  ⊨  ⁺⟨ ĩ₀ v ⟩ᴾᵒ[ ι ] Pᵒ˙

  -- For a context-redex pair, stating that the reduction is not stuck
  -- and for every next state the weakest precondition coinductively holds

  -- We should use ⇛ᵒ' (the concrete version) instead of ⇛ᵒ (the abstract
  -- version) here to pass the strict positivity check

  ⁺⟨⟩ᴾᵒ-kr' :  ∀ᵒ M , ⟨ M ⟩⇛ᵒ'⟨ M ⟩ ⌜ (kr , M) ⇒ᴷᴿ∑ ⌝ᵒ×
                 ∀ᵒ e , ∀ᵒ M' , ⌜ (kr , M) ⇒ᴷᴿ (e , M') ⌝ᵒ→
                   ⟨ M ⟩⇛ᵒ'⟨ M' ⟩ ⟨ e ⟩ᴾᵒ[< ι ] Pᵒ˙  ⊨
               ⁺⟨ ĩ₁ kr ⟩ᴾᵒ[ ι ] Pᵒ˙

--------------------------------------------------------------------------------
-- Semantic total weakest precondition

infix 3 ⁺⟨_⟩ᵀᵒ[_]_ ⟨_⟩ᵀᵒ[_]_ ⟨_⟩ᵀᵒ[<_]_

-- Wpᵀ :  ⁺⟨ ⟩ᵀᵒ[ ] with the arguments re-ordered

data  Wpᵀ (Pᵒ˙ : Val T → Propᵒ ł) (ι : Size) :  Val/Ktxred T →  Propᵒ (2ᴸ ⊔ᴸ ł)

-- ⁺⟨ ⟩ᵀᵒ[ ] :  Semantic partial weakest precondition on Val/Ktxred
-- ⟨ ⟩ᵀᵒ[ ] :  Semantic total weakest precondition on Expr
-- ⟨ ⟩[< ]ᵀᵒ :  ⟨ ⟩ᵀᵒ[ ] under Thunk

⁺⟨_⟩ᵀᵒ[_]_ :  Val/Ktxred T →  Size →  (Val T → Propᵒ ł) →  Propᵒ (2ᴸ ⊔ᴸ ł)
⁺⟨ kr ⟩ᵀᵒ[ ι ] Pᵒ˙ =  Wpᵀ Pᵒ˙ ι kr

-- We use Shrunk for defining Wpᵀ, which enables induction based semantically on
-- the size rather than on the syntactic structure.

⟨_⟩ᵀᵒ[_]_ ⟨_⟩ᵀᵒ[<_]_ :  Expr ∞ T →  Size →  (Val T → Propᵒ ł) →  Propᵒ (2ᴸ ⊔ᴸ ł)
⟨ e ⟩ᵀᵒ[ ι ] Pᵒ˙ =  ⁺⟨ val/ktxred e ⟩ᵀᵒ[ ι ] Pᵒ˙
⟨ e ⟩ᵀᵒ[< ι ] Pᵒ˙ =  Shrunkᵒ (⟨ e ⟩ᵀᵒ[_] Pᵒ˙) ι

-- Define Wpᵀ

data  Wpᵀ Pᵒ˙ ι  where

  -- For a value, having the postcondition under ⇛ᵒ

  ⁺⟨⟩ᵀᵒ-val :  (∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ˙ v)  ⊨  ⁺⟨ ĩ₀ v ⟩ᵀᵒ[ ι ] Pᵒ˙

  -- For a context-redex pair, stating that the reduction is not stuck
  -- and for every next state the weakest precondition inductively holds

  ⁺⟨⟩ᵀᵒ-kr' :  ∀ᵒ M , ⟨ M ⟩⇛ᵒ'⟨ M ⟩ ⌜ (kr , M) ⇒ᴷᴿ∑ ⌝ᵒ×
                 ∀ᵒ e , ∀ᵒ M' , ⌜ (kr , M) ⇒ᴷᴿ (e , M') ⌝ᵒ→
                   ⟨ M ⟩⇛ᵒ'⟨ M' ⟩ ⟨ e ⟩ᵀᵒ[< ι ] Pᵒ˙  ⊨
               ⁺⟨ ĩ₁ kr ⟩ᵀᵒ[ ι ] Pᵒ˙

--------------------------------------------------------------------------------
-- Lemmas on the partial and total weakest preconditions

abstract

  -- Invert ⁺⟨⟩ᴾᵒ-val / ⁺⟨⟩ᵀᵒ-val

  ⁺⟨⟩ᴾᵒ-val⁻¹ :  ⁺⟨ ĩ₀ v ⟩ᴾᵒ[ ι ] Pᵒ˙  ⊨  ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ˙ v
  ⁺⟨⟩ᴾᵒ-val⁻¹ (⁺⟨⟩ᴾᵒ-val M⇛MPv) =  M⇛MPv

  ⁺⟨⟩ᵀᵒ-val⁻¹ :  ⁺⟨ ĩ₀ v ⟩ᵀᵒ[ ι ] Pᵒ˙  ⊨  ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ˙ v
  ⁺⟨⟩ᵀᵒ-val⁻¹ (⁺⟨⟩ᵀᵒ-val M⇛MPv) =  M⇛MPv

  -- Modified ⁺⟨⟩ᴾᵒ-kr' / ⁺⟨⟩ᵀᵒ-kr'

  ⁺⟨⟩ᴾᵒ-kr :  ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⌜ (kr , M) ⇒ᴷᴿ∑ ⌝ᵒ×
                ∀ᵒ e , ∀ᵒ M' , ⌜ (kr , M) ⇒ᴷᴿ (e , M') ⌝ᵒ→
                  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ ⟨ e ⟩ᴾᵒ[< ι ] Pᵒ˙  ⊨
              ⁺⟨ ĩ₁ kr ⟩ᴾᵒ[ ι ] Pᵒ˙
  ⁺⟨⟩ᴾᵒ-kr big =  ⁺⟨⟩ᴾᵒ-kr' λ M → big M ▷ (⇛ᵒ-mono λ (krM⇒ , big) → krM⇒ ,
    λ e M' krM⇒eM' → big e M' krM⇒eM' ▷ ⇛ᵒ⇒⇛ᵒ') ▷ ⇛ᵒ⇒⇛ᵒ'

  ⁺⟨⟩ᵀᵒ-kr :  ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⌜ (kr , M) ⇒ᴷᴿ∑ ⌝ᵒ×
                ∀ᵒ e , ∀ᵒ M' , ⌜ (kr , M) ⇒ᴷᴿ (e , M') ⌝ᵒ→
                  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ ⟨ e ⟩ᵀᵒ[< ι ] Pᵒ˙  ⊨
              ⁺⟨ ĩ₁ kr ⟩ᵀᵒ[ ι ] Pᵒ˙
  ⁺⟨⟩ᵀᵒ-kr big =  ⁺⟨⟩ᵀᵒ-kr' λ M → big M ▷ (⇛ᵒ-mono λ (krM⇒ , big) → krM⇒ ,
    λ e M' krM⇒eM' → big e M' krM⇒eM' ▷ ⇛ᵒ⇒⇛ᵒ') ▷ ⇛ᵒ⇒⇛ᵒ'

  -- Invert ⁺⟨⟩ᴾᵒ-kr / ⁺⟨⟩ᵀᵒ-kr

  ⁺⟨⟩ᴾᵒ-kr⁻¹ :  ⁺⟨ ĩ₁ kr ⟩ᴾᵒ[ ι ] Pᵒ˙  ⊨
                ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⌜ (kr , M) ⇒ᴷᴿ∑ ⌝ᵒ×
                  (∀ᵒ e , ∀ᵒ M' , ⌜ (kr , M) ⇒ᴷᴿ (e , M') ⌝ᵒ→
                    ⟨ M ⟩⇛ᵒ⟨ M' ⟩ ⟨ e ⟩ᴾᵒ[< ι ] Pᵒ˙)
  ⁺⟨⟩ᴾᵒ-kr⁻¹ (⁺⟨⟩ᴾᵒ-kr' big) =  λ M → big M ▷ ⇛ᵒ'⇒⇛ᵒ ▷ ⇛ᵒ-mono λ (krM⇒ , big) →
    krM⇒ , λ e M' krM⇒eM' → big e M' krM⇒eM' ▷ ⇛ᵒ'⇒⇛ᵒ

  ⁺⟨⟩ᵀᵒ-kr⁻¹ :  ⁺⟨ ĩ₁ kr ⟩ᵀᵒ[ ι ] Pᵒ˙  ⊨
                ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⌜ (kr , M) ⇒ᴷᴿ∑ ⌝ᵒ×
                  (∀ᵒ e , ∀ᵒ M' , ⌜ (kr , M) ⇒ᴷᴿ (e , M') ⌝ᵒ→
                    ⟨ M ⟩⇛ᵒ⟨ M' ⟩ ⟨ e ⟩ᵀᵒ[< ι ] Pᵒ˙)
  ⁺⟨⟩ᵀᵒ-kr⁻¹ (⁺⟨⟩ᵀᵒ-kr' big) =  λ M → big M ▷ ⇛ᵒ'⇒⇛ᵒ ▷ ⇛ᵒ-mono λ (krM⇒ , big) →
    krM⇒ , λ e M' krM⇒eM' → big e M' krM⇒eM' ▷ ⇛ᵒ'⇒⇛ᵒ

  -- Monoᵒ for ⁺⟨⟩ᴾᵒ / ⁺⟨⟩ᵀᵒ

  ⁺⟨⟩ᴾᵒ-Mono :  Monoᵒ $ ⁺⟨ vk ⟩ᴾᵒ[ ι ] Pᵒ˙
  ⁺⟨⟩ᴾᵒ-Mono {vk = ĩ₀ _} a⊑b =
    ⁺⟨⟩ᴾᵒ-val⁻¹ › ∀ᵒ-Mono (λ _ → ⇛ᵒ-Mono) a⊑b › ⁺⟨⟩ᴾᵒ-val
  ⁺⟨⟩ᴾᵒ-Mono {vk = ĩ₁ _} a⊑b =
    ⁺⟨⟩ᴾᵒ-kr⁻¹ › ∀ᵒ-Mono (λ _ → ⇛ᵒ-Mono) a⊑b › ⁺⟨⟩ᴾᵒ-kr

  ⁺⟨⟩ᵀᵒ-Mono :  Monoᵒ $ ⁺⟨ vk ⟩ᵀᵒ[ ι ] Pᵒ˙
  ⁺⟨⟩ᵀᵒ-Mono {vk = ĩ₀ _} a⊑b =
    ⁺⟨⟩ᵀᵒ-val⁻¹ › ∀ᵒ-Mono (λ _ → ⇛ᵒ-Mono) a⊑b › ⁺⟨⟩ᵀᵒ-val
  ⁺⟨⟩ᵀᵒ-Mono {vk = ĩ₁ _} a⊑b =
    ⁺⟨⟩ᵀᵒ-kr⁻¹ › ∀ᵒ-Mono (λ _ → ⇛ᵒ-Mono) a⊑b › ⁺⟨⟩ᵀᵒ-kr

  -- Monotonicity of ⁺⟨⟩ᴾᵒ / ⁺⟨⟩ᵀᵒ

  ⁺⟨⟩ᴾᵒ-mono✓ :  (∀ v → Pᵒ˙ v ⊨✓ Qᵒ˙ v) →
                 ⁺⟨ vk ⟩ᴾᵒ[ ι ] Pᵒ˙ ⊨ ⁺⟨ vk ⟩ᴾᵒ[ ι ] Qᵒ˙
  ⁺⟨⟩ᴾᵒ-mono✓ {vk = ĩ₀ _} Pv⊨✓Qv ⟨v⟩P =  ⁺⟨⟩ᴾᵒ-val λ M → ⁺⟨⟩ᴾᵒ-val⁻¹ ⟨v⟩P M ▷
    ⇛ᵒ-mono✓ (Pv⊨✓Qv _)
  ⁺⟨⟩ᴾᵒ-mono✓ {vk = ĩ₁ _} Pv⊨✓Qv ⟨kr⟩P =  ⁺⟨⟩ᴾᵒ-kr λ M → ⁺⟨⟩ᴾᵒ-kr⁻¹ ⟨kr⟩P M ▷
    ⇛ᵒ-mono λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' → big e M' krM⇒eM' ▷
    ⇛ᵒ-mono λ big → λ{ .! → ⁺⟨⟩ᴾᵒ-mono✓ Pv⊨✓Qv $ big .! }

  ⁺⟨⟩ᴾᵒ-mono :  (∀ v → Pᵒ˙ v ⊨ Qᵒ˙ v) →  ⁺⟨ vk ⟩ᴾᵒ[ ι ] Pᵒ˙ ⊨ ⁺⟨ vk ⟩ᴾᵒ[ ι ] Qᵒ˙
  ⁺⟨⟩ᴾᵒ-mono =  (⊨⇒⊨✓ ∘_) › ⁺⟨⟩ᴾᵒ-mono✓

  ⁺⟨⟩ᵀᵒ-mono✓ :  (∀ v → Pᵒ˙ v ⊨✓ Qᵒ˙ v) →
                 ⁺⟨ vk ⟩ᵀᵒ[ ι ] Pᵒ˙ ⊨ ⁺⟨ vk ⟩ᵀᵒ[ ι ] Qᵒ˙
  ⁺⟨⟩ᵀᵒ-mono✓ {vk = ĩ₀ _} Pv⊨✓Qv ⟨v⟩P =  ⁺⟨⟩ᵀᵒ-val λ M → ⁺⟨⟩ᵀᵒ-val⁻¹ ⟨v⟩P M ▷
    ⇛ᵒ-mono✓ (Pv⊨✓Qv _)
  ⁺⟨⟩ᵀᵒ-mono✓ {vk = ĩ₁ _} {ι = ι} Pv⊨✓Qv ⟨kr⟩P =  ⁺⟨⟩ᵀᵒ-kr λ M →
    ⁺⟨⟩ᵀᵒ-kr⁻¹ ⟨kr⟩P M ▷ ⇛ᵒ-mono λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' →
    big e M' krM⇒eM' ▷
    ⇛ᵒ-mono λ{ (§ big) → §_ {ι = ι} $ ⁺⟨⟩ᵀᵒ-mono✓ Pv⊨✓Qv big }

  ⁺⟨⟩ᵀᵒ-mono :  (∀ v → Pᵒ˙ v ⊨ Qᵒ˙ v) →  ⁺⟨ vk ⟩ᵀᵒ[ ι ] Pᵒ˙ ⊨ ⁺⟨ vk ⟩ᵀᵒ[ ι ] Qᵒ˙
  ⁺⟨⟩ᵀᵒ-mono =  (⊨⇒⊨✓ ∘_) › ⁺⟨⟩ᵀᵒ-mono✓

  -- Modify the size of ⁺⟨⟩ᴾᵒ / ⁺⟨⟩ᵀᵒ

  ⁺⟨⟩ᴾᵒ-size :  ∀{ι' : Size< ι} →  ⁺⟨ vk ⟩ᴾᵒ[ ι ] Pᵒ˙  ⊨  ⁺⟨ vk ⟩ᴾᵒ[ ι' ] Pᵒ˙
  ⁺⟨⟩ᴾᵒ-size ⟨vk⟩P =  ⟨vk⟩P

  ⁺⟨⟩ᵀᵒ-size :  ∀{ι' : Size< ι} →  ⁺⟨ vk ⟩ᵀᵒ[ ι' ] Pᵒ˙  ⊨  ⁺⟨ vk ⟩ᵀᵒ[ ι ] Pᵒ˙
  ⁺⟨⟩ᵀᵒ-size ⟨vk⟩P =  ⟨vk⟩P

  -- Convert ⁺⟨⟩ᵀᵒ into ⁺⟨⟩ᴾᵒ

  ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ :  ⁺⟨ vk ⟩ᵀᵒ[ ι ] Pᵒ˙  ⊨  ⁺⟨ vk ⟩ᴾᵒ[ ι' ] Pᵒ˙
  ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ {vk = ĩ₀ _} ⟨v⟩P =  ⁺⟨⟩ᴾᵒ-val $ ⁺⟨⟩ᵀᵒ-val⁻¹ ⟨v⟩P
  ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ {vk = ĩ₁ _} ⟨kr⟩P =  ⁺⟨⟩ᴾᵒ-kr λ M → ⁺⟨⟩ᵀᵒ-kr⁻¹ ⟨kr⟩P M ▷ ⇛ᵒ-mono
    λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' → big e M' krM⇒eM' ▷
    ⇛ᵒ-mono λ{ (§ big) → λ{ .! → ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ big }}

  -- ⁺⟨⟩ᴾᵒ / ⁺⟨⟩ᵀᵒ absorbs ⇛ᵒ outside itself

  ⇛ᵒ-⁺⟨⟩ᴾᵒ :  ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⁺⟨ vk ⟩ᴾᵒ[ ι ] Pᵒ˙  ⊨  ⁺⟨ vk ⟩ᴾᵒ[ ι ] Pᵒ˙
  ⇛ᵒ-⁺⟨⟩ᴾᵒ {vk = ĩ₀ _} ⇛⟨v⟩P =  ⁺⟨⟩ᴾᵒ-val λ M → ⇛⟨v⟩P M ▷
    ⇛ᵒ-mono (⁺⟨⟩ᴾᵒ-val⁻¹ › _$ M) ▷ ⇛ᵒ-join
  ⇛ᵒ-⁺⟨⟩ᴾᵒ {vk = ĩ₁ _} ⇛⟨kr⟩P =  ⁺⟨⟩ᴾᵒ-kr λ M → ⇛⟨kr⟩P M ▷
    ⇛ᵒ-mono (⁺⟨⟩ᴾᵒ-kr⁻¹ › _$ M) ▷ ⇛ᵒ-join

  ⇛ᵒ-⁺⟨⟩ᵀᵒ :  ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ ⁺⟨ vk ⟩ᵀᵒ[ ι ] Pᵒ˙  ⊨  ⁺⟨ vk ⟩ᵀᵒ[ ι ] Pᵒ˙
  ⇛ᵒ-⁺⟨⟩ᵀᵒ {vk = ĩ₀ _} ⇛⟨v⟩P =  ⁺⟨⟩ᵀᵒ-val λ M → ⇛⟨v⟩P M ▷
    ⇛ᵒ-mono (⁺⟨⟩ᵀᵒ-val⁻¹ › _$ M) ▷ ⇛ᵒ-join
  ⇛ᵒ-⁺⟨⟩ᵀᵒ {vk = ĩ₁ _} ⇛⟨kr⟩P =  ⁺⟨⟩ᵀᵒ-kr λ M → ⇛⟨kr⟩P M ▷
    ⇛ᵒ-mono (⁺⟨⟩ᵀᵒ-kr⁻¹ › _$ M) ▷ ⇛ᵒ-join

  -- ⊨✓ into ⊨ when the right-hand side is ⁺⟨⟩ᴾᵒ / ⁺⟨⟩ᵀᵒ

  ⊨✓⇒⊨-⁺⟨⟩ᴾᵒ :  Pᵒ ⊨✓ ⁺⟨ vk ⟩ᴾᵒ[ ι ] Qᵒ˙ →  Pᵒ ⊨ ⁺⟨ vk ⟩ᴾᵒ[ ι ] Qᵒ˙
  ⊨✓⇒⊨-⁺⟨⟩ᴾᵒ P⊨✓⟨vk⟩Q Pa =  ⇛ᵒ-⁺⟨⟩ᴾᵒ λ _ → Pa ▷ ⊨✓⇒⊨-⇛ᵒ λ ✓∙ →
    P⊨✓⟨vk⟩Q ✓∙ › ⇛ᵒ-intro

  ⊨✓⇒⊨-⁺⟨⟩ᵀᵒ :  Pᵒ ⊨✓ ⁺⟨ vk ⟩ᵀᵒ[ ι ] Qᵒ˙ →  Pᵒ ⊨ ⁺⟨ vk ⟩ᵀᵒ[ ι ] Qᵒ˙
  ⊨✓⇒⊨-⁺⟨⟩ᵀᵒ P⊨✓⟨vk⟩Q Pa =  ⇛ᵒ-⁺⟨⟩ᵀᵒ λ _ → Pa ▷ ⊨✓⇒⊨-⇛ᵒ λ ✓∙ →
    P⊨✓⟨vk⟩Q ✓∙ › ⇛ᵒ-intro

  -- ⁺⟨⟩ᴾᵒ / ⁺⟨⟩ᵀᵒ absorbs ⇛ᵒ inside itself

  ⁺⟨⟩ᴾᵒ-⇛ᵒ :  ⁺⟨ vk ⟩ᴾᵒ[ ι ] (λ v → ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ˙ v)  ⊨
              ⁺⟨ vk ⟩ᴾᵒ[ ι ] Pᵒ˙
  ⁺⟨⟩ᴾᵒ-⇛ᵒ {vk = ĩ₀ _} ⟨v⟩⇛P =  ⁺⟨⟩ᴾᵒ-val λ M → ⁺⟨⟩ᴾᵒ-val⁻¹ ⟨v⟩⇛P M ▷
    ⇛ᵒ-mono (_$ M) ▷ ⇛ᵒ-join
  ⁺⟨⟩ᴾᵒ-⇛ᵒ {vk = ĩ₁ _} ⟨kr⟩⇛P =  ⁺⟨⟩ᴾᵒ-kr λ M → ⁺⟨⟩ᴾᵒ-kr⁻¹ ⟨kr⟩⇛P M ▷ ⇛ᵒ-mono
    λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' → big e M' krM⇒eM' ▷
    ⇛ᵒ-mono λ big → λ{ .! → ⁺⟨⟩ᴾᵒ-⇛ᵒ $ big .! }

  ⁺⟨⟩ᵀᵒ-⇛ᵒ :  ⁺⟨ vk ⟩ᵀᵒ[ ι ] (λ v → ∀ᵒ M , ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ˙ v)  ⊨
              ⁺⟨ vk ⟩ᵀᵒ[ ι ] Pᵒ˙
  ⁺⟨⟩ᵀᵒ-⇛ᵒ {vk = ĩ₀ _} ⟨v⟩⇛P =  ⁺⟨⟩ᵀᵒ-val λ M → ⁺⟨⟩ᵀᵒ-val⁻¹ ⟨v⟩⇛P M ▷
    ⇛ᵒ-mono (_$ M) ▷ ⇛ᵒ-join
  ⁺⟨⟩ᵀᵒ-⇛ᵒ {vk = ĩ₁ _} {ι = ι} ⟨kr⟩⇛P =  ⁺⟨⟩ᵀᵒ-kr λ M → ⁺⟨⟩ᵀᵒ-kr⁻¹ ⟨kr⟩⇛P M ▷
    ⇛ᵒ-mono λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' → big e M' krM⇒eM' ▷
    ⇛ᵒ-mono λ{ (§ big) → §_ {ι = ι} $ ⁺⟨⟩ᵀᵒ-⇛ᵒ big }

  -- ⁺⟨⟩ᴾᵒ / ⁺⟨⟩ᵀᵒ can eat a proposition

  ⁺⟨⟩ᴾᵒ-eatˡ :  Qᵒ ∗ᵒ (⁺⟨ vk ⟩ᴾᵒ[ ι ] Pᵒ˙)  ⊨  ⁺⟨ vk ⟩ᴾᵒ[ ι ] λ v → Qᵒ ∗ᵒ Pᵒ˙ v
  ⁺⟨⟩ᴾᵒ-eatˡ {vk = ĩ₀ _} Q∗⟨v⟩P =  ⁺⟨⟩ᴾᵒ-val λ M → Q∗⟨v⟩P ▷
    ∗ᵒ-monoʳ (⁺⟨⟩ᴾᵒ-val⁻¹ › _$ M) ▷ ⇛ᵒ-eatˡ
  ⁺⟨⟩ᴾᵒ-eatˡ {vk = ĩ₁ _} Q∗⟨kr⟩P =  ⁺⟨⟩ᴾᵒ-kr λ M → Q∗⟨kr⟩P ▷
    ∗ᵒ-monoʳ (⁺⟨⟩ᴾᵒ-kr⁻¹ › _$ M) ▷ ⇛ᵒ-eatˡ ▷ ⇛ᵒ-mono $ ∗ᵒ∃ᵒ-out ›
    λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' → big ▷
    ∗ᵒ-monoʳ (λ big → big e M' krM⇒eM') ▷ ⇛ᵒ-eatˡ ▷
    ⇛ᵒ-mono $ ∗ᵒThunkᵒ-out › λ big → λ{ .! → big .! ▷ ⁺⟨⟩ᴾᵒ-eatˡ }

  ⁺⟨⟩ᵀᵒ-eatˡ :  Qᵒ ∗ᵒ (⁺⟨ vk ⟩ᵀᵒ[ ι ] Pᵒ˙)  ⊨  ⁺⟨ vk ⟩ᵀᵒ[ ι ] λ v → Qᵒ ∗ᵒ Pᵒ˙ v
  ⁺⟨⟩ᵀᵒ-eatˡ {vk = ĩ₀ _} Q∗⟨v⟩P =  ⁺⟨⟩ᵀᵒ-val λ M → Q∗⟨v⟩P ▷
    ∗ᵒ-monoʳ (⁺⟨⟩ᵀᵒ-val⁻¹ › _$ M) ▷ ⇛ᵒ-eatˡ
  ⁺⟨⟩ᵀᵒ-eatˡ {vk = ĩ₁ _} {ι = ι} Q∗⟨kr⟩P =  ⁺⟨⟩ᵀᵒ-kr λ M → Q∗⟨kr⟩P ▷
    ∗ᵒ-monoʳ (⁺⟨⟩ᵀᵒ-kr⁻¹ › _$ M) ▷ ⇛ᵒ-eatˡ ▷ ⇛ᵒ-mono $ ∗ᵒ∃ᵒ-out ›
    λ (krM⇒ , big) → krM⇒ , λ e M' krM⇒eM' → big ▷
    ∗ᵒ-monoʳ (λ big → big e M' krM⇒eM') ▷ ⇛ᵒ-eatˡ ▷
    ⇛ᵒ-mono $ ∗ᵒShrunkᵒ-out › λ{ (§ big) → §_ {ι = ι} $ ⁺⟨⟩ᵀᵒ-eatˡ big }
