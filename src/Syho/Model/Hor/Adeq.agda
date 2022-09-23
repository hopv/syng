--------------------------------------------------------------------------------
-- Adequacy of the semantic partial and total weakest preconditions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Hor.Adeq where

open import Base.Level using (Level; 2ᴸ)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Few using (⊤)
open import Base.Eq using (_≡_)
open import Base.Acc using (Acc; acc)
open import Base.Size using (Size; ∞; Size₀; sz; sz⁻¹; _<ˢ_; size<; !; §_;
  <ˢ-wf)
open import Base.Prod using (_×_; π₀; π₁; _,_; -,_)
open import Base.Sum using (ĩ₁_)
open import Base.Option using (¿_; ň; š_)
open import Base.List using (List; []; _∷_; _$ᴸ_; _∈ᴸ_; ∈ʰᵈ; ∈ᵗˡ_; aug-refl;
  aug-∷; _≺ᴰᴹ⟨_⟩_; ≺ᴰᴹ-hd; ≺ᴰᴹ-tl; ≺ᴰᴹ-wf)
open import Syho.Lang.Expr using (Type; ◸_; Expr; Val; V⇒E)
open import Syho.Lang.Ktxred using (Ktxred; val/ktxred; val/ktxred-V⇒E)
open import Syho.Lang.Reduce using (Mem; ✓ᴹ_; _⇒ᴷᴿ∑; redᴱ; _⇒ᵀ_; _⇐ᵀ_; redᵀ-hd;
  redᵀ-tl; _⇒ᵀ*_; ⇒ᵀ*-refl; ⇒ᵀ*-step)
open import Syho.Model.ERA.Glob using (Resᴳ; _✓ᴳ_; Envᴵⁿᴳ; envᴳ; empᴵⁿᴳ-✓)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨_; ⊨_; ∃ᵒ-syntax; ⌜_⌝ᵒ;
  ⌜_⌝ᵒ×_; _∗ᵒ_; [∗ᵒ∈]-syntax; [∗ᵒ∈²]-syntax; ∗ᵒ⇒∗ᵒ'; ∗ᵒ'⇒∗ᵒ; ∗ᵒ-mono; ∗ᵒ-monoˡ;
  ∗ᵒ-monoʳ; ∗ᵒ-assocˡ; ?∗ᵒ-comm; ∗ᵒ?-intro; ∗ᵒ-elimˡ; ∗ᵒ-elimʳ; [∗ᵒ]-Mono;
  Thunkᵒ-Mono; Shrunkᵒ-Mono; Shrunkᵒ-mono; Shrunkᵒ∗ᵒ-out; ∗ᵒShrunkᵒ-out)
open import Syho.Model.Supd.Interp using (⟨_⟩⇛ᵒ⟨_⟩_; Invᴳ; Invᴳ-emp; ⇛ᵒ-mono;
  ⇛ᵒ-intro; ⇛ᵒ-join; ⇛ᵒ-eatˡ; ⇛ᵒ-eatʳ; ⇛ᵒ-adeq; ⇛ᵒ-step)
open import Syho.Model.Hor.Wp using (⟨_⟩ᴾᵒ[_]_; ⟨_⟩ᵀᵒ[_]_; ⟨_⟩ᴾᵒ⊤[_]; ⟨_⟩ᵀᵒ⊤[_];
  ⁺⟨⟩ᴾᵒ-val⁻¹; ⁺⟨⟩ᴾᵒ-kr⁻¹; ⁺⟨⟩ᵀᵒ-kr⁻¹; ⁺⟨⟩ᴾᵒ-Mono; ⁺⟨⟩ᴾᵒ⊤-Mono; ⁺⟨⟩ᵀᵒ-Mono;
  ⁺⟨⟩ᴾᵒ⊤⇒⁺⟨⟩ᴾᵒ; ⁺⟨⟩ᵀᵒ⊤⇒⁺⟨⟩ᵀᵒ; ⁺⟨⟩ᴾᵒ⇒⁺⟨⟩ᴾᵒ⊤; ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᵀᵒ⊤; ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ)

private variable
  ł :  Level
  ι :  Size
  ιs :  List Size₀
  M M' :  Mem
  T :  Type
  e⁺ e e' :  Expr ∞ T
  eˇ :  ¿ Expr ∞ (◸ ⊤)
  es es' :  List (Expr ∞ (◸ ⊤))
  v :  Val T
  kr' :  Ktxred T
  Pᵒ˙ :  Val T → Propᵒ ł
  X˙ :  Val T → Set ł
  Eᴵⁿ :  Envᴵⁿᴳ
  a :  Resᴳ

--------------------------------------------------------------------------------
-- Adequacy of the semantic partial weakest precondition

-- Separating conjunction of ⟨ ⟩ᴾᵒ⊤[ ∞ ] over expressions of type ◸ ⊤

[∗ᵒ]⟨_⟩ᴾᵒ⊤[∞] :  List (Expr ∞ (◸ ⊤)) →  Propᵒ 2ᴸ
[∗ᵒ]⟨ es ⟩ᴾᵒ⊤[∞] =  [∗ᵒ e ∈ es ] ⟨ e ⟩ᴾᵒ⊤[ ∞ ]

abstract

  -- Monoᵒ for [∗ᵒ]⟨ ⟩ᴾᵒ⊤[∞]

  [∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-Mono :  Monoᵒ [∗ᵒ]⟨ es ⟩ᴾᵒ⊤[∞]
  [∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-Mono {es = es} =  [∗ᵒ]-Mono {Pᵒs = ⟨_⟩ᴾᵒ⊤[ ∞ ] $ᴸ es}

  -- Eliminate [∗ᵒ]⟨⟩ᴾᵒ⊤[∞] with ∈ᴸ

  [∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-elim :  e ∈ᴸ es →  [∗ᵒ]⟨ es ⟩ᴾᵒ⊤[∞]  ⊨  ⟨ e ⟩ᴾᵒ⊤[ ∞ ]
  [∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-elim ∈ʰᵈ =  ∗ᵒ-elimˡ ⁺⟨⟩ᴾᵒ⊤-Mono
  [∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-elim {es = _ ∷ es'} (∈ᵗˡ ∈es') =
    ∗ᵒ-elimʳ ([∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-Mono {es = es'}) › [∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-elim ∈es'

  -- Lemma: If (e , es , M) ⇒ᵀ (e' , es' , M'),
  -- then ⟨ e ⟩ᴾᵒ[ ∞ ] Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es ⟩ᴾᵒ⊤[∞] entails
  -- ⟨ e' ⟩ᴾᵒ[ ∞ ] Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es' ⟩ᴾᵒ⊤[∞] under ⟨ M ⟩⇛ᵒ⟨ M' ⟩

  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ :  (e , es , M) ⇒ᵀ (e' , es' , M') →
    (⟨ e ⟩ᴾᵒ[ ∞ ] Pᵒ˙) ∗ᵒ [∗ᵒ]⟨ es ⟩ᴾᵒ⊤[∞]  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩
      (⟨ e' ⟩ᴾᵒ[ ∞ ] Pᵒ˙) ∗ᵒ [∗ᵒ]⟨ es' ⟩ᴾᵒ⊤[∞]
  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ (redᵀ-hd (redᴱ {eˇ = ň} e≡kr e'M'⇐krM))  rewrite e≡kr =
    ∗ᵒ-monoˡ (⁺⟨⟩ᴾᵒ-kr⁻¹ › (_$ _) › ⇛ᵒ-mono (λ big → big .π₁ _ _ _ e'M'⇐krM) ›
      ⇛ᵒ-join › ⇛ᵒ-mono $ ∗ᵒ-elimˡ (Thunkᵒ-Mono ⁺⟨⟩ᴾᵒ-Mono) › λ big → big .!) ›
    ⇛ᵒ-eatʳ
  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ (redᵀ-hd (redᴱ {eˇ = š _} e≡kr e'e⁺M'⇐krM))  rewrite e≡kr =
    ∗ᵒ-monoˡ (⁺⟨⟩ᴾᵒ-kr⁻¹ › (_$ _) › ⇛ᵒ-mono (λ big → big .π₁ _ _ _ e'e⁺M'⇐krM) ›
      ⇛ᵒ-join › ⇛ᵒ-mono $ ∗ᵒ-mono (λ big → big .!) (λ big → big .!)) ›
    ⇛ᵒ-eatʳ › ⇛ᵒ-mono ∗ᵒ-assocˡ
  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ (redᵀ-tl es'M'⇐esM) =
    ∗ᵒ-monoʳ (∗ᵒ-monoˡ ⁺⟨⟩ᴾᵒ⊤⇒⁺⟨⟩ᴾᵒ › ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ es'M'⇐esM) ›
    ⇛ᵒ-eatˡ › ⇛ᵒ-mono $ ∗ᵒ-monoʳ $ ∗ᵒ-monoˡ ⁺⟨⟩ᴾᵒ⇒⁺⟨⟩ᴾᵒ⊤

  -- Lemma: If (e , es , M) ⇒ᵀ* (e' , es' , M'),
  -- then ⟨ e ⟩ᴾᵒ[ ∞ ] Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es ⟩ᴾᵒ⊤[∞] entails
  -- ⟨ e' ⟩ᴾᵒ[ ∞ ] Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es' ⟩ᴾᵒ⊤[∞] under ⟨ M ⟩⇛ᵒ⟨ M' ⟩

  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ* :  (e , es , M) ⇒ᵀ* (e' , es' , M') →
    (⟨ e ⟩ᴾᵒ[ ∞ ] Pᵒ˙) ∗ᵒ [∗ᵒ]⟨ es ⟩ᴾᵒ⊤[∞]  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩
      (⟨ e' ⟩ᴾᵒ[ ∞ ] Pᵒ˙) ∗ᵒ [∗ᵒ]⟨ es' ⟩ᴾᵒ⊤[∞]
  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ* ⇒ᵀ*-refl =  ⇛ᵒ-intro
  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ* (⇒ᵀ*-step M⇒ᵀM'' M''⇒ᵀ*M') =
    ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ M⇒ᵀM'' ›
    ⇛ᵒ-mono (⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ* M''⇒ᵀ*M') › ⇛ᵒ-join

  -- ⊨ ⟨ e ⟩ᴾᵒ[ ∞ ]/ᵀᵒ[ ι ] λ u → ⌜ X˙ u ⌝ᵒ ensures that the X˙ v holds for the
  -- result value v of any reduction sequence starting with (e , [] , M) for
  -- valid M

  ⟨⟩ᴾᵒ-post :  ⊨ ⟨ e ⟩ᴾᵒ[ ∞ ] (λ u → ⌜ X˙ u ⌝ᵒ) →  ✓ᴹ M →
               (e , [] , M) ⇒ᵀ* (V⇒E v , es , M') →  X˙ v
  ⟨⟩ᴾᵒ-post {v = v} ⊨⟨e⟩X ✓M eM⇒*vesM' with (λ{a} → ⊨⟨e⟩X {a} ▷ ∗ᵒ?-intro _ ▷
    ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ* eM⇒*vesM' ▷ ⇛ᵒ-mono $ ∗ᵒ-elimˡ ⁺⟨⟩ᴾᵒ-Mono)
  … | ⊨M⇛M'⟨v⟩X  rewrite val/ktxred-V⇒E {v = v} =  ⇛ᵒ-adeq ✓M
    (⊨M⇛M'⟨v⟩X ▷ ⇛ᵒ-mono (⁺⟨⟩ᴾᵒ-val⁻¹ › (_$ _)) ▷ ⇛ᵒ-join)

  -- If (⟨ e ⟩ᴾᵒ[ ∞ ] Pᵒ˙) is a tautology, then any reduction sequence starting
  -- with (e , [] , M) never gets stuck for valid M

  -- For the head thread

  ⟨⟩ᴾᵒ-nostuck-hd :  ⊨ ⟨ e ⟩ᴾᵒ[ ∞ ] Pᵒ˙ →  ✓ᴹ M →
    (e , [] , M) ⇒ᵀ* (e' , es , M') →  val/ktxred e' ≡ ĩ₁ kr' →  (kr' , M') ⇒ᴷᴿ∑
  ⟨⟩ᴾᵒ-nostuck-hd ⊨⟨e⟩P ✓M eM⇒*e'esM' e'≡kr' with (λ{a} → ⊨⟨e⟩P {a} ▷
    ∗ᵒ?-intro _ ▷ ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ* eM⇒*e'esM' ▷
    ⇛ᵒ-mono $ ∗ᵒ-elimˡ ⁺⟨⟩ᴾᵒ-Mono)
  … | ⊨M⇛M'⟨e'⟩P  rewrite e'≡kr' =  ⇛ᵒ-adeq ✓M
    (⊨M⇛M'⟨e'⟩P ▷ ⇛ᵒ-mono (⁺⟨⟩ᴾᵒ-kr⁻¹ › (_$ _) › ⇛ᵒ-mono π₀) ▷ ⇛ᵒ-join)

  -- For a tail thread

  ⟨⟩ᴾᵒ-nostuck-tl :  ⊨ ⟨ e ⟩ᴾᵒ[ ∞ ] Pᵒ˙ →  ✓ᴹ M →
    (e , [] , M) ⇒ᵀ* (e' , es , M') →  e⁺ ∈ᴸ es →  val/ktxred e⁺ ≡ ĩ₁ kr' →
    (kr' , M') ⇒ᴷᴿ∑
  ⟨⟩ᴾᵒ-nostuck-tl {es = es} ⊨⟨e⟩P ✓M eM⇒*e'esM' e⁺∈es e⁺≡kr' with (λ{a} →
    ⊨⟨e⟩P {a} ▷ ∗ᵒ?-intro _ ▷ ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ* eM⇒*e'esM' ▷
    ⇛ᵒ-mono $ ∗ᵒ-elimʳ ([∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-Mono {es = es}) › [∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-elim e⁺∈es)
  … | ⊨M⇛M'⟨e⁺⟩  rewrite e⁺≡kr' =  ⇛ᵒ-adeq ✓M (⊨M⇛M'⟨e⁺⟩ ▷
    ⇛ᵒ-mono (⁺⟨⟩ᴾᵒ⊤⇒⁺⟨⟩ᴾᵒ › ⁺⟨⟩ᴾᵒ-kr⁻¹ › (_$ _) › ⇛ᵒ-mono π₀) ▷ ⇛ᵒ-join)

--------------------------------------------------------------------------------
-- Adequacy of the semantic total weakest precondition

-- Separating conjunction of ⟨ ⟩ᵀᵒ⊤[ ] over expressions of type ◸ ⊤ and sizes

[∗ᵒ]⟨_⟩ᵀᵒ⊤[_] :  List (Expr ∞ (◸ ⊤)) →  List Size₀ →  Propᵒ 2ᴸ
[∗ᵒ]⟨ es ⟩ᵀᵒ⊤[ ιs ] =  [∗ᵒ (e , sz ι) ∈² es , ιs ] ⟨ e ⟩ᵀᵒ⊤[ ι ]

abstract

  -- On the postcondition

  ⟨⟩ᵀᵒ-post :  ⊨ ⟨ e ⟩ᵀᵒ[ ∞ ] (λ u → ⌜ X˙ u ⌝ᵒ) →  ✓ᴹ M →
               (e , [] , M) ⇒ᵀ* (V⇒E v , es , M') →  X˙ v
  ⟨⟩ᵀᵒ-post ⊨⟨e⟩X =  ⟨⟩ᴾᵒ-post $ λ{a} → ⊨⟨e⟩X {a} ▷ ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ

  -- On the no-stuck property

  ⟨⟩ᵀᵒ-nostuck-hd :  ⊨ ⟨ e ⟩ᵀᵒ[ ∞ ] Pᵒ˙ →  ✓ᴹ M →
    (e , [] , M) ⇒ᵀ* (e' , es , M') →  val/ktxred e' ≡ ĩ₁ kr' →  (kr' , M') ⇒ᴷᴿ∑
  ⟨⟩ᵀᵒ-nostuck-hd ⊨⟨e⟩P =  ⟨⟩ᴾᵒ-nostuck-hd $ λ{a} → ⊨⟨e⟩P {a} ▷ ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ

  ⟨⟩ᵀᵒ-nostuck-tl :  ⊨ ⟨ e ⟩ᵀᵒ[ ∞ ] Pᵒ˙ →  ✓ᴹ M →
    (e , [] , M) ⇒ᵀ* (e' , es , M') →  e⁺ ∈ᴸ es →  val/ktxred e⁺ ≡ ĩ₁ kr' →
    (kr' , M') ⇒ᴷᴿ∑
  ⟨⟩ᵀᵒ-nostuck-tl ⊨⟨e⟩P =  ⟨⟩ᴾᵒ-nostuck-tl $ λ{a} → ⊨⟨e⟩P {a} ▷ ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ

  -- Lemma: If (e , es , M) ⇒ᵀ (e' , es' , M'),
  -- then ⟨ e ⟩ᵀᵒ[ ι ] Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es ⟩ᵀᵒ⊤[ ιs ] entails
  -- ⟨ e' ⟩ᵀᵒ[ ι' ] Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es' ⟩ᵀᵒ⊤[ ιs' ] under ⟨ M ⟩⇛ᵒ⟨ M' ⟩
  -- for some ι', ιs' satisfying sz ι' ∷ ιs' ≺ᴰᴹ⟨ _<ˢ_ ⟩ sz ι ∷ ιs

  ⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ :  (e , es , M) ⇒ᵀ (e' , es' , M') →
    (⟨ e ⟩ᵀᵒ[ ι ] Pᵒ˙) ∗ᵒ [∗ᵒ]⟨ es ⟩ᵀᵒ⊤[ ιs ]  ⊨  ⟨ M ⟩⇛ᵒ⟨ M' ⟩
      ∃ᵒ ι₀' , ∃ᵒ ιs' , ⌜ ι₀' ∷ ιs' ≺ᴰᴹ⟨ _<ˢ_ ⟩ sz ι ∷ ιs ⌝ᵒ×
      (⟨ e' ⟩ᵀᵒ[ sz⁻¹ ι₀' ] Pᵒ˙) ∗ᵒ [∗ᵒ]⟨ es' ⟩ᵀᵒ⊤[ ιs' ]
  ⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ (redᵀ-hd (redᴱ {eˇ = ň} e≡kr e'M'⇐krM))  rewrite e≡kr =
    ∗ᵒ-monoˡ (⁺⟨⟩ᵀᵒ-kr⁻¹ › (_$ _) › ⇛ᵒ-mono (λ big → big .π₁ _ _ _ e'M'⇐krM) ›
      ⇛ᵒ-join) › ⇛ᵒ-eatʳ › ⇛ᵒ-mono $
    ∗ᵒ-monoˡ (∗ᵒ-elimˡ $ Shrunkᵒ-Mono ⁺⟨⟩ᵀᵒ-Mono) › Shrunkᵒ∗ᵒ-out ›
    λ{ (§ big) → -, -, ≺ᴰᴹ-hd $ aug-∷ size< aug-refl , big }
  ⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ (redᵀ-hd (redᴱ {eˇ = š _} e≡kr e'e⁺M'⇐krM))  rewrite e≡kr =
    ∗ᵒ-monoˡ (⁺⟨⟩ᵀᵒ-kr⁻¹ › (_$ _) › ⇛ᵒ-mono (λ big → big .π₁ _ _ _ e'e⁺M'⇐krM) ›
      ⇛ᵒ-join) › ⇛ᵒ-eatʳ › ⇛ᵒ-mono $ ∗ᵒ-assocˡ › Shrunkᵒ∗ᵒ-out › λ{ (§ big) →
    big ▷ ?∗ᵒ-comm ▷ Shrunkᵒ∗ᵒ-out ▷ λ{ (§ big) → -, -,
    ≺ᴰᴹ-hd $ aug-∷ size< $ aug-∷ size< aug-refl , ?∗ᵒ-comm big }}
  ⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ {ιs = _ ∷ _} (redᵀ-tl esM⇒es'M') =
    ∗ᵒ-monoʳ (∗ᵒ-monoˡ ⁺⟨⟩ᵀᵒ⊤⇒⁺⟨⟩ᵀᵒ › ⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ esM⇒es'M') › ⇛ᵒ-eatˡ ›
    ⇛ᵒ-mono $ ∗ᵒ⇒∗ᵒ' › λ (-, -, ∙⊑ , ⟨e⟩P , -, -, ι'∷ιs'≺ , ⟨es'⟩) → -, -,
    ≺ᴰᴹ-tl ι'∷ιs'≺ , ∗ᵒ'⇒∗ᵒ (-, -, ∙⊑ , ⟨e⟩P , ∗ᵒ-monoˡ ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᵀᵒ⊤ ⟨es'⟩)
  ⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ {ιs = []} (redᵀ-tl _) =  ∗ᵒ⇒∗ᵒ' › λ ()

  -- ⊨ ⟨ e ⟩ᵀᵒ[ ι ] Pᵒ˙ ensures that (e , [] , M) is accessible with respect to
  -- ⇐ᵀ, i.e., any reduction sequence starting with (e , M) eventually
  -- terminates, for valid M

  ⟨⟩ᵀᵒ⇒acc :  ⊨ ⟨ e ⟩ᵀᵒ[ ι ] Pᵒ˙ →  ✓ᴹ M →  Acc _⇐ᵀ_ (e , [] , M)
  ⟨⟩ᵀᵒ⇒acc ⊨⟨e⟩P ✓M =  go {ιs = []} (≺ᴰᴹ-wf <ˢ-wf) (empᴵⁿᴳ-✓ ✓M)
    (⊨⟨e⟩P ▷ ∗ᵒ?-intro _ ▷ ∗ᵒ?-intro Invᴳ-emp)
   where
    -- Induction with the termination metric sz ι ∷ ιs
    go :  Acc _≺ᴰᴹ⟨ _<ˢ_ ⟩_ (sz ι ∷ ιs) →  envᴳ M Eᴵⁿ ✓ᴳ a →
          (((⟨ e ⟩ᵀᵒ[ ι ] Pᵒ˙) ∗ᵒ [∗ᵒ]⟨ es ⟩ᵀᵒ⊤[ ιs ]) ∗ᵒ Invᴳ Eᴵⁿ) a  →
          Acc _⇐ᵀ_ (e , es , M)
    go (acc ≺ι∷ιs⇒acc) ME✓a ⟨e⟩P∗⟨es⟩∗InvEa =  acc λ eesM⇒e'es'M' →
      ⟨e⟩P∗⟨es⟩∗InvEa ▷ ∗ᵒ-monoˡ (⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ eesM⇒e'es'M') ▷
      ⇛ᵒ-step ME✓a ▷ λ (-, -, M'E'✓b , big) → ∗ᵒ⇒∗ᵒ' big ▷
      λ (-, -, ∙⊑ , (-, -, ≺ι∷ιs , big) , InvE') →
      go (≺ι∷ιs⇒acc ≺ι∷ιs) M'E'✓b $ ∗ᵒ'⇒∗ᵒ (-, -, ∙⊑ , big , InvE')
