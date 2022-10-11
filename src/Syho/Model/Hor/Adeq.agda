--------------------------------------------------------------------------------
-- Adequacy of the semantic partial and total weakest preconditions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Hor.Adeq where

open import Base.Level using (Level; 1ᴸ; 3ᴸ)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Few using (⊤; ⊥₀; absurd)
open import Base.Eq using (_≡_; refl)
open import Base.Acc using (Acc; acc)
open import Base.Size using (Size; ∞; Size'; sz; sz⁻¹; _<ˢ_; size<; !; §_;
  <ˢ-wf)
open import Base.Bool using (tt; ff)
open import Base.Prod using (∑-syntax; _×_; π₀; π₁; _,_; -,_)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Base.Option using (¿_; ň; š_)
open import Base.List using (List; []; _∷_; ¿⇒ᴸ; _⧺_; _$ᴸ_; _∈ᴸ_; ∈ʰᵈ; ∈ᵗˡ_;
  aug-refl; aug-∷; _≺ᴰᴹ⟨_⟩_; Rᴰᴹ; ≺ᴰᴹ-hd; ≺ᴰᴹ-tl; ≺ᴰᴹ-wf)
open import Base.Sety using ()
open import Syho.Lang.Expr using (Type; ◸_; Expr∞; Val; V⇒E; Mem; ✓ᴹ_)
open import Syho.Lang.Ktxred using (Ktxred; val/ktxred; val/ktxred-ĩ₀;
  val/ktxred-V⇒E)
open import Syho.Lang.Reduce using ([]⇒; redᴷᴿ; _⇒ᴷᴿ∑; redᴱ; _⇒ᵀ_; _⇒ᵀ○_; _⇒ᵀ●_;
  redᵀ-hd; redᵀ-tl; _⇒ᵀ*_; ⇒ᵀ*-refl; ⇒ᵀ*-step; SNᵀ; Infᵀ; infᵀ)
open import Syho.Model.ERA.Glob using (Resᴳ; _✓ᴳ_; Envᴵⁿᴳ; envᴳ; empᴵⁿᴳ-✓[⊤])
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨_; ⊨_; ∃ᵒ-syntax;
  ⌜_⌝ᵒ; ⌜_⌝ᵒ×_; ⊥ᵒ₀; _∗ᵒ_; [∗ᵒ∈]-syntax; [∗ᵒ∈²]-syntax; Thunkᵒ; substᵒ;
  ⌜⌝ᵒ-Mono; ∗ᵒ⇒∗ᵒ'; ∗ᵒ'⇒∗ᵒ; ∗ᵒ-mono; ∗ᵒ-monoˡ; ∗ᵒ-monoʳ; ∗ᵒ-assocˡ; ∗ᵒ-assocʳ;
  ?∗ᵒ-comm; ∗ᵒ?-intro; ∗ᵒ-elimˡ; ∗ᵒ-elimʳ; [∗ᵒ]-Mono; [∗ᵒ∈²]-Mono; -∗ᵒ-applyˡ;
  ◎-just; Shrunkᵒ∗ᵒ-out)
open import Syho.Model.Prop.Names using ([⊤]ᴺᵒ)
open import Syho.Model.Supd.Interp using (⟨_⟩⇛ᴹ⟨_⟩_; Invᴳ; Invᴳ-emp; ⇛ᴹ-Mono;
  ⇛ᴹ-mono✓; ⇛ᴹ-mono; ⊨✓⇒⊨-⇛ᴹ; ⇛ᴹ-intro; ⇛ᴹ-join; ⇛ᴹ-eatˡ; ⇛ᴹ-eatʳ; ⇛ᴹ-adeq;
  ⇛ᴹ-step)
open import Syho.Model.Hor.Wp using (⁺⟨_⟩ᴾᵒ; ⟨_⟩ᴾᵒ; ⟨_⟩ᵀᵒ; ⟨_⟩∞ᵒ; ⟨_⟩ᵀᵒ˂;
  ⟨_⟩∞ᵒ˂ˡ; ⟨_⟩∞ᵒ˂ʳ; ⟨_⟩ᴾᵒ⊤; ⟨_⟩ᵀᵒ⊤; ⟨¿_⟩ᴾᵒ⊤˂; ⟨¿_⟩ᵀᵒ⊤˂; ⁺⟨⟩ᴾᵒ-val⁻¹; ⁺⟨⟩ᴾᵒ-kr⁻¹;
  ⁺⟨⟩ᵀᵒ-kr⁻¹; ⁺⟨⟩∞ᵒ-kr⁻¹; ⁺⟨⟩ᴾᵒ-Mono; ⁺⟨⟩ᴾᵒ⊤-Mono; ⁺⟨⟩ᵀᵒ-Mono; ⁺⟨⟩∞ᵒ-Mono;
  ∀ᵒ⇛ᴹ-Mono; ⁺⟨⟩ᴾᵒ⊤⇒⁺⟨⟩ᴾᵒ; ⁺⟨⟩ᵀᵒ⊤⇒⁺⟨⟩ᵀᵒ; ⁺⟨⟩ᴾᵒ⇒⁺⟨⟩ᴾᵒ⊤; ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᵀᵒ⊤;
  ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ; ⁺⟨⟩∞ᵒ⇒⁺⟨⟩ᴾᵒ)

private variable
  ł :  Level
  ι ι₀ ι' :  Size
  ιs :  List (Size' 3ᴸ)
  M M' :  Mem
  X :  Set₀
  T :  Type
  e⁺ e e' :  Expr∞ T
  eˇ eˇ' :  ¿ Expr∞ (◸ ⊤)
  es es' :  List (Expr∞ (◸ ⊤))
  v :  X
  kr :  Ktxred T
  Pᵒ˙ :  X → Propᵒ ł
  X˙ :  X → Set ł
  Eᴵⁿ :  Envᴵⁿᴳ
  a :  Resᴳ

--------------------------------------------------------------------------------
-- Adequacy of the semantic partial weakest precondition

-- Separating conjunction of ⟨ ⟩ᴾᵒ⊤ ∞ over expressions of type ◸ ⊤

[∗ᵒ]⟨_⟩ᴾᵒ⊤∞ :  List (Expr∞ (◸ ⊤)) →  Propᵒ 1ᴸ
[∗ᵒ]⟨ es ⟩ᴾᵒ⊤∞ =  [∗ᵒ e ∈ es ] ⟨ e ⟩ᴾᵒ⊤ ∞

abstract

  -- Monoᵒ for [∗ᵒ]⟨ ⟩ᴾᵒ⊤∞

  [∗ᵒ]⟨⟩ᴾᵒ⊤∞-Mono :  Monoᵒ [∗ᵒ]⟨ es ⟩ᴾᵒ⊤∞
  [∗ᵒ]⟨⟩ᴾᵒ⊤∞-Mono {es = es} =  [∗ᵒ]-Mono {Pᵒs = (λ e → ⟨ e ⟩ᴾᵒ⊤ ∞) $ᴸ es}

  -- Eliminate [∗ᵒ]⟨⟩ᴾᵒ⊤∞ with ∈ᴸ

  [∗ᵒ]⟨⟩ᴾᵒ⊤∞-elim :  e ∈ᴸ es →  [∗ᵒ]⟨ es ⟩ᴾᵒ⊤∞  ⊨  ⟨ e ⟩ᴾᵒ⊤ ∞
  [∗ᵒ]⟨⟩ᴾᵒ⊤∞-elim ∈ʰᵈ =  ∗ᵒ-elimˡ ⁺⟨⟩ᴾᵒ⊤-Mono
  [∗ᵒ]⟨⟩ᴾᵒ⊤∞-elim {es = _ ∷ es'} (∈ᵗˡ ∈es') =
    ∗ᵒ-elimʳ ([∗ᵒ]⟨⟩ᴾᵒ⊤∞-Mono {es = es'}) › [∗ᵒ]⟨⟩ᴾᵒ⊤∞-elim ∈es'

  -- Lemma: If (e , es , M) ⇒ᵀ (e' , es' , M'),
  -- then ⟨ e ⟩ᴾᵒ ∞ Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es ⟩ᴾᵒ⊤∞ entails
  -- ⟨ e' ⟩ᴾᵒ ∞ Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es' ⟩ᴾᵒ⊤∞ under ⟨ M ⟩⇛ᴹ⟨ M' ⟩ with [⊤]ᴺᵒ

  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤∞-⇒ᵀ :  (e , es , M) ⇒ᵀ (e' , es' , M') →
    [⊤]ᴺᵒ ∗ᵒ ⟨ e ⟩ᴾᵒ ∞ Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es ⟩ᴾᵒ⊤∞  ⊨ ⟨ M ⟩⇛ᴹ⟨ M' ⟩
      [⊤]ᴺᵒ ∗ᵒ ⟨ e' ⟩ᴾᵒ ∞ Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es' ⟩ᴾᵒ⊤∞
  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤∞-⇒ᵀ (-, redᵀ-hd {es = es} (redᴱ {eˇ = eˇ} e⇒kr e'eˇM'⇐))
    rewrite e⇒kr =  ∗ᵒ-assocʳ › ∗ᵒ-monoˡ (⊨✓⇒⊨-⇛ᴹ λ ✓∙ → ∗ᵒ-monoʳ ⁺⟨⟩ᴾᵒ-kr⁻¹ ›
    -∗ᵒ-applyˡ ∀ᵒ⇛ᴹ-Mono ✓∙ › (_$ _) › ⇛ᴹ-mono (λ (-, big) →
    big _ _ _ (-, e'eˇM'⇐) ▷ ⇛ᴹ-mono (∗ᵒ-monoʳ $ ∗ᵒ-monoˡ λ big → big .!)) ›
    ⇛ᴹ-join) › ⇛ᴹ-eatʳ › ⇛ᴹ-mono $ ∗ᵒ-assocˡ › ∗ᵒ-monoʳ $ ∗ᵒ-assocˡ ›
    ∗ᵒ-monoʳ $ go {eˇ}
   where
    go :  ⟨¿ eˇ' ⟩ᴾᵒ⊤˂ ∞ ∗ᵒ [∗ᵒ]⟨ es ⟩ᴾᵒ⊤∞  ⊨  [∗ᵒ]⟨ ¿⇒ᴸ eˇ' ⧺ es ⟩ᴾᵒ⊤∞
    go {ň} =  ∗ᵒ-elimʳ $ [∗ᵒ]⟨⟩ᴾᵒ⊤∞-Mono {es = es}
    go {š _} =  ∗ᵒ-monoˡ λ big → big .!
  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤∞-⇒ᵀ (-, redᵀ-tl es'M'⇐esM) =  ?∗ᵒ-comm › ∗ᵒ-monoʳ
    (∗ᵒ-monoʳ (∗ᵒ-monoˡ ⁺⟨⟩ᴾᵒ⊤⇒⁺⟨⟩ᴾᵒ) › ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤∞-⇒ᵀ (-, es'M'⇐esM)) ›
    ⇛ᴹ-eatˡ › ⇛ᴹ-mono $ ?∗ᵒ-comm › ∗ᵒ-monoʳ $ ∗ᵒ-monoʳ $ ∗ᵒ-monoˡ ⁺⟨⟩ᴾᵒ⇒⁺⟨⟩ᴾᵒ⊤

  -- Lemma: If (e , es , M) ⇒ᵀ* (e' , es' , M'),
  -- then ⟨ e ⟩ᴾᵒ ∞ Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es ⟩ᴾᵒ⊤∞ entails
  -- ⟨ e' ⟩ᴾᵒ ∞ Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es' ⟩ᴾᵒ⊤∞ under ⟨ M ⟩⇛ᴹ⟨ M' ⟩ with [⊤]ᴺᵒ

  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤∞-⇒ᵀ* :  (e , es , M) ⇒ᵀ* (e' , es' , M') →
    [⊤]ᴺᵒ ∗ᵒ ⟨ e ⟩ᴾᵒ ∞ Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es ⟩ᴾᵒ⊤∞  ⊨ ⟨ M ⟩⇛ᴹ⟨ M' ⟩
      [⊤]ᴺᵒ ∗ᵒ ⟨ e' ⟩ᴾᵒ ∞ Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es' ⟩ᴾᵒ⊤∞
  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤∞-⇒ᵀ* ⇒ᵀ*-refl =  ⇛ᴹ-intro
  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤∞-⇒ᵀ* (⇒ᵀ*-step M⇒ᵀM'' M''⇒ᵀ*M') =  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤∞-⇒ᵀ M⇒ᵀM'' ›
    ⇛ᴹ-mono (⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤∞-⇒ᵀ* M''⇒ᵀ*M') › ⇛ᴹ-join

  -- ⊨ ⟨ e ⟩ᴾᵒ ∞ λ u → ⌜ X˙ u ⌝ᵒ ensures that the X˙ v holds for the
  -- result value v of any reduction sequence starting with (e , [] , M) for
  -- valid M

  ⟨⟩ᴾᵒ-post :  ⊨ ⟨ e ⟩ᴾᵒ ∞ (λ u → ⌜ X˙ u ⌝ᵒ) →  ✓ᴹ M →
               (e , [] , M) ⇒ᵀ* (V⇒E {T} v , es , M') →  X˙ v
  ⟨⟩ᴾᵒ-post ⊨⟨e⟩X ✓M eM⇒*vesM' =  ⇛ᴹ-adeq ✓M $ ∗ᵒ?-intro (⊨⟨e⟩X ▷ ∗ᵒ?-intro _) ›
    ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤∞-⇒ᵀ* eM⇒*vesM' › ⇛ᴹ-mono✓ (λ ✓∙ →
    ∗ᵒ-monoʳ (∗ᵒ-elimˡ ⁺⟨⟩ᴾᵒ-Mono ›
    substᵒ (λ kr → ⁺⟨ kr ⟩ᴾᵒ ∞ _) (val/ktxred-V⇒E) › ⁺⟨⟩ᴾᵒ-val⁻¹) ›
    -∗ᵒ-applyˡ ∀ᵒ⇛ᴹ-Mono ✓∙ › (_$ _) › ⇛ᴹ-mono $ ∗ᵒ-elimʳ ⌜⌝ᵒ-Mono) › ⇛ᴹ-join

  -- If ⟨ e ⟩ᴾᵒ ∞ Pᵒ˙ is a tautology, then any reduction sequence starting with
  -- (e , [] , M) never gets stuck for valid M

  -- For the main thread

  ⟨⟩ᴾᵒ-progress-main :  ⊨ ⟨ e ⟩ᴾᵒ ∞ Pᵒ˙ →  ✓ᴹ M →
    (e , [] , M) ⇒ᵀ* (e' , es , M') →  val/ktxred e' ≡ ĩ₁ kr →  (kr , M') ⇒ᴷᴿ∑
  ⟨⟩ᴾᵒ-progress-main ⊨⟨e⟩P ✓M eM⇒*e'esM' e'≡kr =  ⇛ᴹ-adeq ✓M $
    ∗ᵒ?-intro (⊨⟨e⟩P ▷ ∗ᵒ?-intro _) › ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤∞-⇒ᵀ* eM⇒*e'esM' ›
    ⇛ᴹ-mono✓ (λ ✓∙ → ∗ᵒ-monoʳ (∗ᵒ-elimˡ ⁺⟨⟩ᴾᵒ-Mono ›
    substᵒ (λ kr → ⁺⟨ kr ⟩ᴾᵒ ∞ _) e'≡kr › ⁺⟨⟩ᴾᵒ-kr⁻¹) ›
    -∗ᵒ-applyˡ ∀ᵒ⇛ᴹ-Mono ✓∙ › (_$ _) › ⇛ᴹ-mono π₀) › ⇛ᴹ-join

  -- For forked threads

  ⟨⟩ᴾᵒ-progress-forked :
    ⊨ ⟨ e ⟩ᴾᵒ ∞ Pᵒ˙ →  ✓ᴹ M →  (e , [] , M) ⇒ᵀ* (e' , es , M') →  e⁺ ∈ᴸ es →
    val/ktxred e⁺ ≡ ĩ₁ kr →  (kr , M') ⇒ᴷᴿ∑
  ⟨⟩ᴾᵒ-progress-forked {es = es} ⊨⟨e⟩P ✓M eM⇒*e'esM' e⁺∈es e⁺≡kr =  ⇛ᴹ-adeq ✓M $
    ∗ᵒ?-intro (⊨⟨e⟩P ▷ ∗ᵒ?-intro _) › ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤∞-⇒ᵀ* eM⇒*e'esM' ›
    ⇛ᴹ-mono✓ (λ ✓∙ → ∗ᵒ-monoʳ (∗ᵒ-elimʳ ([∗ᵒ]⟨⟩ᴾᵒ⊤∞-Mono {es = es}) ›
    [∗ᵒ]⟨⟩ᴾᵒ⊤∞-elim e⁺∈es › ⁺⟨⟩ᴾᵒ⊤⇒⁺⟨⟩ᴾᵒ ›
    substᵒ (λ kr → ⁺⟨ kr ⟩ᴾᵒ ∞ _) e⁺≡kr › ⁺⟨⟩ᴾᵒ-kr⁻¹) ›
    -∗ᵒ-applyˡ ∀ᵒ⇛ᴹ-Mono ✓∙ › (_$ _) › ⇛ᴹ-mono π₀) › ⇛ᴹ-join

--------------------------------------------------------------------------------
-- Adequacy of the semantic total weakest precondition

-- Separating conjunction of ⟨ ⟩ᵀᵒ⊤ over expressions of type ◸ ⊤ and sizes

[∗ᵒ]⟨_⟩ᵀᵒ⊤ :  List (Expr∞ (◸ ⊤)) →  List (Size' 3ᴸ) →  Propᵒ 1ᴸ
[∗ᵒ]⟨ es ⟩ᵀᵒ⊤ ιs =  [∗ᵒ (e , sz ι) ∈² es , ιs ] ⟨ e ⟩ᵀᵒ⊤ ι

abstract

  -- Monoᵒ for [∗ᵒ]⟨ ⟩ᵀᵒ⊤

  [∗ᵒ]⟨⟩ᵀᵒ⊤-Mono :  Monoᵒ $ [∗ᵒ]⟨ es ⟩ᵀᵒ⊤ ιs
  [∗ᵒ]⟨⟩ᵀᵒ⊤-Mono {es} =  [∗ᵒ∈²]-Mono {xs = es}

  -- On the postcondition

  ⟨⟩ᵀᵒ-post :  ⊨ ⟨ e ⟩ᵀᵒ ∞ (λ u → ⌜ X˙ u ⌝ᵒ) →  ✓ᴹ M →
               (e , [] , M) ⇒ᵀ* (V⇒E v , es , M') →  X˙ v
  ⟨⟩ᵀᵒ-post ⊨⟨e⟩X =  ⟨⟩ᴾᵒ-post $ λ{a} → ⊨⟨e⟩X {a} ▷ ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ

  -- On the progress property

  ⟨⟩ᵀᵒ-progress-main :  ⊨ ⟨ e ⟩ᵀᵒ ∞ Pᵒ˙ →  ✓ᴹ M →
    (e , [] , M) ⇒ᵀ* (e' , es , M') →  val/ktxred e' ≡ ĩ₁ kr →  (kr , M') ⇒ᴷᴿ∑
  ⟨⟩ᵀᵒ-progress-main ⊨⟨e⟩P =  ⟨⟩ᴾᵒ-progress-main $ ⊨⟨e⟩P ▷ ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ

  ⟨⟩ᵀᵒ-progress-forked :
    ⊨ ⟨ e ⟩ᵀᵒ ∞ Pᵒ˙ →  ✓ᴹ M →  (e , [] , M) ⇒ᵀ* (e' , es , M') →  e⁺ ∈ᴸ es →
    val/ktxred e⁺ ≡ ĩ₁ kr →  (kr , M') ⇒ᴷᴿ∑
  ⟨⟩ᵀᵒ-progress-forked ⊨⟨e⟩P =  ⟨⟩ᴾᵒ-progress-forked $ ⊨⟨e⟩P ▷ ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ

  -- Lemma: If (e , es , M) ⇒ᵀ (e' , es' , M'),
  -- then ⟨ e ⟩ᵀᵒ ι Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es ⟩ᵀᵒ⊤ ιs entails
  -- ⟨ e' ⟩ᵀᵒ ι' Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es' ⟩ᵀᵒ⊤ ιs' under ⟨ M ⟩⇛ᴹ⟨ M' ⟩ with [⊤]ᴺᵒ
  -- for some ι', ιs' satisfying sz ι' ∷ ιs' ≺ᴰᴹ⟨ _<ˢ_ ⟩ sz ι ∷ ιs

  ⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ :  (e , es , M) ⇒ᵀ (e' , es' , M') →
    [⊤]ᴺᵒ ∗ᵒ ⟨ e ⟩ᵀᵒ ι Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es ⟩ᵀᵒ⊤ ιs  ⊨ ⟨ M ⟩⇛ᴹ⟨ M' ⟩
      ∃ᵒ ι'⁺ , ∃ᵒ ιs' , ⌜ ι'⁺ ∷ ιs' ≺ᴰᴹ⟨ _<ˢ_ ⟩ sz ι ∷ ιs ⌝ᵒ×
        [⊤]ᴺᵒ ∗ᵒ ⟨ e' ⟩ᵀᵒ (sz⁻¹ ι'⁺) Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es' ⟩ᵀᵒ⊤ ιs'
  ⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ (-, redᵀ-hd {es = es} (redᴱ {eˇ = eˇ} e⇒kr e'eˇM'⇐))
    rewrite e⇒kr =  ∗ᵒ-assocʳ › ∗ᵒ-monoˡ (⊨✓⇒⊨-⇛ᴹ λ ✓∙ → ∗ᵒ-monoʳ ⁺⟨⟩ᵀᵒ-kr⁻¹ ›
    -∗ᵒ-applyˡ ∀ᵒ⇛ᴹ-Mono ✓∙ › (_$ _) ›
    ⇛ᴹ-mono (λ (-, big) → big _ _ _ (-, e'eˇM'⇐)) › ⇛ᴹ-join) › ⇛ᴹ-eatʳ ›
    ⇛ᴹ-mono $ ∗ᵒ-assocˡ › ∗ᵒ-monoʳ (∗ᵒ-assocˡ › go {eˇ' = eˇ}) › ∗ᵒ⇒∗ᵒ' ›
    λ{ (-, -, b∙c⊑a , [⊤]b , -, -, ι'∷ιs'≺ι∷ιs , big) →
    -, -, ι'∷ιs'≺ι∷ιs , ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , [⊤]b , big) }
   where
    go :  ⟨ e ⟩ᵀᵒ˂ ι Pᵒ˙ ∗ᵒ ⟨¿ eˇ' ⟩ᵀᵒ⊤˂ ι ∗ᵒ [∗ᵒ]⟨ es ⟩ᵀᵒ⊤ ιs ⊨
            ∃ᵒ ι'⁺ , ∃ᵒ ιs' , ⌜ ι'⁺ ∷ ιs' ≺ᴰᴹ⟨ _<ˢ_ ⟩ sz ι ∷ ιs ⌝ᵒ×
              ⟨ e ⟩ᵀᵒ (sz⁻¹ ι'⁺) Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ ¿⇒ᴸ eˇ' ⧺ es ⟩ᵀᵒ⊤ ιs'
    go {eˇ' = ň} =  Shrunkᵒ∗ᵒ-out › λ{ (§ big) → -, -,
      ≺ᴰᴹ-hd $ aug-∷ size< aug-refl ,
      big ▷ ∗ᵒ-monoʳ (∗ᵒ-elimʳ $ [∗ᵒ]⟨⟩ᵀᵒ⊤-Mono {es}) }
    go {eˇ' = š _} =  Shrunkᵒ∗ᵒ-out › λ{ (§ big) → big ▷ ?∗ᵒ-comm ▷
      Shrunkᵒ∗ᵒ-out ▷ λ{ (§ big) → -, -,
      ≺ᴰᴹ-hd $ aug-∷ size< $ aug-∷ size< aug-refl , big ▷ ?∗ᵒ-comm }}
  ⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ {ιs = []} (-, redᵀ-tl _) =  ∗ᵒ-assocʳ › ∗ᵒ⇒∗ᵒ' › λ ()
  ⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ {ιs = _ ∷ _} (-, redᵀ-tl esM⇒) =  ?∗ᵒ-comm ›
    ∗ᵒ-monoʳ (∗ᵒ-monoʳ (∗ᵒ-monoˡ ⁺⟨⟩ᵀᵒ⊤⇒⁺⟨⟩ᵀᵒ) › ⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ (-, esM⇒)) ›
    ⇛ᴹ-eatˡ › ⇛ᴹ-mono $ ∗ᵒ⇒∗ᵒ' › λ (-, -, ∙⊑ , ⟨e⟩P , -, -, ι'∷ιs'≺ , big) →
    -, -, ≺ᴰᴹ-tl ι'∷ιs'≺ ,
    ∗ᵒ'⇒∗ᵒ (-, -, ∙⊑ , ⟨e⟩P , big ▷ ∗ᵒ-monoʳ (∗ᵒ-monoˡ ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᵀᵒ⊤)) ▷ ?∗ᵒ-comm

  -- ⊨ ⟨ e ⟩ᵀᵒ ι Pᵒ˙ ensures that (e , [] , M) is strongly normalizing
  -- for valid M

  ⟨⟩ᵀᵒ⇒SN :  ⊨ ⟨ e ⟩ᵀᵒ ι Pᵒ˙ →  ✓ᴹ M →  SNᵀ (e , [] , M)
  ⟨⟩ᵀᵒ⇒SN ⊨⟨e⟩P ✓M =  go {ιs = []} (≺ᴰᴹ-wf <ˢ-wf) (empᴵⁿᴳ-✓[⊤] ✓M) $
    ◎-just ▷ ∗ᵒ?-intro (∗ᵒ?-intro _ ⊨⟨e⟩P) ▷ ∗ᵒ?-intro Invᴳ-emp
   where
    -- Well-founded induction by the metric sz ι ∷ ιs
    go :  Acc (Rᴰᴹ _<ˢ_) (sz ι ∷ ιs) →  envᴳ M Eᴵⁿ ✓ᴳ a →
      (([⊤]ᴺᵒ ∗ᵒ ⟨ e ⟩ᵀᵒ ι Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es ⟩ᵀᵒ⊤ ιs) ∗ᵒ Invᴳ Eᴵⁿ) a  →
      SNᵀ (e , es , M)
    go (acc ≺ι∷ιs⇒acc) ME✓a big =  acc λ eesM⇒ → big ▷
      ∗ᵒ-monoˡ (⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ eesM⇒) ▷ ⇛ᴹ-step ME✓a ▷
      λ (-, -, M'E'✓b , big) → ∗ᵒ⇒∗ᵒ' big ▷
      λ (-, -, ∙⊑ , (-, -, ≺ι∷ιs , big) , InvE') →
      go (≺ι∷ιs⇒acc ≺ι∷ιs) M'E'✓b $ ∗ᵒ'⇒∗ᵒ (-, -, ∙⊑ , big , InvE')

--------------------------------------------------------------------------------
-- Adequacy of the semantic infinite weakest precondition

abstract

  -- On the progress property
  -- The main thread never becomes a value

  ⟨⟩∞ᵒ-progress-main :
    ⊨ ⟨ e ⟩∞ᵒ ι ∞ →  ✓ᴹ M →  (e , [] , M) ⇒ᵀ* (e' , es , M') →
    ∑ kr ,  val/ktxred e' ≡ ĩ₁ kr  ×  (kr , M') ⇒ᴷᴿ∑
  ⟨⟩∞ᵒ-progress-main {e' = e'} ⊨⟨e⟩P ✓M eM⇒* with val/ktxred e' |
    (λ{v} → val/ktxred-ĩ₀ {e = e'} {v}) | (λ{kr} → ⟨⟩ᴾᵒ-progress-main
    {Pᵒ˙ = λ _ → ⊥ᵒ₀} {kr = kr} (⁺⟨⟩∞ᵒ⇒⁺⟨⟩ᴾᵒ ⊨⟨e⟩P) ✓M eM⇒*)
  … | ĩ₀ v | ⇒e'⇒v | _  rewrite ⇒e'⇒v refl =  absurd $
    ⟨⟩ᴾᵒ-post {X˙ = λ _ → ⊥₀} (⁺⟨⟩∞ᵒ⇒⁺⟨⟩ᴾᵒ ⊨⟨e⟩P) ✓M eM⇒*
  … | ĩ₁ kr | _ | ⇒krM'⇒ =  -, refl , ⇒krM'⇒ refl

  ⟨⟩∞ᵒ-progress-forked :
    ⊨ ⟨ e ⟩∞ᵒ ι ∞ →  ✓ᴹ M →  (e , [] , M) ⇒ᵀ* (e' , es , M') →  e⁺ ∈ᴸ es →
    val/ktxred e⁺ ≡ ĩ₁ kr →  (kr , M') ⇒ᴷᴿ∑
  ⟨⟩∞ᵒ-progress-forked ⊨⟨e⟩P =
    ⟨⟩ᴾᵒ-progress-forked $ ⊨⟨e⟩P ▷ ⁺⟨⟩∞ᵒ⇒⁺⟨⟩ᴾᵒ {Pᵒ˙ = λ _ → ⊥ᵒ₀}

  -- Lemma: If (e , es , M) ⇒ᵀ○ (e' , es' , M'),
  -- then ⟨ e ⟩∞ᵒ ι ι₀ ∗ᵒ [∗ᵒ]⟨ es ⟩ᵀᵒ⊤ ιs entails
  -- ⟨ e' ⟩∞ᵒ ι' ι₀ ∗ᵒ [∗ᵒ]⟨ es' ⟩ᵀᵒ⊤ ιs' under ⟨ M ⟩⇛ᴹ⟨ M' ⟩ with [⊤]ᴺᵒ
  -- for some ι', ιs' satisfying sz ι' ∷ ιs' ≺ᴰᴹ⟨ _<ˢ_ ⟩ sz ι ∷ ιs

  ⟨⟩∞ᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ○ :  (e , es , M) ⇒ᵀ○ (e' , es' , M') →
    [⊤]ᴺᵒ ∗ᵒ ⟨ e ⟩∞ᵒ ι ι₀ ∗ᵒ [∗ᵒ]⟨ es ⟩ᵀᵒ⊤ ιs  ⊨ ⟨ M ⟩⇛ᴹ⟨ M' ⟩
      ∃ᵒ ι'⁺ , ∃ᵒ ιs' , ⌜ ι'⁺ ∷ ιs' ≺ᴰᴹ⟨ _<ˢ_ ⟩ sz ι ∷ ιs ⌝ᵒ×
        [⊤]ᴺᵒ ∗ᵒ ⟨ e' ⟩∞ᵒ (sz⁻¹ ι'⁺) ι₀ ∗ᵒ [∗ᵒ]⟨ es' ⟩ᵀᵒ⊤ ιs'
  ⟨⟩∞ᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ○ (redᵀ-hd {es = es} (redᴱ {eˇ = eˇ} e⇒kr e'eˇM'⇐○))
    rewrite e⇒kr =  ∗ᵒ-assocʳ › ∗ᵒ-monoˡ (⊨✓⇒⊨-⇛ᴹ λ ✓∙ → ∗ᵒ-monoʳ ⁺⟨⟩∞ᵒ-kr⁻¹ ›
    -∗ᵒ-applyˡ ∀ᵒ⇛ᴹ-Mono ✓∙ › (_$ _) ›
    ⇛ᴹ-mono (λ (-, big) → big _ _ _ _ e'eˇM'⇐○) › ⇛ᴹ-join) › ⇛ᴹ-eatʳ ›
    ⇛ᴹ-mono $ ∗ᵒ-assocˡ › ∗ᵒ-monoʳ (∗ᵒ-assocˡ › go {eˇ' = eˇ}) › ∗ᵒ⇒∗ᵒ' ›
    λ{ (-, -, b∙c⊑a , [⊤]b , -, -, ι'∷ιs'≺ι∷ιs , big) →
    -, -, ι'∷ιs'≺ι∷ιs , ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , [⊤]b , big) }
   where
    go :  ⟨ e ⟩∞ᵒ˂ˡ ι ι₀ ∗ᵒ ⟨¿ eˇ' ⟩ᵀᵒ⊤˂ ι ∗ᵒ [∗ᵒ]⟨ es ⟩ᵀᵒ⊤ ιs ⊨
            ∃ᵒ ι'⁺ , ∃ᵒ ιs' , ⌜ ι'⁺ ∷ ιs' ≺ᴰᴹ⟨ _<ˢ_ ⟩ sz ι ∷ ιs ⌝ᵒ×
              ⟨ e ⟩∞ᵒ (sz⁻¹ ι'⁺) ι₀ ∗ᵒ [∗ᵒ]⟨ ¿⇒ᴸ eˇ' ⧺ es ⟩ᵀᵒ⊤ ιs'
    go {eˇ' = ň} =  Shrunkᵒ∗ᵒ-out › λ{ (§ big) → -, -,
      ≺ᴰᴹ-hd $ aug-∷ size< aug-refl ,
      big ▷ ∗ᵒ-monoʳ (∗ᵒ-elimʳ $ [∗ᵒ]⟨⟩ᵀᵒ⊤-Mono {es}) }
    go {eˇ' = š _} =  Shrunkᵒ∗ᵒ-out › λ{ (§ big) → big ▷ ?∗ᵒ-comm ▷
      Shrunkᵒ∗ᵒ-out ▷ λ{ (§ big) → -, -,
      ≺ᴰᴹ-hd $ aug-∷ size< $ aug-∷ size< aug-refl , big ▷ ?∗ᵒ-comm }}
  ⟨⟩∞ᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ○ {ιs = []} (redᵀ-tl _) =  ∗ᵒ-assocʳ › ∗ᵒ⇒∗ᵒ' › λ ()
  ⟨⟩∞ᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ○ {ιs = _ ∷ _} (redᵀ-tl esM⇒) =  ?∗ᵒ-comm ›
    ∗ᵒ-monoʳ (∗ᵒ-monoʳ (∗ᵒ-monoˡ ⁺⟨⟩ᵀᵒ⊤⇒⁺⟨⟩ᵀᵒ) › ⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ (-, esM⇒)) ›
    ⇛ᴹ-eatˡ › ⇛ᴹ-mono $ ∗ᵒ⇒∗ᵒ' › λ (-, -, ∙⊑ , ⟨e⟩P , -, -, ι'∷ιs'≺ , big) →
    -, -, ≺ᴰᴹ-tl ι'∷ιs'≺ ,
    ∗ᵒ'⇒∗ᵒ (-, -, ∙⊑ , ⟨e⟩P , big ▷ ∗ᵒ-monoʳ (∗ᵒ-monoˡ ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᵀᵒ⊤)) ▷ ?∗ᵒ-comm

  -- Lemma: If (e , es , M) ⇒ᵀ● (e' , es' , M'),
  -- then ⟨ e ⟩∞ᵒ ι ι₀ ∗ᵒ [∗ᵒ]⟨ es ⟩ᵀᵒ⊤ ιs entails
  -- ⟨ e' ⟩∞ᵒ ∞ - ∗ᵒ [∗ᵒ]⟨ es' ⟩ᵀᵒ⊤ ιs under ⟨ M ⟩⇛ᴹ⟨ M' ⟩ with [⊤]ᴺᵒ and Thunkᵒ

  ⟨⟩∞ᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ● :  (e , es , M) ⇒ᵀ● (e' , es' , M') →
    [⊤]ᴺᵒ ∗ᵒ ⟨ e ⟩∞ᵒ ι ι₀ ∗ᵒ [∗ᵒ]⟨ es ⟩ᵀᵒ⊤ ιs  ⊨ ⟨ M ⟩⇛ᴹ⟨ M' ⟩
      Thunkᵒ (λ ι₀' → [⊤]ᴺᵒ ∗ᵒ ⟨ e' ⟩∞ᵒ ∞ ι₀' ∗ᵒ [∗ᵒ]⟨ es' ⟩ᵀᵒ⊤ ιs) ι₀
  ⟨⟩∞ᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ● (redᵀ-hd (redᴱ e⇒kr (redᴷᴿ []⇒)))  rewrite e⇒kr =
    ∗ᵒ-assocʳ › ∗ᵒ-monoˡ (⊨✓⇒⊨-⇛ᴹ λ ✓∙ → ∗ᵒ-monoʳ ⁺⟨⟩∞ᵒ-kr⁻¹ ›
    -∗ᵒ-applyˡ ∀ᵒ⇛ᴹ-Mono ✓∙ › (_$ _) ›
    ⇛ᴹ-mono (λ (-, big) → big _ _ _ _ (redᴷᴿ []⇒)) › ⇛ᴹ-join) › ⇛ᴹ-eatʳ ›
    ⇛ᴹ-mono $ ∗ᵒ-assocˡ › λ big → λ{ .! → big ▷ ∗ᵒ-monoʳ
    (∗ᵒ-monoˡ $ ∗ᵒ-monoˡ (λ big → big .!) › ∗ᵒ-elimˡ ⁺⟨⟩∞ᵒ-Mono) }

  -- ⊨ ⟨ e ⟩∞ᵒ ι ∞ ensures that any execution from (e , [] , M) triggers the
  -- event an infinite number of times

  ⟨⟩∞ᵒ⇒Inf :  ⊨ ⟨ e ⟩∞ᵒ ι ι' →  ✓ᴹ M →  Infᵀ ι' (e , [] , M)
  ⟨⟩∞ᵒ⇒Inf ⊨⟨e⟩∞ ✓M =  go {ιs = []} (≺ᴰᴹ-wf <ˢ-wf) (empᴵⁿᴳ-✓[⊤] ✓M) $
    ◎-just ▷ ∗ᵒ?-intro (∗ᵒ?-intro _ ⊨⟨e⟩∞) ▷ ∗ᵒ?-intro Invᴳ-emp
   where
    -- Well-founded induction by the metric (ι' , sz ι ∷ ιs)
    go :  Acc (Rᴰᴹ _<ˢ_) (sz ι ∷ ιs) →  envᴳ M Eᴵⁿ ✓ᴳ a →
      (([⊤]ᴺᵒ ∗ᵒ ⟨ e ⟩∞ᵒ ι ι' ∗ᵒ [∗ᵒ]⟨ es ⟩ᵀᵒ⊤ ιs) ∗ᵒ Invᴳ Eᴵⁿ) a  →
      Infᵀ ι' (e , es , M)
    go (acc ≺ι∷ιs⇒acc) ME✓a big =  infᵀ λ{
      {b = ff} eesM⇒○ → big ▷ ∗ᵒ-monoˡ (⟨⟩∞ᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ○ eesM⇒○) ▷
        ⇛ᴹ-step ME✓a ▷ λ (-, -, M'E'✓b , big) → ∗ᵒ⇒∗ᵒ' big ▷
        λ (-, -, ∙⊑ , (-, -, ≺ι∷ιs , big) , InvE') →
        go (≺ι∷ιs⇒acc ≺ι∷ιs) M'E'✓b $ ∗ᵒ'⇒∗ᵒ (-, -, ∙⊑ , big , InvE');
      {b = tt} eesM⇒● .! → big ▷ ∗ᵒ-monoˡ (⟨⟩∞ᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ● eesM⇒●) ▷
        ⇛ᴹ-step ME✓a ▷ λ (-, -, M'E'✓b , big) →
        go (≺ᴰᴹ-wf <ˢ-wf) M'E'✓b $ big ▷ ∗ᵒ-monoˡ λ big → big .! }
