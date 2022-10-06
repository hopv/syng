--------------------------------------------------------------------------------
-- Adequacy of the semantic partial and total weakest preconditions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Hor.Adeq where

open import Base.Level using (Level; 1ᴸ)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Few using (⊤)
open import Base.Eq using (_≡_)
open import Base.Acc using (Acc; acc)
open import Base.Size using (Size; ∞; Size₀; sz; sz⁻¹; _<ˢ_; size<; !; §_;
  <ˢ-wf)
open import Base.Prod using (_×_; π₀; π₁; _,_; -,_)
open import Base.Sum using (ĩ₁_)
open import Base.Option using (¿_; ň; š_)
open import Base.List using (List; []; _∷_; ¿⇒ᴸ; _⧺_; _$ᴸ_; _∈ᴸ_; ∈ʰᵈ; ∈ᵗˡ_;
  aug-refl; aug-∷; _≺ᴰᴹ⟨_⟩_; Rᴰᴹ; ≺ᴰᴹ-hd; ≺ᴰᴹ-tl; ≺ᴰᴹ-wf)
open import Base.Sety using ()
open import Syho.Lang.Expr using (Type; ◸_; Expr∞; Val; V⇒E)
open import Syho.Lang.Ktxred using (Ktxred; val/ktxred; val/ktxred-V⇒E)
open import Syho.Lang.Reduce using (Mem; ✓ᴹ_; _⇒ᴷᴿ∑; redᴱ; _⇒ᵀ_; _⇐ᵀ_; redᵀ-hd;
  redᵀ-tl; _⇒ᵀ*_; ⇒ᵀ*-refl; ⇒ᵀ*-step)
open import Syho.Model.ERA.Glob using (Resᴳ; _✓ᴳ_; Envᴵⁿᴳ; envᴳ; empᴵⁿᴳ-✓)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨_; ⊨_; ∃ᵒ-syntax; ⌜_⌝ᵒ;
  ⌜_⌝ᵒ×_; _∗ᵒ_; [∗ᵒ∈]-syntax; [∗ᵒ∈²]-syntax; substᵒ; ⌜⌝ᵒ-Mono; ∗ᵒ⇒∗ᵒ'; ∗ᵒ'⇒∗ᵒ;
  ∗ᵒ-Mono; ∗ᵒ-monoˡ; ∗ᵒ-monoʳ; ∗ᵒ-assocˡ; ∗ᵒ-assocʳ; ?∗ᵒ-comm; ?∗ᵒ-intro;
  ∗ᵒ?-intro; ∗ᵒ-elimˡ; ∗ᵒ-elimʳ; [∗ᵒ]-Mono; -∗ᵒ-applyʳ; ◎-Mono; ◎-just;
  Shrunkᵒ∗ᵒ-out)
open import Syho.Model.Prop.Names using ([⊤]ᴺᵒ)
open import Syho.Model.Supd.Interp using (⟨_⟩⇛ᴹ⟨_⟩_; Invᴳ; Invᴳ-emp; ⇛ᴹ-Mono;
  ⇛ᴹ-mono✓; ⇛ᴹ-mono; ⊨✓⇒⊨-⇛ᴹ; ⇛ᴹ-intro; ⇛ᴹ-join; ⇛ᴹ-eatˡ; ⇛ᴹ-eatʳ; ⇛ᴹ-adeq;
  ⇛ᴹ-step)
open import Syho.Model.Hor.Wp using (⁺⟨_⟩ᴾᵒ[_]_; ⟨_⟩ᴾᵒ[_]_; ⟨_⟩ᵀᵒ[_]_;
  ⟨_⟩ᵀᵒ[<_]_; ⟨_⟩ᴾᵒ⊤[_]; ⟨_⟩ᵀᵒ⊤[_]; ⟨¿_⟩ᴾᵒ⊤[<_]; ⟨¿_⟩ᵀᵒ⊤[<_]; ⁺⟨⟩ᴾᵒ-val⁻¹;
  ⁺⟨⟩ᴾᵒ-kr⁻¹; ⁺⟨⟩ᵀᵒ-kr⁻¹; ⁺⟨⟩ᴾᵒ-Mono; ⁺⟨⟩ᴾᵒ⊤-Mono; ⁺⟨⟩ᵀᵒ-Mono; ∀ᵒ⇛ᴹ-Mono;
  ⁺⟨⟩ᴾᵒ⊤⇒⁺⟨⟩ᴾᵒ; ⁺⟨⟩ᵀᵒ⊤⇒⁺⟨⟩ᵀᵒ; ⁺⟨⟩ᴾᵒ⇒⁺⟨⟩ᴾᵒ⊤; ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᵀᵒ⊤; ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ)

private variable
  ł :  Level
  ι :  Size
  ιs :  List Size₀
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

-- Separating conjunction of ⟨ ⟩ᴾᵒ⊤[ ∞ ] over expressions of type ◸ ⊤

[∗ᵒ]⟨_⟩ᴾᵒ⊤[∞] :  List (Expr∞ (◸ ⊤)) →  Propᵒ 1ᴸ
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
  -- ⟨ e' ⟩ᴾᵒ[ ∞ ] Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es' ⟩ᴾᵒ⊤[∞] under ⟨ M ⟩⇛ᴹ⟨ M' ⟩

  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ :  (e , es , M) ⇒ᵀ (e' , es' , M') →
    (⟨ e ⟩ᴾᵒ[ ∞ ] Pᵒ˙) ∗ᵒ [∗ᵒ]⟨ es ⟩ᴾᵒ⊤[∞] ∗ᵒ [⊤]ᴺᵒ  ⊨ ⟨ M ⟩⇛ᴹ⟨ M' ⟩
      (⟨ e' ⟩ᴾᵒ[ ∞ ] Pᵒ˙) ∗ᵒ [∗ᵒ]⟨ es' ⟩ᴾᵒ⊤[∞] ∗ᵒ [⊤]ᴺᵒ
  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ (redᵀ-hd {es = es} (redᴱ {eˇ = eˇ} e≡kr e'eˇM'⇐))
    rewrite e≡kr =  ?∗ᵒ-comm › ∗ᵒ-monoʳ (⊨✓⇒⊨-⇛ᴹ λ ✓∙ → ∗ᵒ-monoˡ ⁺⟨⟩ᴾᵒ-kr⁻¹ ›
    -∗ᵒ-applyʳ ∀ᵒ⇛ᴹ-Mono ✓∙ › (_$ _) › ⇛ᴹ-mono (λ (-, big) → big _ _ _ e'eˇM'⇐ ▷
    ⇛ᴹ-mono (∗ᵒ-monoˡ λ big → big .!)) › ⇛ᴹ-join) › ⇛ᴹ-eatˡ ›
    ⇛ᴹ-mono $ ?∗ᵒ-comm › ∗ᵒ-monoʳ $ ?∗ᵒ-comm › ∗ᵒ-assocʳ › ∗ᵒ-monoˡ $ go {eˇ}
   where
    go :  ⟨¿ eˇ' ⟩ᴾᵒ⊤[< ∞ ] ∗ᵒ [∗ᵒ]⟨ es ⟩ᴾᵒ⊤[∞]  ⊨  [∗ᵒ]⟨ ¿⇒ᴸ eˇ' ⧺ es ⟩ᴾᵒ⊤[∞]
    go {ň} =  ∗ᵒ-elimʳ $ [∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-Mono {es = es}
    go {š _} =  ∗ᵒ-monoˡ λ big → big .!
  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ (redᵀ-tl es'M'⇐esM) =  ∗ᵒ-monoʳ
    (∗ᵒ-assocˡ › ∗ᵒ-monoˡ ⁺⟨⟩ᴾᵒ⊤⇒⁺⟨⟩ᴾᵒ › ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ es'M'⇐esM) ›
    ⇛ᴹ-eatˡ › ⇛ᴹ-mono $ ∗ᵒ-monoʳ $ ∗ᵒ-assocʳ › ∗ᵒ-monoˡ $ ∗ᵒ-monoˡ ⁺⟨⟩ᴾᵒ⇒⁺⟨⟩ᴾᵒ⊤

  -- Lemma: If (e , es , M) ⇒ᵀ* (e' , es' , M'),
  -- then ⟨ e ⟩ᴾᵒ[ ∞ ] Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es ⟩ᴾᵒ⊤[∞] entails
  -- ⟨ e' ⟩ᴾᵒ[ ∞ ] Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es' ⟩ᴾᵒ⊤[∞] under ⟨ M ⟩⇛ᴹ⟨ M' ⟩

  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ* :  (e , es , M) ⇒ᵀ* (e' , es' , M') →
    (⟨ e ⟩ᴾᵒ[ ∞ ] Pᵒ˙) ∗ᵒ [∗ᵒ]⟨ es ⟩ᴾᵒ⊤[∞] ∗ᵒ [⊤]ᴺᵒ  ⊨  ⟨ M ⟩⇛ᴹ⟨ M' ⟩
      (⟨ e' ⟩ᴾᵒ[ ∞ ] Pᵒ˙) ∗ᵒ [∗ᵒ]⟨ es' ⟩ᴾᵒ⊤[∞] ∗ᵒ [⊤]ᴺᵒ
  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ* ⇒ᵀ*-refl =  ⇛ᴹ-intro
  ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ* (⇒ᵀ*-step M⇒ᵀM'' M''⇒ᵀ*M') =
    ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ M⇒ᵀM'' ›
    ⇛ᴹ-mono (⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ* M''⇒ᵀ*M') › ⇛ᴹ-join

  -- ⊨ ⟨ e ⟩ᴾᵒ[ ∞ ]/ᵀᵒ[ ι ] λ u → ⌜ X˙ u ⌝ᵒ ensures that the X˙ v holds for the
  -- result value v of any reduction sequence starting with (e , [] , M) for
  -- valid M

  ⟨⟩ᴾᵒ-post :  ⊨ ⟨ e ⟩ᴾᵒ[ ∞ ] (λ u → ⌜ X˙ u ⌝ᵒ) →  ✓ᴹ M →
               (e , [] , M) ⇒ᵀ* (V⇒E {T} v , es , M') →  X˙ v
  ⟨⟩ᴾᵒ-post ⊨⟨e⟩X ✓M eM⇒*vesM' =  ⇛ᴹ-adeq ✓M $ ?∗ᵒ-intro _ › ?∗ᵒ-intro ⊨⟨e⟩X ›
    ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ* eM⇒*vesM' › ⇛ᴹ-mono✓ (λ ✓∙ → ∗ᵒ-assocʳ ›
    ∗ᵒ-monoˡ (∗ᵒ-elimˡ ⁺⟨⟩ᴾᵒ-Mono › substᵒ (⁺⟨_⟩ᴾᵒ[ ∞ ] _) (val/ktxred-V⇒E) ›
    ⁺⟨⟩ᴾᵒ-val⁻¹) › -∗ᵒ-applyʳ ∀ᵒ⇛ᴹ-Mono ✓∙ › (_$ _) ›
    ⇛ᴹ-mono $ ∗ᵒ-elimˡ ⌜⌝ᵒ-Mono) › ⇛ᴹ-join

  -- If (⟨ e ⟩ᴾᵒ[ ∞ ] Pᵒ˙) is a tautology, then any reduction sequence starting
  -- with (e , [] , M) never gets stuck for valid M

  -- For the head thread

  ⟨⟩ᴾᵒ-nostuck-hd :  ⊨ ⟨ e ⟩ᴾᵒ[ ∞ ] Pᵒ˙ →  ✓ᴹ M →
    (e , [] , M) ⇒ᵀ* (e' , es , M') →  val/ktxred e' ≡ ĩ₁ kr →  (kr , M') ⇒ᴷᴿ∑
  ⟨⟩ᴾᵒ-nostuck-hd ⊨⟨e⟩P ✓M eM⇒*e'esM' e'≡kr =  ⇛ᴹ-adeq ✓M $ ?∗ᵒ-intro _ ›
    ?∗ᵒ-intro ⊨⟨e⟩P › ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ* eM⇒*e'esM' › ⇛ᴹ-mono✓ (λ ✓∙ →
    ∗ᵒ-assocʳ › ∗ᵒ-monoˡ (∗ᵒ-elimˡ ⁺⟨⟩ᴾᵒ-Mono › substᵒ (⁺⟨_⟩ᴾᵒ[ ∞ ] _) e'≡kr ›
    ⁺⟨⟩ᴾᵒ-kr⁻¹) › -∗ᵒ-applyʳ ∀ᵒ⇛ᴹ-Mono ✓∙ › (_$ _) › ⇛ᴹ-mono π₀) › ⇛ᴹ-join

  -- For a tail thread

  ⟨⟩ᴾᵒ-nostuck-tl :  ⊨ ⟨ e ⟩ᴾᵒ[ ∞ ] Pᵒ˙ →  ✓ᴹ M →
    (e , [] , M) ⇒ᵀ* (e' , es , M') →  e⁺ ∈ᴸ es →  val/ktxred e⁺ ≡ ĩ₁ kr →
    (kr , M') ⇒ᴷᴿ∑
  ⟨⟩ᴾᵒ-nostuck-tl {es = es} ⊨⟨e⟩P ✓M eM⇒*e'esM' e⁺∈es e⁺≡kr =  ⇛ᴹ-adeq ✓M $
    ?∗ᵒ-intro _ › ?∗ᵒ-intro ⊨⟨e⟩P › ⟨⟩ᴾᵒ-[∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-⇒ᵀ* eM⇒*e'esM' › ⇛ᴹ-mono✓
    (λ ✓∙ → ∗ᵒ-assocʳ › ∗ᵒ-monoˡ (∗ᵒ-elimʳ ([∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-Mono {es = es}) ›
    [∗ᵒ]⟨⟩ᴾᵒ⊤[∞]-elim e⁺∈es › ⁺⟨⟩ᴾᵒ⊤⇒⁺⟨⟩ᴾᵒ › substᵒ (⁺⟨_⟩ᴾᵒ[ ∞ ] _) e⁺≡kr ›
    ⁺⟨⟩ᴾᵒ-kr⁻¹) › -∗ᵒ-applyʳ ∀ᵒ⇛ᴹ-Mono ✓∙ › (_$ _) › ⇛ᴹ-mono π₀) › ⇛ᴹ-join

--------------------------------------------------------------------------------
-- Adequacy of the semantic total weakest precondition

-- Separating conjunction of ⟨ ⟩ᵀᵒ⊤[ ] over expressions of type ◸ ⊤ and sizes

[∗ᵒ]⟨_⟩ᵀᵒ⊤[_] :  List (Expr∞ (◸ ⊤)) →  List Size₀ →  Propᵒ 1ᴸ
[∗ᵒ]⟨ es ⟩ᵀᵒ⊤[ ιs ] =  [∗ᵒ (e , sz ι) ∈² es , ιs ] ⟨ e ⟩ᵀᵒ⊤[ ι ]

abstract

  -- On the postcondition

  ⟨⟩ᵀᵒ-post :  ⊨ ⟨ e ⟩ᵀᵒ[ ∞ ] (λ u → ⌜ X˙ u ⌝ᵒ) →  ✓ᴹ M →
               (e , [] , M) ⇒ᵀ* (V⇒E v , es , M') →  X˙ v
  ⟨⟩ᵀᵒ-post ⊨⟨e⟩X =  ⟨⟩ᴾᵒ-post $ λ{a} → ⊨⟨e⟩X {a} ▷ ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ

  -- On the no-stuck property

  ⟨⟩ᵀᵒ-nostuck-hd :  ⊨ ⟨ e ⟩ᵀᵒ[ ∞ ] Pᵒ˙ →  ✓ᴹ M →
    (e , [] , M) ⇒ᵀ* (e' , es , M') →  val/ktxred e' ≡ ĩ₁ kr →  (kr , M') ⇒ᴷᴿ∑
  ⟨⟩ᵀᵒ-nostuck-hd ⊨⟨e⟩P =  ⟨⟩ᴾᵒ-nostuck-hd $ ⊨⟨e⟩P ▷ ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ

  ⟨⟩ᵀᵒ-nostuck-tl :  ⊨ ⟨ e ⟩ᵀᵒ[ ∞ ] Pᵒ˙ →  ✓ᴹ M →
    (e , [] , M) ⇒ᵀ* (e' , es , M') →  e⁺ ∈ᴸ es →  val/ktxred e⁺ ≡ ĩ₁ kr →
    (kr , M') ⇒ᴷᴿ∑
  ⟨⟩ᵀᵒ-nostuck-tl ⊨⟨e⟩P =  ⟨⟩ᴾᵒ-nostuck-tl $ ⊨⟨e⟩P ▷ ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ

  -- Lemma: If (e , es , M) ⇒ᵀ (e' , es' , M'),
  -- then ⟨ e ⟩ᵀᵒ[ ι ] Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es ⟩ᵀᵒ⊤[ ιs ] entails
  -- ⟨ e' ⟩ᵀᵒ[ ι' ] Pᵒ˙ ∗ᵒ [∗ᵒ]⟨ es' ⟩ᵀᵒ⊤[ ιs' ] under ⟨ M ⟩⇛ᴹ⟨ M' ⟩
  -- for some ι', ιs' satisfying sz ι' ∷ ιs' ≺ᴰᴹ⟨ _<ˢ_ ⟩ sz ι ∷ ιs

  ⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ :  (e , es , M) ⇒ᵀ (e' , es' , M') →
    (⟨ e ⟩ᵀᵒ[ ι ] Pᵒ˙) ∗ᵒ [∗ᵒ]⟨ es ⟩ᵀᵒ⊤[ ιs ] ∗ᵒ [⊤]ᴺᵒ  ⊨ ⟨ M ⟩⇛ᴹ⟨ M' ⟩
      ∃ᵒ ι₀' , ∃ᵒ ιs' , ⌜ ι₀' ∷ ιs' ≺ᴰᴹ⟨ _<ˢ_ ⟩ sz ι ∷ ιs ⌝ᵒ×
        (⟨ e' ⟩ᵀᵒ[ sz⁻¹ ι₀' ] Pᵒ˙) ∗ᵒ [∗ᵒ]⟨ es' ⟩ᵀᵒ⊤[ ιs' ] ∗ᵒ [⊤]ᴺᵒ
  ⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ (redᵀ-hd {es = es} (redᴱ {eˇ = eˇ} e≡kr e'eˇM'⇐))
    rewrite e≡kr =  ?∗ᵒ-comm › ∗ᵒ-monoʳ (⊨✓⇒⊨-⇛ᴹ λ ✓∙ → ∗ᵒ-monoˡ ⁺⟨⟩ᵀᵒ-kr⁻¹ ›
    -∗ᵒ-applyʳ ∀ᵒ⇛ᴹ-Mono ✓∙ › (_$ _) ›
    ⇛ᴹ-mono (λ (-, big) → big _ _ _ e'eˇM'⇐) › ⇛ᴹ-join) › ⇛ᴹ-eatˡ ›
    ⇛ᴹ-mono $ ?∗ᵒ-comm › ∗ᵒ-monoʳ ?∗ᵒ-comm › go {eˇ' = eˇ}
   where
    go :
      (⟨ e ⟩ᵀᵒ[< ι ] Pᵒ˙) ∗ᵒ ⟨¿ eˇ' ⟩ᵀᵒ⊤[< ι ] ∗ᵒ [∗ᵒ]⟨ es ⟩ᵀᵒ⊤[ ιs ] ∗ᵒ [⊤]ᴺᵒ ⊨
        ∃ᵒ ι₀' , ∃ᵒ ιs' , ⌜ ι₀' ∷ ιs' ≺ᴰᴹ⟨ _<ˢ_ ⟩ sz ι ∷ ιs ⌝ᵒ×
          (⟨ e ⟩ᵀᵒ[ sz⁻¹ ι₀' ] Pᵒ˙) ∗ᵒ [∗ᵒ]⟨ ¿⇒ᴸ eˇ' ⧺ es ⟩ᵀᵒ⊤[ ιs' ] ∗ᵒ [⊤]ᴺᵒ
    go {eˇ' = ň} =  Shrunkᵒ∗ᵒ-out › λ{ (§ big) → -, -,
      ≺ᴰᴹ-hd $ aug-∷ size< aug-refl , big ▷ ∗ᵒ-monoʳ (∗ᵒ-elimʳ ∗ᵒ-Mono) }
    go {eˇ' = š _} =  Shrunkᵒ∗ᵒ-out › λ{ (§ big) → big ▷ ?∗ᵒ-comm ▷
      Shrunkᵒ∗ᵒ-out ▷ λ{ (§ big) → -, -,
      ≺ᴰᴹ-hd $ aug-∷ size< $ aug-∷ size< aug-refl ,
      big ▷ ?∗ᵒ-comm ▷ ∗ᵒ-monoʳ ∗ᵒ-assocʳ }}
  ⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ {ιs = []} (redᵀ-tl _) =  ?∗ᵒ-comm › ∗ᵒ⇒∗ᵒ' › λ ()
  ⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ {ιs = _ ∷ _} (redᵀ-tl esM⇒) =
    ∗ᵒ-monoʳ (∗ᵒ-assocˡ › ∗ᵒ-monoˡ ⁺⟨⟩ᵀᵒ⊤⇒⁺⟨⟩ᵀᵒ › ⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ esM⇒) ›
    ⇛ᴹ-eatˡ › ⇛ᴹ-mono $ ∗ᵒ⇒∗ᵒ' › λ (-, -, ∙⊑ , ⟨e⟩P , -, -, ι'∷ιs'≺ , big) →
    -, -, ≺ᴰᴹ-tl ι'∷ιs'≺ ,
    ∗ᵒ'⇒∗ᵒ (-, -, ∙⊑ , ⟨e⟩P , big ▷ ∗ᵒ-monoˡ ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᵀᵒ⊤ ▷ ∗ᵒ-assocʳ)

  -- ⊨ ⟨ e ⟩ᵀᵒ[ ι ] Pᵒ˙ ensures that (e , [] , M) is accessible with respect to
  -- ⇐ᵀ, i.e., any reduction sequence starting with (e , M) eventually
  -- terminates, for valid M
  -- We don't assume fair thread scheduling for termination

  ⟨⟩ᵀᵒ⇒acc :  ⊨ ⟨ e ⟩ᵀᵒ[ ι ] Pᵒ˙ →  ✓ᴹ M →  Acc _⇐ᵀ_ (e , [] , M)
  ⟨⟩ᵀᵒ⇒acc ⊨⟨e⟩P ✓M =  go {ιs = []} (≺ᴰᴹ-wf <ˢ-wf) (empᴵⁿᴳ-✓ ✓M) $
    ◎-just ▷ ?∗ᵒ-intro _ ▷ ?∗ᵒ-intro ⊨⟨e⟩P ▷ ∗ᵒ?-intro Invᴳ-emp
   where
    -- Well-founded induction by the metric sz ι ∷ ιs
    go :  Acc (Rᴰᴹ _<ˢ_) (sz ι ∷ ιs) →  envᴳ M Eᴵⁿ ✓ᴳ a →
      (((⟨ e ⟩ᵀᵒ[ ι ] Pᵒ˙) ∗ᵒ [∗ᵒ]⟨ es ⟩ᵀᵒ⊤[ ιs ] ∗ᵒ [⊤]ᴺᵒ) ∗ᵒ Invᴳ Eᴵⁿ) a  →
      Acc _⇐ᵀ_ (e , es , M)
    go (acc ≺ι∷ιs⇒acc) ME✓a big =  acc λ eesM⇒ → big ▷
      ∗ᵒ-monoˡ (⟨⟩ᵀᵒ-[∗ᵒ]⟨⟩ᵀᵒ⊤-⇒ᵀ eesM⇒) ▷ ⇛ᴹ-step ME✓a ▷
      λ (-, -, M'E'✓b , big) → ∗ᵒ⇒∗ᵒ' big ▷
      λ (-, -, ∙⊑ , (-, -, ≺ι∷ιs , big) , InvE') →
      go (≺ι∷ιs⇒acc ≺ι∷ιs) M'E'✓b $ ∗ᵒ'⇒∗ᵒ (-, -, ∙⊑ , big , InvE')
