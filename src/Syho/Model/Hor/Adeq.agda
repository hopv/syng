--------------------------------------------------------------------------------
-- Adequacy of the semantic partial and total weakest preconditions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Hor.Adeq where

open import Base.Level using (Level)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Few using (¬_)
open import Base.Eq using (_≡_)
open import Base.Acc using (Acc; acc)
open import Base.Size using (Size; ∞; !; §_)
open import Base.Prod using (_×_; π₀; π₁; _,_; -,_)
open import Base.Sum using (ĩ₁_)
open import Syho.Lang.Expr using (Type; Expr; Val; V⇒E)
open import Syho.Lang.Ktxred using (Ktxred; val/ktxred; val/ktxred-V⇒E)
open import Syho.Lang.Reduce using (Mem; ✓ᴹ_; _⇒ᴷᴿ∑; redᴱ; _⇒ᴱ*_; ⇒ᴱ*-refl;
  ⇒ᴱ*-step; _⇐ᴱ_)
open import Syho.Model.ERA.Glob using (Resᴳ; _✓ᴳ_; Envᴵⁿᴳ; envᴳ; empᴵⁿᴳ-✓)
open import Syho.Model.Prop.Base using (Propᵒ; _⊨_; ⊨_; ⌜_⌝ᵒ; _∗ᵒ_; ∗ᵒ-monoˡ;
  ∗ᵒ?-intro; Shrunkᵒ∗ᵒ-out)
open import Syho.Model.Supd.Interp using (⟨_⟩⇛ᵒ⟨_⟩_; Invᴳ; Invᴳ-emp; ⇛ᵒ-mono;
  ⇛ᵒ-intro; ⇛ᵒ-join; ⇛ᵒ-adeq; ⇛ᵒ-step)
open import Syho.Model.Hor.Wp using (⟨_⟩ᴾᵒ[_]_; ⟨_⟩ᵀᵒ[_]_; ⟨_⟩ᵀᵒ[<_]_;
  ⁺⟨⟩ᴾᵒ-val⁻¹; ⁺⟨⟩ᵀᵒ-val⁻¹; ⁺⟨⟩ᴾᵒ-kr⁻¹; ⁺⟨⟩ᵀᵒ-kr⁻¹)

private variable
  ł :  Level
  ι :  Size
  T :  Type
  M⁻ M M' :  Mem
  e e' :  Expr ∞ T
  v :  Val T
  kr' :  Ktxred T
  Pᵒ˙ :  Val T → Propᵒ ł
  X˙ :  Val T → Set ł
  Eᴵⁿ :  Envᴵⁿᴳ
  a :  Resᴳ

--------------------------------------------------------------------------------
-- Adequacy of the semantic partial and total weakest preconditions

abstract

  -- Useful lemma: If ⊨ ⟨ M⁻ ⟩⇛ᵒ⟨ M ⟩ ⟨ e ⟩ᴾᵒ[ ∞ ]/ᵀᵒ[< ι ] Pᵒ˙ holds,
  -- for every (e' , M') reachable from (e , M),
  -- we have ⊨ ⟨ M⁻ ⟩⇛ᵒ⟨ M' ⟩ ⟨ e' ⟩ᴾᵒ[ ∞ ]/ᵀᵒ[< ι ] Pᵒ˙

  ⇛ᵒ⟨⟩ᴾᵒ-⇒ᴱ* :  ⊨ ⟨ M⁻ ⟩⇛ᵒ⟨ M ⟩ ⟨ e ⟩ᴾᵒ[ ∞ ] Pᵒ˙ →  (e , M) ⇒ᴱ* (e' , M') →
                ⊨ ⟨ M⁻ ⟩⇛ᵒ⟨ M' ⟩ ⟨ e' ⟩ᴾᵒ[ ∞ ] Pᵒ˙
  ⇛ᵒ⟨⟩ᴾᵒ-⇒ᴱ* ⊨M⁻⇛M⟨e⟩P ⇒ᴱ*-refl =  ⊨M⁻⇛M⟨e⟩P
  ⇛ᵒ⟨⟩ᴾᵒ-⇒ᴱ* ⊨M⁻⇛M⟨e⟩P (⇒ᴱ*-step (redᴱ e≡kr krM⇒e⁺M⁺) e⁺M⁺⇒*e'M')
    rewrite e≡kr =  ⇛ᵒ⟨⟩ᴾᵒ-⇒ᴱ*
    (⊨M⁻⇛M⟨e⟩P ▷ ⇛ᵒ-mono (⁺⟨⟩ᴾᵒ-kr⁻¹ › (_$ _) ›
      ⇛ᵒ-mono (λ big → big .π₁ _ _ krM⇒e⁺M⁺) › ⇛ᵒ-join ›
      ⇛ᵒ-mono (λ big → big .!)) ▷ ⇛ᵒ-join) e⁺M⁺⇒*e'M'

  ⇛ᵒ⟨⟩ᵀᵒ-⇒ᴱ* :  ⊨ ⟨ M⁻ ⟩⇛ᵒ⟨ M ⟩ ⟨ e ⟩ᵀᵒ[< ι ] Pᵒ˙ →  (e , M) ⇒ᴱ* (e' , M') →
                ⊨ ⟨ M⁻ ⟩⇛ᵒ⟨ M' ⟩ ⟨ e' ⟩ᵀᵒ[< ι ] Pᵒ˙
  ⇛ᵒ⟨⟩ᵀᵒ-⇒ᴱ* ⊨M⁻⇛M⟨e⟩P ⇒ᴱ*-refl =  ⊨M⁻⇛M⟨e⟩P
  ⇛ᵒ⟨⟩ᵀᵒ-⇒ᴱ* ⊨M⁻⇛M⟨e⟩P (⇒ᴱ*-step (redᴱ e≡kr krM⇒e⁺M⁺) e⁺M⁺⇒*e'M')
    rewrite e≡kr =  ⇛ᵒ⟨⟩ᵀᵒ-⇒ᴱ*
    (⊨M⁻⇛M⟨e⟩P ▷ ⇛ᵒ-mono (λ{ (§ big) → big ▷ ⁺⟨⟩ᵀᵒ-kr⁻¹ ▷ (_$ _) ▷
      ⇛ᵒ-mono (λ big → big .π₁ _ _ krM⇒e⁺M⁺) ▷ ⇛ᵒ-join ▷
      ⇛ᵒ-mono λ{ (§ big) → § big }}) ▷ ⇛ᵒ-join) e⁺M⁺⇒*e'M'

  -- ⊨ ⟨ e ⟩ᴾᵒ[ ∞ ]/ᵀᵒ[ ι ] Pᵒ˙ ensures that any reduction iteration starting
  -- with (e , M) never gets stuck for valid M

  ⟨⟩ᴾᵒ-nostuck :  ✓ᴹ M →  ⊨ ⟨ e ⟩ᴾᵒ[ ∞ ] Pᵒ˙ →  (e , M) ⇒ᴱ* (e' , M') →
                  val/ktxred e' ≡ ĩ₁ kr' →  (kr' , M') ⇒ᴷᴿ∑
  ⟨⟩ᴾᵒ-nostuck ✓M ⊨⟨e⟩P eM⇒*e'M' e'≡kr'
    with ⇛ᵒ⟨⟩ᴾᵒ-⇒ᴱ* (⇛ᵒ-intro ⊨⟨e⟩P) eM⇒*e'M'
  … | ⊨M⁻⇛M'⟨e'⟩P  rewrite e'≡kr' =  ⇛ᵒ-adeq ✓M
    (⊨M⁻⇛M'⟨e'⟩P ▷ ⇛ᵒ-mono (⁺⟨⟩ᴾᵒ-kr⁻¹ › (_$ _) › ⇛ᵒ-mono π₀) ▷ ⇛ᵒ-join)

  ⟨⟩ᵀᵒ-nostuck :  ✓ᴹ M →  ⊨ ⟨ e ⟩ᵀᵒ[ ι ] Pᵒ˙ →  (e , M) ⇒ᴱ* (e' , M') →
                  val/ktxred e' ≡ ĩ₁ kr' →  (kr' , M') ⇒ᴷᴿ∑
  ⟨⟩ᵀᵒ-nostuck ✓M ⊨⟨e⟩P eM⇒*e'M' e'≡kr'
    with ⇛ᵒ⟨⟩ᵀᵒ-⇒ᴱ* (⇛ᵒ-intro $ § ⊨⟨e⟩P) eM⇒*e'M'
  … | ⊨M⁻⇛M'⟨e'⟩P  rewrite e'≡kr' =  ⇛ᵒ-adeq ✓M (⊨M⁻⇛M'⟨e'⟩P ▷
      ⇛ᵒ-mono (λ{ (§ big) → big ▷ ⁺⟨⟩ᵀᵒ-kr⁻¹ ▷ (_$ _) ▷ ⇛ᵒ-mono π₀}) ▷ ⇛ᵒ-join)

  -- ⊨ ⟨ e ⟩ᴾᵒ[ ∞ ]/ᵀᵒ[ ι ] λ u → ⌜ X˙ u ⌝ᵒ ensures that the X˙ v holds for the
  -- result value v of any reduction starting with (e , M) for valid M

  ⟨⟩ᴾᵒ-post :  ✓ᴹ M →  ⊨ ⟨ e ⟩ᴾᵒ[ ∞ ] (λ u → ⌜ X˙ u ⌝ᵒ) →
               (e , M) ⇒ᴱ* (V⇒E v , M') →  X˙ v
  ⟨⟩ᴾᵒ-post {v = v} ✓M ⊨⟨e⟩P eM⇒*e'M'  with ⇛ᵒ⟨⟩ᴾᵒ-⇒ᴱ* (⇛ᵒ-intro ⊨⟨e⟩P) eM⇒*e'M'
  … | ⊨M⁻⇛M'⟨e'⟩P  rewrite val/ktxred-V⇒E {v = v} =  ⇛ᵒ-adeq ✓M
    (⊨M⁻⇛M'⟨e'⟩P ▷ ⇛ᵒ-mono (⁺⟨⟩ᴾᵒ-val⁻¹ › (_$ _)) ▷ ⇛ᵒ-join)

  ⟨⟩ᵀᵒ-post :  ✓ᴹ M →  ⊨ ⟨ e ⟩ᵀᵒ[ ι ] (λ u → ⌜ X˙ u ⌝ᵒ) →
               (e , M) ⇒ᴱ* (V⇒E v , M') →  X˙ v
  ⟨⟩ᵀᵒ-post {v = v} ✓M ⊨⟨e⟩P eM⇒*e'M'
    with ⇛ᵒ⟨⟩ᵀᵒ-⇒ᴱ* (⇛ᵒ-intro $ § ⊨⟨e⟩P) eM⇒*e'M'
  … | ⊨M⁻⇛M'⟨e'⟩P  rewrite val/ktxred-V⇒E {v = v} =  ⇛ᵒ-adeq ✓M (⊨M⁻⇛M'⟨e'⟩P ▷
    ⇛ᵒ-mono (λ{ (§ big) → big ▷ ⁺⟨⟩ᵀᵒ-val⁻¹ ▷ (_$ _) }) ▷ ⇛ᵒ-join)

  -- ⊨ ⟨ e ⟩ᵀᵒ[ ι ] Pᵒ˙ ensures that (e , M) is accessible with respect to ⇐ᴱ,
  -- i.e., every reduction sequence from (e , M) terminates, for valid M

  ⟨⟩ᵀᵒ⇒acc :  ✓ᴹ M →  ⊨ ⟨ e ⟩ᵀᵒ[ ι ] Pᵒ˙ →  Acc _⇐ᴱ_ (e , M)
  ⟨⟩ᵀᵒ⇒acc ✓M ⊨⟨e⟩P =  go (empᴵⁿᴳ-✓ ✓M) (⊨⟨e⟩P ▷ ∗ᵒ?-intro Invᴳ-emp)
   where
    go :  envᴳ M Eᴵⁿ ✓ᴳ a →  ((⟨ e ⟩ᵀᵒ[ ι ] Pᵒ˙) ∗ᵒ Invᴳ Eᴵⁿ) a  →
          Acc _⇐ᴱ_ (e , M)
    go {M} {e = e} ME✓a ⟨e⟩P∗InvEa =  acc fo
     where
      fo :  (e' , M') ⇐ᴱ (e , M) →  Acc _⇐ᴱ_ (e' , M')
      fo (redᴱ e≡kr krM⇒e'M')  rewrite e≡kr
        with ⇛ᵒ-step (ME✓a , ⟨e⟩P∗InvEa ▷ ∗ᵒ-monoˡ (⁺⟨⟩ᵀᵒ-kr⁻¹ ›
          (_$ _) › ⇛ᵒ-mono (λ big → big .π₁ _ _ krM⇒e'M') › ⇛ᵒ-join))
      … | -, -, M'E'✓b , ⟨e'⟩<P∗InvE'b  with Shrunkᵒ∗ᵒ-out ⟨e'⟩<P∗InvE'b
      …   | § ⟨e'⟩P∗InvE'b =  go M'E'✓b ⟨e'⟩P∗InvE'b
