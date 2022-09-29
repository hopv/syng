--------------------------------------------------------------------------------
-- Interpret the indirection modality and the precursors
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Ind where

open import Base.Level using (1ᴸ)
open import Base.Func using (_$_; _›_)
open import Base.Few using (absurd)
open import Base.Size using (∞)
open import Base.Prod using (_,_; -,_; -ᴵ,_)
open import Base.Zoi using (⊤ᶻ)
open import Base.Nat using (ℕ; ṡ_)
open import Syho.Lang.Expr using (Type; Expr∞; Val)
open import Syho.Lang.Ktxred using (Redex)
open import Syho.Logic.Prop using (Prop∞; ⊤'; _∗_; [_]ᴺ; Basic)
open import Syho.Logic.Core using (_⊢[_]_; _»_; ∗-assocˡ; ∗-assocʳ; ∗-monoˡ;
  ∗-monoʳ; ?∗-comm; ∗?-comm; ∗-elimʳ)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_; ⇛-ṡ; _ᵘ»_; _ᵘ»ᵘ_; ⇛-frameˡ;
  ⇛-frameʳ)
open import Syho.Logic.Hor using (_⊢[_][_]ᵃ⟨_⟩_; _⊢[_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ[_]_;
  hor-ᵀ⇒ᴾ; ahor-ṡ; horᵀ-ṡ; _ᵃʰ»ᵘ_; _ʰ»ᵘ_; _ᵘ»ᵃʰ_; _ᵘ»ʰ_; ahor-frameˡ;
  hor-frameˡ)
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Ind using (indˣ; indᵖ)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ; iᴵⁿᵈˣ; iᴵⁿᵈᵖ)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨_; ∃ᵒ-syntax; ∃ᴵ-syntax;
  ⌜_⌝ᵒ×_; _⨿ᵒ_; _∗ᵒ_; ◎⟨_⟩_; ∃ᵒ-Mono; ∃ᴵ-Mono; ⨿ᵒ-Mono; ∗ᵒ⇒∗ᵒ'; ∗ᵒ'⇒∗ᵒ; ∗ᵒ-Mono;
  ∗ᵒ-assocʳ; ?∗ᵒ-intro; ◎-Mono)
open import Syho.Model.Prop.Basic using (⸨_⸩ᴮ)

private variable
  i j :  ℕ
  X :  Set₀
  T :  Type
  P P' Q Q' R :  Prop∞
  Q˙ Q'˙ :  X →  Prop∞
  red :  Redex T
  e :  Expr∞ T

--------------------------------------------------------------------------------
-- Ind :  Indirection base

Indˣ Indᵖ Ind :  Prop∞ →  Propᵒ 1ᴸ
Indˣ P =  ∃ᵒ i , ◎⟨ iᴵⁿᵈˣ ⟩ indˣ i P
Indᵖ P =  ∃ᵒ i , ◎⟨ iᴵⁿᵈᵖ ⟩ indᵖ i P
Ind P =  Indˣ P ⨿ᵒ Indᵖ P

abstract

  Indˣ-Mono :  Monoᵒ $ Indˣ P
  Indˣ-Mono =  ∃ᵒ-Mono λ _ → ◎-Mono

  Indᵖ-Mono :  Monoᵒ $ Indᵖ P
  Indᵖ-Mono =  ∃ᵒ-Mono λ _ → ◎-Mono

  Ind-Mono :  Monoᵒ $ Ind P
  Ind-Mono =  ⨿ᵒ-Mono Indˣ-Mono Indᵖ-Mono

--------------------------------------------------------------------------------
-- ○ᵒ :  Interpret the indirection modality ○

infix 8 ○ᵒ_
○ᵒ_ :  Prop∞ →  Propᵒ 1ᴸ
○ᵒ P =  ∃ᵒ Q , ∃ᴵ BasicQ , ∃ᵒ R ,
  ⌜ Q ∗ R ⊢[ ∞ ] P ⌝ᵒ×  ⸨ Q ⸩ᴮ {{BasicQ}}  ∗ᵒ  Ind R

abstract

  -- Monoᵒ for ○ᵒ

  ○ᵒ-Mono :  Monoᵒ $ ○ᵒ P
  ○ᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- Monotonicity of ○ᵒ

  ○ᵒ-mono :  P ⊢[ ∞ ] Q →  ○ᵒ P ⊨ ○ᵒ Q
  ○ᵒ-mono P⊢Q (-, -ᴵ, -, R∗S⊢P , R∗IndSa) =  -, -ᴵ, -, R∗S⊢P » P⊢Q , R∗IndSa

  -- Let ○ᵒ eat a proposition under ∗ᵒ

  ○ᵒ-eatˡ :  {{_ : Basic Q}} →  ⸨ Q ⸩ᴮ ∗ᵒ ○ᵒ P ⊨ ○ᵒ (Q ∗ P)
  ○ᵒ-eatˡ =  ∗ᵒ⇒∗ᵒ' › λ{ (-, -, b∙c⊑a , Qb , -, -ᴵ, -, R∗S⊢P , R∗IndSc) →
    -, -ᴵ, -, ∗-assocˡ » ∗-monoʳ R∗S⊢P ,
    ∗ᵒ-assocʳ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Qb , R∗IndSc) }

  -- Make ○ᵒ out of Ind

  Ind⇒○ᵒ :  Ind P ⊨ ○ᵒ P
  Ind⇒○ᵒ IndPa =  ⊤' , -ᴵ, -, ∗-elimʳ , ?∗ᵒ-intro absurd IndPa

--------------------------------------------------------------------------------
-- ↪⇛ᵒ :  Interpret the super-update precursor ↪⇛

infixr 5 _↪[_]⇛ᵒ_
_↪[_]⇛ᵒ_ :  Prop∞ →  ℕ →  Prop∞ →  Propᵒ 1ᴸ
P ↪[ i ]⇛ᵒ Q =  ∃ᵒ R , ∃ᴵ BasicR , ∃ᵒ S ,
  ⌜ P ∗ R ∗ S ⊢[ ∞ ][ i ]⇛ Q ⌝ᵒ×  ⸨ R ⸩ᴮ {{BasicR}}  ∗ᵒ  Ind S

abstract

  -- Monoᵒ for ↪⇛ᵒ

  ↪⇛ᵒ-Mono :  Monoᵒ $ P ↪[ i ]⇛ᵒ Q
  ↪⇛ᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- Modify ⇛ proof

  ↪⇛ᵒ-ṡ :  P ↪[ i ]⇛ᵒ Q  ⊨  P ↪[ ṡ i ]⇛ᵒ Q
  ↪⇛ᵒ-ṡ (-, -ᴵ, -, P∗R∗S⊢⇛Q , R∗IndSa) =  -, -ᴵ, -, ⇛-ṡ P∗R∗S⊢⇛Q , R∗IndSa

  ↪⇛ᵒ-eatˡ⁻ˡᵘ :  {{_ : Basic R}} →
    R ∗ P' ⊢[ ∞ ][ i ]⇛ P →  ⸨ R ⸩ᴮ ∗ᵒ (P ↪[ i ]⇛ᵒ Q)  ⊨  P' ↪[ i ]⇛ᵒ Q
  ↪⇛ᵒ-eatˡ⁻ˡᵘ R∗P'⊢⇛P =  ∗ᵒ⇒∗ᵒ' › λ{
    (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⇛Q , S∗IndTc) →  -, -ᴵ, -,
    -- P'∗(R∗S)∗T ⊢ P'∗R∗S∗T ⊢ R∗P'∗S∗T ⊢ (R∗P')∗S∗T ⊢⇛ P∗S∗T ⊢⇛ Q
    ∗-monoʳ ∗-assocˡ » ?∗-comm » ∗-assocʳ » ⇛-frameʳ R∗P'⊢⇛P ᵘ»ᵘ P∗S∗T⊢⇛Q ,
    ∗ᵒ-assocʳ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Rb , S∗IndTc) }

  ↪⇛ᵒ-eatˡ⁻ʳ :  {{_ : Basic R}} →
    ⸨ R ⸩ᴮ ∗ᵒ (P ↪[ i ]⇛ᵒ Q)  ⊨  P ↪[ i ]⇛ᵒ R ∗ Q
  ↪⇛ᵒ-eatˡ⁻ʳ =  ∗ᵒ⇒∗ᵒ' › λ{ (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⇛Q , S∗IndTc) →
    -, -ᴵ, -,
    -- P∗(R∗S)∗T ⊢ P∗R∗S∗T ⊢⇛ R∗P∗S∗T ⊢⇛ R∗Q
    ∗-monoʳ ∗-assocˡ » ?∗-comm » ⇛-frameˡ P∗S∗T⊢⇛Q ,
    ∗ᵒ-assocʳ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Rb , S∗IndTc) }

  ↪⇛ᵒ-monoʳᵘ :  Q ⊢[ ∞ ][ i ]⇛ Q' →  P ↪[ i ]⇛ᵒ Q  ⊨  P ↪[ i ]⇛ᵒ Q'
  ↪⇛ᵒ-monoʳᵘ Q⊢⇛Q' (-, -ᴵ, -, P∗R∗S⊢⇛Q , R∗IndSa) =
    -, -ᴵ, -, P∗R∗S⊢⇛Q ᵘ»ᵘ Q⊢⇛Q' , R∗IndSa

  ↪⇛ᵒ-frameˡ :  P ↪[ i ]⇛ᵒ Q  ⊨  R ∗ P ↪[ i ]⇛ᵒ R ∗ Q
  ↪⇛ᵒ-frameˡ (-, -ᴵ, -, P∗R∗S⊢⇛Q , R∗IndSa) =
    -, -ᴵ, -, ∗-assocˡ » ⇛-frameˡ P∗R∗S⊢⇛Q , R∗IndSa

  -- Make ↪⇛ᵒ out of ○ᵒ

  ○ᵒ⇒↪⇛ᵒ :  P ∗ R ⊢[ ∞ ][ i ]⇛ Q →  ○ᵒ R  ⊨  P ↪[ i ]⇛ᵒ Q
  ○ᵒ⇒↪⇛ᵒ P∗R⊢⇛Q (-, -ᴵ, -, S∗T⊢R , S∗IndTa) =
    -, -ᴵ, -, ∗-monoʳ S∗T⊢R » P∗R⊢⇛Q , S∗IndTa

--------------------------------------------------------------------------------
-- ↪ᵃ⟨ ⟩ᵒ :  Interpret the partial Hoare-triple precursor ↪ᵃ⟨ ⟩

infixr 5 _↪[_]ᵃ⟨_⟩ᵒ_
_↪[_]ᵃ⟨_⟩ᵒ_ :  Prop∞ →  ℕ →  Redex T →  (Val T → Prop∞) →  Propᵒ 1ᴸ
P ↪[ i ]ᵃ⟨ red ⟩ᵒ Q˙ =  ∃ᵒ R , ∃ᴵ BasicR , ∃ᵒ S ,
  ⌜ P ∗ R ∗ S ⊢[ ∞ ][ i ]ᵃ⟨ red ⟩ Q˙ ⌝ᵒ×  ⸨ R ⸩ᴮ {{BasicR}}  ∗ᵒ  Ind S

abstract

  -- Monoᵒ for ↪ᵃ⟨ ⟩ᵒ

  ↪ᵃ⟨⟩ᵒ-Mono :  Monoᵒ $ P ↪[ i ]ᵃ⟨ red ⟩ᵒ Q˙
  ↪ᵃ⟨⟩ᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- Modify ᵃ⟨ ⟩ proof

  ↪ᵃ⟨⟩ᵒ-ṡ :  P ↪[ i ]ᵃ⟨ red ⟩ᵒ Q˙  ⊨  P ↪[ ṡ i ]ᵃ⟨ red ⟩ᵒ Q˙
  ↪ᵃ⟨⟩ᵒ-ṡ (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, ahor-ṡ P∗R∗S⊢⟨e⟩Q , R∗IndSa

  ↪ᵃ⟨⟩ᵒ-eatˡ⁻ˡᵘ :  {{_ : Basic R}} →  R ∗ P' ⊢[ ∞ ][ j ]⇛ P →
                   ⸨ R ⸩ᴮ ∗ᵒ (P ↪[ i ]ᵃ⟨ red ⟩ᵒ Q˙)  ⊨  P' ↪[ i ]ᵃ⟨ red ⟩ᵒ Q˙
  ↪ᵃ⟨⟩ᵒ-eatˡ⁻ˡᵘ R∗P'⊢⇛P =  ∗ᵒ⇒∗ᵒ' › λ{
    (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⟨e⟩Q , S∗IndTc) →  -, -ᴵ, -,
    -- P'∗(R∗S)∗T ⊢ P'∗R∗S∗T ⊢ R∗P'∗S∗T ⊢ (R∗P')∗S∗T ⊢⇛ P∗S∗T ⊢⟨e⟩ᵀ Q˙
    ∗-monoʳ ∗-assocˡ » ?∗-comm » ∗-assocʳ » ⇛-frameʳ R∗P'⊢⇛P ᵘ»ᵃʰ P∗S∗T⊢⟨e⟩Q ,
    ∗ᵒ-assocʳ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Rb , S∗IndTc) }

  ↪ᵃ⟨⟩ᵒ-eatˡ⁻ʳ :  {{_ : Basic R}} →
    ⸨ R ⸩ᴮ ∗ᵒ (P ↪[ i ]ᵃ⟨ red ⟩ᵒ Q˙)  ⊨  P ↪[ i ]ᵃ⟨ red ⟩ᵒ λ v → R ∗ Q˙ v
  ↪ᵃ⟨⟩ᵒ-eatˡ⁻ʳ =  ∗ᵒ⇒∗ᵒ' › λ{
    (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⟨e⟩Q , S∗IndTc) →  -, -ᴵ, -,
    -- P∗(R∗S)∗T ⊢ P∗R∗S∗T ⊢ R∗P∗S∗T ⊢⟨e⟩ᵀ R∗Q
    ∗-monoʳ ∗-assocˡ » ?∗-comm » ahor-frameˡ P∗S∗T⊢⟨e⟩Q ,
    ∗ᵒ-assocʳ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Rb , S∗IndTc) }

  ↪ᵃ⟨⟩ᵒ-monoʳᵘ :  (∀ v →  Q˙ v ⊢[ ∞ ][ j ]⇛ Q'˙ v) →
                  P ↪[ i ]ᵃ⟨ red ⟩ᵒ Q˙  ⊨  P ↪[ i ]ᵃ⟨ red ⟩ᵒ Q'˙
  ↪ᵃ⟨⟩ᵒ-monoʳᵘ ∀vQ⊢⇛Q' (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, P∗R∗S⊢⟨e⟩Q ᵃʰ»ᵘ ∀vQ⊢⇛Q' , R∗IndSa

  ↪ᵃ⟨⟩ᵒ-frameˡ :  P ↪[ i ]ᵃ⟨ red ⟩ᵒ Q˙  ⊨  R ∗ P ↪[ i ]ᵃ⟨ red ⟩ᵒ λ v → R ∗ Q˙ v
  ↪ᵃ⟨⟩ᵒ-frameˡ (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, ∗-assocˡ » ahor-frameˡ P∗R∗S⊢⟨e⟩Q , R∗IndSa

  -- Make ↪⟨ ⟩ᵀᵒ out of ○ᵒ

  ○ᵒ⇒↪ᵃ⟨⟩ᵒ :  P ∗ R ⊢[ ∞ ][ i ]ᵃ⟨ red ⟩ Q˙ →  ○ᵒ R  ⊨  P ↪[ i ]ᵃ⟨ red ⟩ᵒ Q˙
  ○ᵒ⇒↪ᵃ⟨⟩ᵒ P∗R⊢⟨e⟩Q (-, -ᴵ, -, S∗T⊢R , S∗IndTa) =
    -, -ᴵ, -, ∗-monoʳ S∗T⊢R » P∗R⊢⟨e⟩Q , S∗IndTa

--------------------------------------------------------------------------------
-- ↪⟨ ⟩ᴾᵒ :  Interpret the partial Hoare-triple precursor ↪⟨ ⟩ᴾ

infixr 5 _↪⟨_⟩ᴾᵒ_
_↪⟨_⟩ᴾᵒ_ :  Prop∞ →  Expr∞ T →  (Val T → Prop∞) →  Propᵒ 1ᴸ
P ↪⟨ e ⟩ᴾᵒ Q˙ =  ∃ᵒ R , ∃ᴵ BasicR , ∃ᵒ S ,
  ⌜ P ∗ R ∗ S ⊢[ ∞ ]⟨ e ⟩ᴾ Q˙ ⌝ᵒ×  ⸨ R ⸩ᴮ {{BasicR}}  ∗ᵒ  Ind S

abstract

  -- Monoᵒ for ↪⟨ ⟩ᴾᵒ

  ↪⟨⟩ᴾᵒ-Mono :  Monoᵒ $ P ↪⟨ e ⟩ᴾᵒ Q˙
  ↪⟨⟩ᴾᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- Modify ⟨ ⟩ᴾ proof

  ↪⟨⟩ᴾᵒ-eatˡ⁻ˡᵘ :  {{_ : Basic R}} →
                   (R ∗ P') ∗ [ ⊤ᶻ ]ᴺ ⊢[ ∞ ][ i ]⇛ P ∗ [ ⊤ᶻ ]ᴺ →
                   ⸨ R ⸩ᴮ ∗ᵒ (P ↪⟨ e ⟩ᴾᵒ Q˙)  ⊨  P' ↪⟨ e ⟩ᴾᵒ Q˙
  ↪⟨⟩ᴾᵒ-eatˡ⁻ˡᵘ R∗P'⊢⇛[⊤]P =  ∗ᵒ⇒∗ᵒ' › λ{
    (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⟨e⟩Q , S∗IndTc) →  -, -ᴵ, -,
    -- P'∗(R∗S)∗T ⊢ P'∗R∗S∗T ⊢ R∗P'∗S∗T ⊢ (R∗P')∗S∗T ⊢⇛[⊤] P∗S∗T ⊢⟨e⟩ᴾ Q˙
    ∗-monoʳ ∗-assocˡ » ?∗-comm » ∗-assocʳ »
      (∗?-comm » ⇛-frameʳ R∗P'⊢⇛[⊤]P ᵘ» ∗?-comm) ᵘ»ʰ P∗S∗T⊢⟨e⟩Q ,
    ∗ᵒ-assocʳ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Rb , S∗IndTc) }

  ↪⟨⟩ᴾᵒ-eatˡ⁻ʳ :  {{_ : Basic R}} →
    ⸨ R ⸩ᴮ ∗ᵒ (P ↪⟨ e ⟩ᴾᵒ Q˙)  ⊨  P ↪⟨ e ⟩ᴾᵒ λ v → R ∗ Q˙ v
  ↪⟨⟩ᴾᵒ-eatˡ⁻ʳ =  ∗ᵒ⇒∗ᵒ' › λ{
    (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⟨e⟩Q , S∗IndTc) →  -, -ᴵ, -,
    -- P∗(R∗S)∗T ⊢ P∗R∗S∗T ⊢ R∗P∗S∗T ⊢⟨e⟩ᴾ R∗Q
    ∗-monoʳ ∗-assocˡ » ?∗-comm » hor-frameˡ P∗S∗T⊢⟨e⟩Q ,
    ∗ᵒ-assocʳ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Rb , S∗IndTc) }

  ↪⟨⟩ᴾᵒ-monoʳᵘ :  (∀ v →  Q˙ v ∗ [ ⊤ᶻ ]ᴺ ⊢[ ∞ ][ i ]⇛ Q'˙ v ∗ [ ⊤ᶻ ]ᴺ) →
                  P ↪⟨ e ⟩ᴾᵒ Q˙  ⊨  P ↪⟨ e ⟩ᴾᵒ Q'˙
  ↪⟨⟩ᴾᵒ-monoʳᵘ ∀vQ⊢⇛Q' (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, P∗R∗S⊢⟨e⟩Q ʰ»ᵘ ∀vQ⊢⇛Q' , R∗IndSa

  ↪⟨⟩ᴾᵒ-frameˡ :  P ↪⟨ e ⟩ᴾᵒ Q˙  ⊨  R ∗ P ↪⟨ e ⟩ᴾᵒ λ v → R ∗ Q˙ v
  ↪⟨⟩ᴾᵒ-frameˡ (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, ∗-assocˡ » hor-frameˡ P∗R∗S⊢⟨e⟩Q , R∗IndSa

  -- Make ↪⟨ ⟩ᴾᵒ out of ○ᵒ

  ○ᵒ⇒↪⟨⟩ᴾᵒ :  P ∗ R ⊢[ ∞ ]⟨ e ⟩ᴾ Q˙ →  ○ᵒ R  ⊨  P ↪⟨ e ⟩ᴾᵒ Q˙
  ○ᵒ⇒↪⟨⟩ᴾᵒ P∗R⊢⟨e⟩Q (-, -ᴵ, -, S∗T⊢R , S∗IndTa) =
    -, -ᴵ, -, ∗-monoʳ S∗T⊢R » P∗R⊢⟨e⟩Q , S∗IndTa

--------------------------------------------------------------------------------
-- ↪⟨ ⟩ᵀᵒ :  Interpret the partial Hoare-triple precursor ↪⟨ ⟩ᵀ

infixr 5 _↪⟨_⟩ᵀ[_]ᵒ_
_↪⟨_⟩ᵀ[_]ᵒ_ :  Prop∞ →  Expr∞ T →  ℕ →  (Val T → Prop∞) →  Propᵒ 1ᴸ
P ↪⟨ e ⟩ᵀ[ i ]ᵒ Q˙ =  ∃ᵒ R , ∃ᴵ BasicR , ∃ᵒ S ,
  ⌜ P ∗ R ∗ S ⊢[ ∞ ]⟨ e ⟩ᵀ[ i ] Q˙ ⌝ᵒ×  ⸨ R ⸩ᴮ {{BasicR}}  ∗ᵒ  Ind S

abstract

  -- Monoᵒ for ↪⟨ ⟩ᵀᵒ

  ↪⟨⟩ᵀᵒ-Mono :  Monoᵒ $ P ↪⟨ e ⟩ᵀ[ i ]ᵒ Q˙
  ↪⟨⟩ᵀᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- Modify ⟨ ⟩ᵀ proof

  ↪⟨⟩ᵀᵒ-ṡ :  P ↪⟨ e ⟩ᵀ[ i ]ᵒ Q˙  ⊨  P ↪⟨ e ⟩ᵀ[ ṡ i ]ᵒ Q˙
  ↪⟨⟩ᵀᵒ-ṡ (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, horᵀ-ṡ P∗R∗S⊢⟨e⟩Q , R∗IndSa

  ↪⟨⟩ᵀᵒ-eatˡ⁻ˡᵘ :  {{_ : Basic R}} →
                   (R ∗ P') ∗ [ ⊤ᶻ ]ᴺ ⊢[ ∞ ][ j ]⇛ P ∗ [ ⊤ᶻ ]ᴺ →
                   ⸨ R ⸩ᴮ ∗ᵒ (P ↪⟨ e ⟩ᵀ[ i ]ᵒ Q˙)  ⊨  P' ↪⟨ e ⟩ᵀ[ i ]ᵒ Q˙
  ↪⟨⟩ᵀᵒ-eatˡ⁻ˡᵘ R∗P'⊢⇛[⊤]P =  ∗ᵒ⇒∗ᵒ' › λ{
    (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⟨e⟩Q , S∗IndTc) →  -, -ᴵ, -,
    -- P'∗(R∗S)∗T ⊢ P'∗R∗S∗T ⊢ R∗P'∗S∗T ⊢ (R∗P')∗S∗T ⊢⇛[⊤] P∗S∗T ⊢⟨e⟩ᵀ Q˙
    ∗-monoʳ ∗-assocˡ » ?∗-comm » ∗-assocʳ »
      (∗?-comm » ⇛-frameʳ R∗P'⊢⇛[⊤]P ᵘ» ∗?-comm) ᵘ»ʰ P∗S∗T⊢⟨e⟩Q ,
    ∗ᵒ-assocʳ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Rb , S∗IndTc) }

  ↪⟨⟩ᵀᵒ-eatˡ⁻ʳ :  {{_ : Basic R}} →
    ⸨ R ⸩ᴮ ∗ᵒ (P ↪⟨ e ⟩ᵀ[ i ]ᵒ Q˙)  ⊨  P ↪⟨ e ⟩ᵀ[ i ]ᵒ λ v → R ∗ Q˙ v
  ↪⟨⟩ᵀᵒ-eatˡ⁻ʳ =  ∗ᵒ⇒∗ᵒ' › λ{
    (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⟨e⟩Q , S∗IndTc) →  -, -ᴵ, -,
    -- P∗(R∗S)∗T ⊢ P∗R∗S∗T ⊢ R∗P∗S∗T ⊢⟨e⟩ᵀ R∗Q
    ∗-monoʳ ∗-assocˡ » ?∗-comm » hor-frameˡ P∗S∗T⊢⟨e⟩Q ,
    ∗ᵒ-assocʳ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Rb , S∗IndTc) }

  ↪⟨⟩ᵀᵒ-monoʳᵘ :  (∀ v →  Q˙ v ∗ [ ⊤ᶻ ]ᴺ ⊢[ ∞ ][ j ]⇛ Q'˙ v ∗ [ ⊤ᶻ ]ᴺ) →
                  P ↪⟨ e ⟩ᵀ[ i ]ᵒ Q˙  ⊨  P ↪⟨ e ⟩ᵀ[ i ]ᵒ Q'˙
  ↪⟨⟩ᵀᵒ-monoʳᵘ ∀vQ⊢⇛Q' (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, P∗R∗S⊢⟨e⟩Q ʰ»ᵘ ∀vQ⊢⇛Q' , R∗IndSa

  ↪⟨⟩ᵀᵒ-frameˡ :  P ↪⟨ e ⟩ᵀ[ i ]ᵒ Q˙  ⊨  R ∗ P ↪⟨ e ⟩ᵀ[ i ]ᵒ λ v → R ∗ Q˙ v
  ↪⟨⟩ᵀᵒ-frameˡ (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, ∗-assocˡ » hor-frameˡ P∗R∗S⊢⟨e⟩Q , R∗IndSa

  -- Turn ↪⟨ ⟩ᵀᵒ into ↪⟨ ⟩ᴾᵒ

  ↪⟨⟩ᵀᵒ⇒↪⟨⟩ᴾᵒ :  P ↪⟨ e ⟩ᵀ[ i ]ᵒ Q˙  ⊨  P ↪⟨ e ⟩ᴾᵒ Q˙
  ↪⟨⟩ᵀᵒ⇒↪⟨⟩ᴾᵒ (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, hor-ᵀ⇒ᴾ P∗R∗S⊢⟨e⟩Q , R∗IndSa

  -- Make ↪⟨ ⟩ᵀᵒ out of ○ᵒ

  ○ᵒ⇒↪⟨⟩ᵀᵒ :  P ∗ R ⊢[ ∞ ]⟨ e ⟩ᵀ[ i ] Q˙ →  ○ᵒ R  ⊨  P ↪⟨ e ⟩ᵀ[ i ]ᵒ Q˙
  ○ᵒ⇒↪⟨⟩ᵀᵒ P∗R⊢⟨e⟩Q (-, -ᴵ, -, S∗T⊢R , S∗IndTa) =
    -, -ᴵ, -, ∗-monoʳ S∗T⊢R » P∗R⊢⟨e⟩Q , S∗IndTa
