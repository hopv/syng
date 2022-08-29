--------------------------------------------------------------------------------
-- Interpreting ○, ↪⇛, ↪⟨ ⟩ᴾ, and ↪⟨ ⟩ᵀ
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Ind where

open import Base.Level using (2ᴸ)
open import Base.Size using (∞)
open import Base.Func using (_$_)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_; ∑ᴵ-syntax; -ᴵ,_)
open import Base.Sum using (_⊎_; inj₀; inj₁)
open import Base.Nat using (ℕ; suc)
open import Syho.Lang.Expr using (Type; Expr; Val)
open import Syho.Logic.Prop using (Prop'; _∗_; Basic)
open import Syho.Logic.Core using (_⊢[_]_; _»_; ∗-assocˡ; ∗-assocʳ; ∗-monoˡ;
  ∗-monoʳ; pullʳˡ)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_; ⇛-suc; _ᵘ»ᵘ_; ⇛-frameˡ;
  ⇛-frameʳ)
open import Syho.Logic.Hor using (_⊢[_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ[_]_; horᵀ-suc; _ʰ»ᵘ_;
  _ᵘ»ʰ_; hor-frameˡ)
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Ind using (line-indˣ; line-ind□)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ; indˣ; ind□; injᴳ)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨_; ∃ᵒ-syntax; ∃ᴵ-syntax;
  ⌜_⌝ᵒ; _×ᵒ_; _⊎ᵒ_; _∗ᵒ_; ●_; ⊎ᵒ-Mono; ∗ᵒ-Mono; ∗ᵒ-assocʳ; ●-Mono)
open import Syho.Model.Prop.Basic using (⸨_⸩ᴮ)

private variable
  i j :  ℕ
  T :  Type
  P P' Q Q' R :  Prop' ∞
  Qᵛ Q'ᵛ :  Val T →  Prop' ∞
  e :  Expr ∞ T

--------------------------------------------------------------------------------
-- Ind :  Indirection base

Indˣ Ind□ Ind :  Prop' ∞ →  Propᵒ 2ᴸ
Indˣ P =  ∃ᵒ i , ● injᴳ indˣ (line-indˣ i P)
Ind□ P =  ∃ᵒ i , ● injᴳ ind□ (line-ind□ i P)
Ind P =  Indˣ P ⊎ᵒ Ind□ P

abstract

  Indˣ-Mono :  Monoᵒ (Indˣ P)
  Indˣ-Mono a⊑b (i , Ownˣ) =  i , ●-Mono a⊑b Ownˣ

  Ind□-Mono :  Monoᵒ (Ind□ P)
  Ind□-Mono a⊑b (i , ●□) =  i , ●-Mono a⊑b ●□

  Ind-Mono :  Monoᵒ (Ind P)
  Ind-Mono =  ⊎ᵒ-Mono Indˣ-Mono Ind□-Mono

--------------------------------------------------------------------------------
-- ○ᵒ :  Interpret the indirection modality ○

infix 8 ○ᵒ_
○ᵒ_ :  Prop' ∞ →  Propᵒ 2ᴸ
○ᵒ P =  ∃ᵒ Q , ∃ᴵ BasicQ , ∃ᵒ R ,
  ⌜ Q ∗ R ⊢[ ∞ ] P ⌝ᵒ  ×ᵒ  ⸨ Q ⸩ᴮ {{BasicQ}}  ∗ᵒ  Ind R

abstract

  ○ᵒ-Mono :  Monoᵒ (○ᵒ P)
  ○ᵒ-Mono a⊑b (-, -ᴵ, -, Q∗R⊢P , Q∗IndRa) =
    -, -ᴵ, -, Q∗R⊢P , ∗ᵒ-Mono a⊑b Q∗IndRa

  ○ᵒ-mono :  P ⊢[ ∞ ] Q →  ○ᵒ P ⊨ ○ᵒ Q
  ○ᵒ-mono P⊢Q (-, -ᴵ, -, R∗S⊢P , R∗IndSa) =
    -, -ᴵ, -, R∗S⊢P » P⊢Q , R∗IndSa

  ○ᵒ-eatˡ :  {{_ : Basic Q}} →  ⸨ Q ⸩ᴮ ∗ᵒ ○ᵒ P ⊨ ○ᵒ (Q ∗ P)
  ○ᵒ-eatˡ (-, -, b∙c⊑a , Qb , -, -ᴵ, -, R∗S⊢P , R∗IndSc) =
    -, -ᴵ, -, ∗-assocˡ » ∗-monoʳ R∗S⊢P , ∗ᵒ-assocʳ (-, -, b∙c⊑a , Qb , R∗IndSc)

--------------------------------------------------------------------------------
-- ↪⇛ᵒ :  Interpret the super-update precursor ↪⇛

infixr 5 _↪[_]⇛ᵒ_
_↪[_]⇛ᵒ_ :  Prop' ∞ →  ℕ →  Prop' ∞ →  Propᵒ 2ᴸ
(P ↪[ i ]⇛ᵒ Q) a =  ∑ R , ∑ᴵ BasicR , ∑ S ,
  P ∗ R ∗ S ⊢[ ∞ ][ i ]⇛ Q  ×  (⸨ R ⸩ᴮ {{BasicR}} ∗ᵒ Ind S) a

abstract

  ↪⇛ᵒ-Mono :  Monoᵒ (P ↪[ i ]⇛ᵒ Q)
  ↪⇛ᵒ-Mono a⊑b (-, -ᴵ, -, P∗R∗S⊢Q , R∗IndSa) =
    -, -ᴵ, -, P∗R∗S⊢Q , ∗ᵒ-Mono a⊑b R∗IndSa

  ↪⇛ᵒ-suc :  P ↪[ i ]⇛ᵒ Q  ⊨  P ↪[ suc i ]⇛ᵒ Q
  ↪⇛ᵒ-suc (-, -ᴵ, -, P∗R∗S⊢⇛Q , R∗IndSa) =
    -, -ᴵ, -, ⇛-suc P∗R∗S⊢⇛Q , R∗IndSa

  ↪⇛ᵒ-eatˡ⁻ˡᵘ :  {{_ : Basic R}} →
    R ∗ P' ⊢[ ∞ ][ i ]⇛ P →  ⸨ R ⸩ᴮ ∗ᵒ (P ↪[ i ]⇛ᵒ Q)  ⊨  P' ↪[ i ]⇛ᵒ Q
  ↪⇛ᵒ-eatˡ⁻ˡᵘ R∗P'⊢⇛P (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⇛Q , S∗IndTc) =
    -, -ᴵ, -,
    -- P'∗(R∗S)∗T ⊢ P'∗R∗S∗T ⊢ R∗P'∗S∗T ⊢ (R∗P')∗S∗T ⊢⇛ P∗S∗T ⊢⇛ Q
    ∗-monoʳ ∗-assocˡ » pullʳˡ » ∗-assocʳ » ⇛-frameʳ R∗P'⊢⇛P ᵘ»ᵘ P∗S∗T⊢⇛Q ,
    ∗ᵒ-assocʳ (-, -, b∙c⊑a , Rb , S∗IndTc)

  ↪⇛ᵒ-eatˡ⁻ʳ :  {{_ : Basic R}} →
    ⸨ R ⸩ᴮ ∗ᵒ (P ↪[ i ]⇛ᵒ Q)  ⊨  P ↪[ i ]⇛ᵒ R ∗ Q
  ↪⇛ᵒ-eatˡ⁻ʳ (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⇛Q , S∗IndTc) =  -, -ᴵ, -,
    -- P∗(R∗S)∗T ⊢ P∗R∗S∗T ⊢⇛ R∗P∗S∗T ⊢⇛ R∗Q
    ∗-monoʳ ∗-assocˡ » pullʳˡ » ⇛-frameˡ P∗S∗T⊢⇛Q ,
    ∗ᵒ-assocʳ (-, -, b∙c⊑a , Rb , S∗IndTc)

  ↪⇛ᵒ-monoʳᵘ :  Q ⊢[ ∞ ][ i ]⇛ Q' →  P ↪[ i ]⇛ᵒ Q  ⊨  P ↪[ i ]⇛ᵒ Q'
  ↪⇛ᵒ-monoʳᵘ Q⊢⇛Q' (-, -ᴵ, -, P∗R∗S⊢⇛Q , R∗IndSa) =
    -, -ᴵ, -, P∗R∗S⊢⇛Q ᵘ»ᵘ Q⊢⇛Q' , R∗IndSa

  ↪⇛ᵒ-frameˡ :  P ↪[ i ]⇛ᵒ Q  ⊨  R ∗ P ↪[ i ]⇛ᵒ R ∗ Q
  ↪⇛ᵒ-frameˡ (-, -ᴵ, -, P∗R∗S⊢⇛Q , R∗IndSa) =
    -, -ᴵ, -, ∗-assocˡ » ⇛-frameˡ P∗R∗S⊢⇛Q , R∗IndSa

  ○ᵒ⇒↪⇛ᵒ :  P ∗ R ⊢[ ∞ ][ i ]⇛ Q →  ○ᵒ R  ⊨  P ↪[ i ]⇛ᵒ Q
  ○ᵒ⇒↪⇛ᵒ P∗R⊢⇛Q (-, -ᴵ, -, S∗T⊢R , S∗IndTa) =
    -, -ᴵ, -, ∗-monoʳ S∗T⊢R » P∗R⊢⇛Q , S∗IndTa

--------------------------------------------------------------------------------
-- ↪⟨ ⟩ᴾᵒ :  Interpret the partial Hoare-triple precursor ↪⟨ ⟩ᴾ

infixr 5 _↪⟨_⟩ᴾᵒ_
_↪⟨_⟩ᴾᵒ_ :  Prop' ∞ →  Expr ∞ T →  (Val T → Prop' ∞) →  Propᵒ 2ᴸ
P ↪⟨ e ⟩ᴾᵒ Qᵛ =  ∃ᵒ R , ∃ᴵ BasicR , ∃ᵒ S ,
  ⌜ P ∗ R ∗ S ⊢[ ∞ ]⟨ e ⟩ᴾ Qᵛ ⌝ᵒ  ×ᵒ  ⸨ R ⸩ᴮ {{BasicR}}  ∗ᵒ  Ind S

abstract

  ↪⟨⟩ᴾᵒ-Mono :  Monoᵒ (P ↪⟨ e ⟩ᴾᵒ Qᵛ)
  ↪⟨⟩ᴾᵒ-Mono a⊑b (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , ∗ᵒ-Mono a⊑b R∗IndSa

  ↪⟨⟩ᴾᵒ-eatˡ⁻ˡᵘ :  {{_ : Basic R}} →  R ∗ P' ⊢[ ∞ ][ i ]⇛ P →
                   ⸨ R ⸩ᴮ ∗ᵒ (P ↪⟨ e ⟩ᴾᵒ Qᵛ)  ⊨  P' ↪⟨ e ⟩ᴾᵒ Qᵛ
  ↪⟨⟩ᴾᵒ-eatˡ⁻ˡᵘ R∗P'⊢⇛P (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⟨e⟩Q , S∗IndTc) =
    -, -ᴵ, -,
    -- P'∗(R∗S)∗T ⊢ P'∗R∗S∗T ⊢ R∗P'∗S∗T ⊢ (R∗P')∗S∗T ⊢⇛ P∗S∗T ⊢⟨e⟩ᴾ Qᵛ
    ∗-monoʳ ∗-assocˡ » pullʳˡ » ∗-assocʳ » ⇛-frameʳ R∗P'⊢⇛P ᵘ»ʰ P∗S∗T⊢⟨e⟩Q ,
    ∗ᵒ-assocʳ (-, -, b∙c⊑a , Rb , S∗IndTc)

  ↪⟨⟩ᴾᵒ-eatˡ⁻ʳ :  {{_ : Basic R}} →
    ⸨ R ⸩ᴮ ∗ᵒ (P ↪⟨ e ⟩ᴾᵒ Qᵛ)  ⊨  P ↪⟨ e ⟩ᴾᵒ λ v → R ∗ Qᵛ v
  ↪⟨⟩ᴾᵒ-eatˡ⁻ʳ (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⟨e⟩Q , S∗IndTc) =  -, -ᴵ, -,
    -- P∗(R∗S)∗T ⊢ P∗R∗S∗T ⊢ R∗P∗S∗T ⊢⟨e⟩ᴾ R∗Q
    ∗-monoʳ ∗-assocˡ » pullʳˡ » hor-frameˡ P∗S∗T⊢⟨e⟩Q ,
    ∗ᵒ-assocʳ (-, -, b∙c⊑a , Rb , S∗IndTc)

  ↪⟨⟩ᴾᵒ-monoʳᵘ :  (∀ v →  Qᵛ v ⊢[ ∞ ][ i ]⇛ Q'ᵛ v) →
                  P ↪⟨ e ⟩ᴾᵒ Qᵛ  ⊨  P ↪⟨ e ⟩ᴾᵒ Q'ᵛ
  ↪⟨⟩ᴾᵒ-monoʳᵘ ∀vQ⊢⇛Q' (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, P∗R∗S⊢⟨e⟩Q ʰ»ᵘ ∀vQ⊢⇛Q' , R∗IndSa

  ↪⟨⟩ᴾᵒ-frameˡ :  P ↪⟨ e ⟩ᴾᵒ Qᵛ  ⊨  R ∗ P ↪⟨ e ⟩ᴾᵒ λ v → R ∗ Qᵛ v
  ↪⟨⟩ᴾᵒ-frameˡ (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, ∗-assocˡ » hor-frameˡ P∗R∗S⊢⟨e⟩Q , R∗IndSa

  ○ᵒ⇒↪⟨⟩ᴾᵒ :  P ∗ R ⊢[ ∞ ]⟨ e ⟩ᴾ Qᵛ →  ○ᵒ R  ⊨  P ↪⟨ e ⟩ᴾᵒ Qᵛ
  ○ᵒ⇒↪⟨⟩ᴾᵒ P∗R⊢⟨e⟩Q (-, -ᴵ, -, S∗T⊢R , S∗IndTa) =
    -, -ᴵ, -, ∗-monoʳ S∗T⊢R » P∗R⊢⟨e⟩Q , S∗IndTa

--------------------------------------------------------------------------------
-- ↪⟨ ⟩ᵀᵒ :  Interpret the partial Hoare-triple precursor ↪⟨ ⟩ᵀ

infixr 5 _↪⟨_⟩ᵀ[_]ᵒ_
_↪⟨_⟩ᵀ[_]ᵒ_ :  Prop' ∞ →  Expr ∞ T →  ℕ →  (Val T → Prop' ∞) →  Propᵒ 2ᴸ
P ↪⟨ e ⟩ᵀ[ i ]ᵒ Qᵛ =  ∃ᵒ R , ∃ᴵ BasicR , ∃ᵒ S ,
  ⌜ P ∗ R ∗ S ⊢[ ∞ ]⟨ e ⟩ᵀ[ i ] Qᵛ ⌝ᵒ  ×ᵒ  ⸨ R ⸩ᴮ {{BasicR}}  ∗ᵒ  Ind S

abstract

  ↪⟨⟩ᵀᵒ-Mono :  Monoᵒ (P ↪⟨ e ⟩ᵀ[ i ]ᵒ Qᵛ)
  ↪⟨⟩ᵀᵒ-Mono a⊑b (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , ∗ᵒ-Mono a⊑b R∗IndSa

  ↪⟨⟩ᵀᵒ-suc :  P ↪⟨ e ⟩ᵀ[ i ]ᵒ Qᵛ  ⊨  P ↪⟨ e ⟩ᵀ[ suc i ]ᵒ Qᵛ
  ↪⟨⟩ᵀᵒ-suc (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, horᵀ-suc P∗R∗S⊢⟨e⟩Q , R∗IndSa

  ↪⟨⟩ᵀᵒ-eatˡ⁻ˡᵘ :  {{_ : Basic R}} →  R ∗ P' ⊢[ ∞ ][ j ]⇛ P →
                   ⸨ R ⸩ᴮ ∗ᵒ (P ↪⟨ e ⟩ᵀ[ i ]ᵒ Qᵛ)  ⊨  P' ↪⟨ e ⟩ᵀ[ i ]ᵒ Qᵛ
  ↪⟨⟩ᵀᵒ-eatˡ⁻ˡᵘ R∗P'⊢⇛P (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⟨e⟩Q , S∗IndTc) =
    -, -ᴵ, -,
    -- P'∗(R∗S)∗T ⊢ P'∗R∗S∗T ⊢ R∗P'∗S∗T ⊢ (R∗P')∗S∗T ⊢⇛ P∗S∗T ⊢⟨e⟩ᵀ Qᵛ
    ∗-monoʳ ∗-assocˡ » pullʳˡ » ∗-assocʳ » ⇛-frameʳ R∗P'⊢⇛P ᵘ»ʰ P∗S∗T⊢⟨e⟩Q ,
    ∗ᵒ-assocʳ (-, -, b∙c⊑a , Rb , S∗IndTc)

  ↪⟨⟩ᵀᵒ-eatˡ⁻ʳ :  {{_ : Basic R}} →
    ⸨ R ⸩ᴮ ∗ᵒ (P ↪⟨ e ⟩ᵀ[ i ]ᵒ Qᵛ)  ⊨  P ↪⟨ e ⟩ᵀ[ i ]ᵒ λ v → R ∗ Qᵛ v
  ↪⟨⟩ᵀᵒ-eatˡ⁻ʳ (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⟨e⟩Q , S∗IndTc) =  -, -ᴵ, -,
    -- P∗(R∗S)∗T ⊢ P∗R∗S∗T ⊢ R∗P∗S∗T ⊢⟨e⟩ᵀ R∗Q
    ∗-monoʳ ∗-assocˡ » pullʳˡ » hor-frameˡ P∗S∗T⊢⟨e⟩Q ,
    ∗ᵒ-assocʳ (-, -, b∙c⊑a , Rb , S∗IndTc)

  ↪⟨⟩ᵀᵒ-monoʳᵘ :  (∀ v →  Qᵛ v ⊢[ ∞ ][ j ]⇛ Q'ᵛ v) →
                  P ↪⟨ e ⟩ᵀ[ i ]ᵒ Qᵛ  ⊨  P ↪⟨ e ⟩ᵀ[ i ]ᵒ Q'ᵛ
  ↪⟨⟩ᵀᵒ-monoʳᵘ ∀vQ⊢⇛Q' (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, P∗R∗S⊢⟨e⟩Q ʰ»ᵘ ∀vQ⊢⇛Q' , R∗IndSa

  ↪⟨⟩ᵀᵒ-frameˡ :  P ↪⟨ e ⟩ᵀ[ i ]ᵒ Qᵛ  ⊨  R ∗ P ↪⟨ e ⟩ᵀ[ i ]ᵒ λ v → R ∗ Qᵛ v
  ↪⟨⟩ᵀᵒ-frameˡ (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, ∗-assocˡ » hor-frameˡ P∗R∗S⊢⟨e⟩Q , R∗IndSa

  ○ᵒ⇒↪⟨⟩ᵀᵒ :  P ∗ R ⊢[ ∞ ]⟨ e ⟩ᵀ[ i ] Qᵛ →  ○ᵒ R  ⊨  P ↪⟨ e ⟩ᵀ[ i ]ᵒ Qᵛ
  ○ᵒ⇒↪⟨⟩ᵀᵒ P∗R⊢⟨e⟩Q (-, -ᴵ, -, S∗T⊢R , S∗IndTa) =
    -, -ᴵ, -, ∗-monoʳ S∗T⊢R » P∗R⊢⟨e⟩Q , S∗IndTa
