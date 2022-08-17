--------------------------------------------------------------------------------
-- Interpreting ○, ↪=>>, ↪⟨ ⟩ᴾ, and ↪⟨ ⟩ᵀ
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Ind where

open import Base.Size using (∞)
open import Base.Func using (it)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_)
open import Base.Sum using (_⊎_)
open import Base.Nat using (ℕ; suc)
open import Syho.Lang.Expr using (Type; Expr; Val)
open import Syho.Logic.Prop using (Prop'; _∗_; Basic)
open import Syho.Logic.Core using (_⊢[_]_; _»_; ∗-assocˡ; ∗-assocʳ; ∗-monoˡ;
  ∗-monoʳ; pullʳˡ)
open import Syho.Logic.Supd using (_⊢[_][_]=>>_; =>>-suc; _ᵘ»ᵘ_; =>>-frameˡ;
  =>>-frameʳ)
open import Syho.Logic.Hor using (_⊢[_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ[_]_; horᵀ-suc; _ʰ»ᵘ_;
  _ᵘ»ʰ_; hor-frameˡ)
open import Syho.Model.ERA using (ERA)
open import Syho.Model.ERA.Ind using (line-indˣ; line-ind□)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ; indˣ; ind□; injᴳ)
open import Syho.Model.Prop using (Propᵒ; _⊨_; _∗ᵒ_; ∗ᵒ-assocʳ)
open import Syho.Model.Basic using (⸨_⸩ᴮ)

open ERA Globᴱᴿᴬ using (_⊑_)

private variable
  i j :  ℕ
  T :  Type
  P P' Q Q' R :  Prop' ∞
  Qᵛ Q'ᵛ :  Val T →  Prop' ∞
  e :  Expr ∞ T

--------------------------------------------------------------------------------
-- indᵒ :  Indirection base

indᵒ :  Prop' ∞ →  Propᵒ
indᵒ P a =  ∑ i ,
  a ⊑ injᴳ indˣ (line-indˣ i P)  ⊎  a ⊑ injᴳ ind□ (line-ind□ i P)

--------------------------------------------------------------------------------
-- ○ᵒ :  Interpret the indirection modality ○

infix 8 ○ᵒ_
○ᵒ_ :  Prop' ∞ →  Propᵒ
(○ᵒ P) a =  ∑ Q , ∑ R , ∑ BasicR ,
  R ∗ Q ⊢[ ∞ ] P  ×  (⸨ R ⸩ᴮ {{BasicR}} ∗ᵒ indᵒ Q) a

abstract

  ○ᵒ-mono :  {{_ : Basic R}} →  R ∗ P ⊢[ ∞ ] Q →  ⸨ R ⸩ᴮ ∗ᵒ ○ᵒ P ⊨ ○ᵒ Q
  ○ᵒ-mono R∗P⊢Q (-, b∙c⊑a , Rb , -, -, BasicT , T∗S⊢P , T∗indSc) =
    let instance _ = BasicT in
    -, -, it , (∗-assocˡ » ∗-monoʳ T∗S⊢P » R∗P⊢Q) ,
    ∗ᵒ-assocʳ (-, b∙c⊑a , Rb , T∗indSc)

--------------------------------------------------------------------------------
-- ↪=>>ᵒ :  Interpret the super-update precursor ↪=>>

infixr 5 _↪[_]=>>ᵒ_
_↪[_]=>>ᵒ_ :  Prop' ∞ →  ℕ →  Prop' ∞ →  Propᵒ
(P ↪[ i ]=>>ᵒ Q) a =  ∑ R , ∑ S , ∑ BasicS ,
  P ∗ S ∗ R ⊢[ ∞ ][ i ]=>> Q  ×  (⸨ S ⸩ᴮ {{BasicS}} ∗ᵒ indᵒ R) a

abstract

  ↪=>>ᵒ-suc :  P ↪[ i ]=>>ᵒ Q  ⊨  P ↪[ suc i ]=>>ᵒ Q
  ↪=>>ᵒ-suc (-, -, BasicS , P∗S∗R⊢[i]=>>Q , S∗Ra) =
    -, -, BasicS , =>>-suc P∗S∗R⊢[i]=>>Q , S∗Ra

  ↪=>>ᵒ-monoˡᵘ-∗ :  {{_ : Basic R}} →
    R ∗ P' ⊢[ ∞ ][ i ]=>> P →  ⸨ R ⸩ᴮ ∗ᵒ (P ↪[ i ]=>>ᵒ Q)  ⊨  P' ↪[ i ]=>>ᵒ Q
  ↪=>>ᵒ-monoˡᵘ-∗ R∗P'⊢=>>P
    (-, b∙c⊑a , Rb , -, -, BasicT , P∗T∗S⊢=>>Q , T∗indSc) =
    let instance _ = BasicT in  -, -, it ,
    -- P'∗(R∗T)∗S ⊢ P'∗R∗T∗S ⊢ R∗P'∗T∗S ⊢ (R∗P')∗T∗S ⊢=>> P∗T∗S ⊢=>> Q
    (∗-monoʳ ∗-assocˡ »
      pullʳˡ » ∗-assocʳ » =>>-frameʳ R∗P'⊢=>>P ᵘ»ᵘ P∗T∗S⊢=>>Q) ,
    ∗ᵒ-assocʳ (-, b∙c⊑a , Rb , T∗indSc)

  ↪=>>ᵒ-monoʳᵘ-∗ :  {{_ : Basic R}} →
    R ∗ Q ⊢[ ∞ ][ i ]=>> Q' →  ⸨ R ⸩ᴮ ∗ᵒ (P ↪[ i ]=>>ᵒ Q)  ⊨  P ↪[ i ]=>>ᵒ Q'
  ↪=>>ᵒ-monoʳᵘ-∗ R∗Q⊢=>>Q'
    (-, b∙c⊑a , Rb , -, -, BasicT , P∗T∗S⊢=>>Q , T∗indSc) =
    let instance _ = BasicT in  -, -, it ,
    -- P∗(R∗T)∗S ⊢ P∗R∗T∗S ⊢=>> R∗P∗T∗S ⊢=>> R∗Q ⊢ Q'
    (∗-monoʳ ∗-assocˡ » pullʳˡ » =>>-frameˡ P∗T∗S⊢=>>Q ᵘ»ᵘ R∗Q⊢=>>Q') ,
    ∗ᵒ-assocʳ (-, b∙c⊑a , Rb , T∗indSc)

--------------------------------------------------------------------------------
-- ↪⟨ ⟩ᴾᵒ :  Interpret the partial Hoare-triple precursor ↪⟨ ⟩ᴾ

infixr 5 _↪⟨_⟩ᴾᵒ_
_↪⟨_⟩ᴾᵒ_ :  Prop' ∞ →  Expr ∞ T →  (Val T → Prop' ∞) →  Propᵒ
(P ↪⟨ e ⟩ᴾᵒ Qᵛ) a =  ∑ R , ∑ S , ∑ BasicS ,
  P ∗ S ∗ R ⊢[ ∞ ]⟨ e ⟩ᴾ Qᵛ  ×  (⸨ S ⸩ᴮ {{BasicS}} ∗ᵒ indᵒ R) a

abstract

  ↪⟨⟩ᴾᵒ-monoˡᵘ-∗ :  {{_ : Basic R}} →  R ∗ P' ⊢[ ∞ ][ i ]=>> P →
                    ⸨ R ⸩ᴮ ∗ᵒ (P ↪⟨ e ⟩ᴾᵒ Qᵛ)  ⊨  P' ↪⟨ e ⟩ᴾᵒ Qᵛ
  ↪⟨⟩ᴾᵒ-monoˡᵘ-∗ R∗P'⊢=>>P
    (-, b∙c⊑a , Rb , -, -, BasicT , P∗T∗S⊢⟨e⟩Q , T∗indSc) =
    let instance _ = BasicT in  -, -, it ,
    -- P'∗(R∗T)∗S ⊢ P'∗R∗T∗S ⊢ R∗P'∗T∗S ⊢ (R∗P')∗T∗S ⊢=>> P∗T∗S ⊢⟨e⟩ᴾ Qᵛ
    (∗-monoʳ ∗-assocˡ »
      pullʳˡ » ∗-assocʳ » =>>-frameʳ R∗P'⊢=>>P ᵘ»ʰ P∗T∗S⊢⟨e⟩Q) ,
    ∗ᵒ-assocʳ (-, b∙c⊑a , Rb , T∗indSc)

  ↪⟨⟩ᴾᵒ-monoʳᵘ-∗ :  {{_ : Basic R}} →  (∀ v →  R ∗ Qᵛ v ⊢[ ∞ ][ i ]=>> Q'ᵛ v) →
                    ⸨ R ⸩ᴮ ∗ᵒ (P ↪⟨ e ⟩ᴾᵒ Qᵛ)  ⊨  P ↪⟨ e ⟩ᴾᵒ Q'ᵛ
  ↪⟨⟩ᴾᵒ-monoʳᵘ-∗ R∗Q⊢=>>Q'
    (-, b∙c⊑a , Rb , -, -, BasicT , P∗T∗S⊢⟨e⟩Q , T∗indSc) =
    let instance _ = BasicT in  -, -, it ,
    -- P∗(R∗T)∗S ⊢ P∗R∗T∗S ⊢ R∗P∗T∗S ⊢⟨e⟩ᴾ R∗Q ⊢=>> Q'
    (∗-monoʳ ∗-assocˡ » pullʳˡ » hor-frameˡ P∗T∗S⊢⟨e⟩Q ʰ»ᵘ R∗Q⊢=>>Q') ,
    ∗ᵒ-assocʳ (-, b∙c⊑a , Rb , T∗indSc)

--------------------------------------------------------------------------------
-- ↪⟨ ⟩ᵀᵒ :  Interpret the partial Hoare-triple precursor ↪⟨ ⟩ᵀ

infixr 5 _↪⟨_⟩ᵀ[_]ᵒ_
_↪⟨_⟩ᵀ[_]ᵒ_ :  Prop' ∞ →  Expr ∞ T →  ℕ →  (Val T → Prop' ∞) →  Propᵒ
(P ↪⟨ e ⟩ᵀ[ i ]ᵒ Qᵛ) a =  ∑ R , ∑ S , ∑ BasicS ,
  P ∗ S ∗ R ⊢[ ∞ ]⟨ e ⟩ᵀ[ i ] Qᵛ  ×  (⸨ S ⸩ᴮ {{BasicS}} ∗ᵒ indᵒ R) a

abstract

  ↪⟨⟩ᵀᵒ-suc :  P ↪⟨ e ⟩ᵀ[ i ]ᵒ Qᵛ  ⊨  P ↪⟨ e ⟩ᵀ[ suc i ]ᵒ Qᵛ
  ↪⟨⟩ᵀᵒ-suc (-, -, BasicS , P∗S∗R⊢⟨e⟩[i]Q , S∗Ra) =
    -, -, BasicS , horᵀ-suc P∗S∗R⊢⟨e⟩[i]Q , S∗Ra

  ↪⟨⟩ᵀᵒ-monoˡᵘ-∗ :  {{_ : Basic R}} →  R ∗ P' ⊢[ ∞ ][ j ]=>> P →
                    ⸨ R ⸩ᴮ ∗ᵒ (P ↪⟨ e ⟩ᵀ[ i ]ᵒ Qᵛ)  ⊨  P' ↪⟨ e ⟩ᵀ[ i ]ᵒ Qᵛ
  ↪⟨⟩ᵀᵒ-monoˡᵘ-∗ R∗P'⊢=>>P
    (-, b∙c⊑a , Rb , -, -, BasicT , P∗T∗S⊢⟨e⟩Q , T∗indSc) =
    let instance _ = BasicT in  -, -, it ,
    -- P'∗(R∗T)∗S ⊢ P'∗R∗T∗S ⊢ R∗P'∗T∗S ⊢ (R∗P')∗T∗S ⊢=>> P∗T∗S ⊢⟨e⟩ᵀ Qᵛ
    (∗-monoʳ ∗-assocˡ »
      pullʳˡ » ∗-assocʳ » =>>-frameʳ R∗P'⊢=>>P ᵘ»ʰ P∗T∗S⊢⟨e⟩Q) ,
    ∗ᵒ-assocʳ (-, b∙c⊑a , Rb , T∗indSc)

  ↪⟨⟩ᵀᵒ-monoʳᵘ-∗ :  {{_ : Basic R}} →  (∀ v →  R ∗ Qᵛ v ⊢[ ∞ ][ j ]=>> Q'ᵛ v) →
                    ⸨ R ⸩ᴮ ∗ᵒ (P ↪⟨ e ⟩ᵀ[ i ]ᵒ Qᵛ)  ⊨  P ↪⟨ e ⟩ᵀ[ i ]ᵒ Q'ᵛ
  ↪⟨⟩ᵀᵒ-monoʳᵘ-∗ R∗Q⊢=>>Q'
    (-, b∙c⊑a , Rb , -, -, BasicT , P∗T∗S⊢⟨e⟩Q , T∗indSc) =
    let instance _ = BasicT in  -, -, it ,
    -- P∗(R∗T)∗S ⊢ P∗R∗T∗S ⊢ R∗P∗T∗S ⊢⟨e⟩ᵀ R∗Q ⊢ Q'
    (∗-monoʳ ∗-assocˡ » pullʳˡ » hor-frameˡ P∗T∗S⊢⟨e⟩Q ʰ»ᵘ R∗Q⊢=>>Q') ,
    ∗ᵒ-assocʳ (-, b∙c⊑a , Rb , T∗indSc)
