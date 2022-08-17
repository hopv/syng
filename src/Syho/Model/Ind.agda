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
open import Syho.Logic.Prop using (Prop'; _∗_; Basic)
open import Syho.Logic.Core using (_⊢[_]_; _»_; ∗-assocˡ; ∗-assocʳ; ∗-monoˡ;
  ∗-monoʳ; pullʳˡ)
open import Syho.Logic.Supd using (_⊢[_][_]=>>_; =>>-suc; =>>-frameˡ; _ᵘ»_)
open import Syho.Model.ERA using (ERA)
open import Syho.Model.ERA.Ind using (line-indˣ; line-ind□)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ; indˣ; ind□; injᴳ)
open import Syho.Model.Prop using (Propᵒ; _⊨_; _∗ᵒ_; ∗ᵒ-assocʳ)
open import Syho.Model.Basic using (⸨_⸩ᴮ)

open ERA Globᴱᴿᴬ using (_⊑_)

private variable
  P P' Q Q' R :  Prop' ∞
  i :  ℕ

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
  ↪=>>ᵒ-suc (_ , _ , BasicS , P∗S∗R⊢[i]=>>Q , S∗Ra) =
    _ , _ , BasicS , =>>-suc P∗S∗R⊢[i]=>>Q , S∗Ra

  ↪=>>ᵒ-monoˡ-∗ :  {{_ : Basic R}} →
    R ∗ P' ⊢[ ∞ ] P →  ⸨ R ⸩ᴮ ∗ᵒ (P ↪[ i ]=>>ᵒ Q)  ⊨  P' ↪[ i ]=>>ᵒ Q
  ↪=>>ᵒ-monoˡ-∗ R∗P'⊢P (-, b∙c⊑a , Rb , -, -, BasicT , P∗T∗S⊢=>>Q , T∗indSc) =
    let instance _ = BasicT in  -, -, it ,
    -- P'∗(R∗T)∗S ⊢ P'∗R∗T∗S ⊢ R∗P'∗T∗S ⊢ (R∗P')∗T∗S ⊢ P∗T∗S ⊢=>> Q
    (∗-monoʳ ∗-assocˡ » pullʳˡ » ∗-assocʳ » ∗-monoˡ R∗P'⊢P » P∗T∗S⊢=>>Q) ,
    ∗ᵒ-assocʳ (-, b∙c⊑a , Rb , T∗indSc)

  ↪=>>ᵒ-monoʳ-∗ :  {{_ : Basic R}} →
    R ∗ Q ⊢[ ∞ ] Q' →  ⸨ R ⸩ᴮ ∗ᵒ (P ↪[ i ]=>>ᵒ Q)  ⊨  P ↪[ i ]=>>ᵒ Q'
  ↪=>>ᵒ-monoʳ-∗ R∗Q⊢Q' (-, b∙c⊑a , Rb , -, -, BasicT , P∗T∗S⊢=>>Q , T∗indSc) =
    let instance _ = BasicT in  -, -, it ,
    -- P∗(R∗T)∗S ⊢ P∗R∗T∗S ⊢ R∗P∗T∗S ⊢=>> R∗Q ⊢ Q'
    (∗-monoʳ ∗-assocˡ » pullʳˡ » =>>-frameˡ P∗T∗S⊢=>>Q ᵘ» R∗Q⊢Q') ,
    ∗ᵒ-assocʳ (-, b∙c⊑a , Rb , T∗indSc)
