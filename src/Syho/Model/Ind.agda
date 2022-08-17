--------------------------------------------------------------------------------
-- Interpreting the indirection modality ○
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Ind where

open import Base.Size using (∞)
open import Base.Func using (it)
open import Base.Prod using (∑-syntax; _×_; _,_)
open import Base.Sum using (_⊎_)
open import Syho.Logic.Prop using (Prop'; _∗_; Basic)
open import Syho.Logic.Core using (_⊢[_]_; _»_; ∗-assocˡ; ∗-monoʳ)
open import Syho.Model.ERA using (ERA)
open import Syho.Model.ERA.Ind using (line-indˣ; line-ind□)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ; indˣ; ind□; injᴳ)
open import Syho.Model.Prop using (Propᵒ; _⊨_; _∗ᵒ_; ∗ᵒ-assocʳ)
open import Syho.Model.Basic using (⸨_⸩ᴮ)

open ERA Globᴱᴿᴬ using (_⊑_)

private variable
  P Q R :  Prop' ∞

--------------------------------------------------------------------------------
-- ind :  Interpret the indirection modality without the monotonicity patch

ind :  Prop' ∞ →  Propᵒ
ind P a =  ∑ i ,
  a ⊑ injᴳ indˣ (line-indˣ i P)  ⊎  a ⊑ injᴳ ind□ (line-ind□ i P)

--------------------------------------------------------------------------------
-- ○ᵒ :  Interpret the indirection modality ○

infix 8 ○ᵒ_
○ᵒ_ :  Prop' ∞ →  Propᵒ
(○ᵒ P) a =  ∑ Q , ∑ R , ∑ BasicR ,
  R ∗ Q ⊢[ ∞ ] P  ×  (⸨ R ⸩ᴮ {{BasicR}} ∗ᵒ ind Q) a

abstract

  ○ᵒ-mono :  {{_ : Basic R}} →  R ∗ P ⊢[ ∞ ] Q →  ⸨ R ⸩ᴮ ∗ᵒ ○ᵒ P ⊨ ○ᵒ Q
  ○ᵒ-mono R∗P⊢Q (_ , b∙c⊑a , Rb , _ , _ , BasicT , T∗S⊢P , T∗indSc) =
    let instance _ = BasicT in
    _ , _ , it , (∗-assocˡ » ∗-monoʳ T∗S⊢P » R∗P⊢Q) ,
    ∗ᵒ-assocʳ (_ , b∙c⊑a , Rb , T∗indSc)
