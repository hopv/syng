--------------------------------------------------------------------------------
-- Example
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Example where

open import Base.Size using (Size; ∞)
open import Base.Thunk using (!)
open import Base.Func using (_$_)
open import Base.Eq using (_≡_; refl)
open import Base.Prod using (-,_)
open import Base.Nat using (ℕ; ṡ_)
open import Syho.Lang.Expr using (Addr; λᵛ-syntax; ṽ_; AnyVal)
open import Syho.Logic.Prop using (Prop'; ⊤'; ⊥'; ⌜_⌝₀; □_; ○_; _↦_)
open import Syho.Logic.Core using (⊢-refl; _»_; ⌜⌝₀-intro; ∗-elimˡ; ∗⊤-intro;
  -∗-intro; □-dup)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_)
open import Syho.Logic.Ind using (□○-alloc-rec)
open import Syho.Logic.Hor using (_⊢[_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ[_]_; hor-val; hor-nd;
  horᴾ-▶; horᵀ-▶; hor-◁; hor-⁏; hor-🞰; hor-←)
open import Syho.Lang.Example using (loop; plus◁3,4; decrloop; decrloop';
  nddecrloop)

private variable
  ι :  Size
  i n :  ℕ
  θ :  Addr
  av :  AnyVal

-- □ ○ □ ○ □ ○ …

□○-loop :  Prop' ι
□○-loop =  □ ○ λ{ .! → □○-loop }

abstract

  -- Get □ ○ □ ○ □ ○ … for free

  □○-loop-alloc :  ⊤' ⊢[ ι ][ i ]⇛ □○-loop
  □○-loop-alloc =  -∗-intro (∗-elimˡ » □-dup) » □○-alloc-rec

  -- Get ⊥' after ▶ ▶ ▶ … under partial Hoare triple

  loop-⊥ :  ⊤' ⊢[ ι ]⟨ loop ⟩ᴾ λ _ → ⊥'
  loop-⊥ =  horᴾ-▶ λ{ .! → loop-⊥ }

  -- Execute plus ◁ ∇ (3 , 4)

  plus◁3,4-7 :  ⊤' ⊢[ ∞ ]⟨ plus◁3,4 ⟩ᵀ[ 0 ] λᵛ n , ⌜ n ≡ 7 ⌝₀
  plus◁3,4-7 =  hor-◁ $ hor-val $ ⌜⌝₀-intro refl

  -- decrloop θ terminates, setting the value at θ to 0

  decrloop-exec :
    θ ↦ (-, ṽ n)  ⊢[ ∞ ]⟨ decrloop θ ⟩ᵀ[ 0 ]  λ _ → θ ↦ (-, ṽ 0)
  decrloop'-exec :
    θ ↦ (-, ṽ n)  ⊢[ ∞ ]⟨ decrloop' θ n ⟩ᵀ[ 0 ]  λ _ → θ ↦ (-, ṽ 0)

  decrloop-exec =  ∗⊤-intro » hor-🞰 $ hor-◁ $ ∗-elimˡ » decrloop'-exec

  decrloop'-exec {n = 0} =  hor-val ⊢-refl
  decrloop'-exec {n = ṡ n} =
    ∗⊤-intro » hor-← $ hor-⁏ $ ∗-elimˡ » horᵀ-▶ decrloop-exec

  -- nddecrloop terminates, setting the value at θ to 0
  -- Notably, the number of reduction steps is dynamically determined

  nddecrloop-exec :
    θ ↦ av  ⊢[ ∞ ]⟨ nddecrloop θ ⟩ᵀ[ 0 ]  λ _ → θ ↦ (-, ṽ 0)
  nddecrloop-exec =
    hor-nd λ _ → ∗⊤-intro » hor-← $ ∗-elimˡ » hor-⁏ decrloop-exec
