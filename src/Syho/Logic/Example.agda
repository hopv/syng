--------------------------------------------------------------------------------
-- Example
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Example where

open import Base.Func using (_$_)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using ()
open import Base.Size using (Size; ∞; !)
open import Base.Prod using (-,_)
open import Base.Nat using (ℕ; ṡ_)
open import Syho.Lang.Expr using (Addr; TyVal; loop)
open import Syho.Lang.Example using (plus◁3,4; decrloop; decrloop'; nddecrloop)
open import Syho.Logic.Prop using (Prop'; ⊤'; ⊥'; ⌜_⌝; □_; ○_; _↦_)
open import Syho.Logic.Core using (⊢-refl; _»_; ⌜⌝-intro; ∗-elimˡ; ∗⊤-intro;
  -∗-intro; □-dup)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_)
open import Syho.Logic.Ind using (□○-alloc-rec)
open import Syho.Logic.Hor using (_⊢[_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ[_]_; hor-val; hor-nd;
  hor-[])
open import Syho.Logic.Mem using (hor-🞰; hor-←)

private variable
  ι :  Size
  i n :  ℕ
  θ :  Addr
  ᵗv :  TyVal

-- □ ○ □ ○ □ ○ …

□○Loop :  Prop' ι
□○Loop =  □ ○ λ{ .! → □○Loop }

abstract

  -- Get □ ○ □ ○ □ ○ … for free

  □○Loop-alloc :  ⊤' ⊢[ ι ][ i ]⇛ □○Loop
  □○Loop-alloc =  -∗-intro (∗-elimˡ » □-dup) » □○-alloc-rec

  -- Get ⊥' after ▶ ▶ ▶ … under partial Hoare triple

  loop-⊥ :  ⊤' ⊢[ ι ]⟨ loop ⟩ᴾ λ _ → ⊥'
  loop-⊥ =  hor-[] λ{ .! → loop-⊥ }

  -- Execute plus ◁ ∇ (3 , 4)

  plus◁3,4-7 :  ⊤' ⊢[ ∞ ]⟨ plus◁3,4 ⟩ᵀ[ 0 ] λ n → ⌜ n ≡ 7 ⌝
  plus◁3,4-7 =  hor-[] $ hor-val $ ⌜⌝-intro refl

  -- decrloop θ terminates, setting the value at θ to 0

  decrloop-exec :
    ∀(n : ℕ) →  θ ↦ (-, n)  ⊢[ ∞ ]⟨ decrloop θ ⟩ᵀ[ 0 ] λ _ →  θ ↦ (-, 0)
  decrloop'-exec :
    ∀ n →  θ ↦ (-, n)  ⊢[ ∞ ]⟨ decrloop' θ n ⟩ᵀ[ 0 ] λ _ →  θ ↦ (-, 0)

  decrloop-exec n =  ∗⊤-intro » hor-🞰 $ hor-[] $ ∗-elimˡ » decrloop'-exec n

  decrloop'-exec 0 =  hor-val ⊢-refl
  decrloop'-exec (ṡ n) =
    ∗⊤-intro » hor-← $ hor-[] $ ∗-elimˡ » hor-[] $ decrloop-exec n

  -- nddecrloop terminates, setting the value at θ to 0
  -- Notably, the number of reduction steps is dynamically determined

  nddecrloop-exec :  θ ↦ ᵗv  ⊢[ ∞ ]⟨ nddecrloop θ ⟩ᵀ[ 0 ] λ _ →  θ ↦ (-, 0)
  nddecrloop-exec =
    hor-nd λ n → ∗⊤-intro » hor-← $ ∗-elimˡ » hor-[] $ decrloop-exec n
