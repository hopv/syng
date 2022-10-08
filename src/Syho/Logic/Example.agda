--------------------------------------------------------------------------------
-- Example
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Example where

open import Base.Func using (_$_)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using ()
open import Base.Size using (Size; !)
open import Base.Prod using (-,_)
open import Base.Nat using (ℕ; ṡ_)
open import Syho.Lang.Expr using (Addr; TyVal; loop)
open import Syho.Lang.Example using (plus◁3,4; decrloop; decrloop'; nddecrloop)
open import Syho.Logic.Prop using (Prop'; Prop∞; ⊤'; ⊥'; ⌜_⌝; □_; ○_; _↦_)
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
  X :  Set₀
  P :  Prop∞
  Q˙ :  X → Prop∞

-- □ ○ □ ○ □ ○ …

□○Loop :  Prop' ι
□○Loop =  □ ○ λ{ .! → □○Loop }

abstract

  ------------------------------------------------------------------------------
  -- Get □ ○ □ ○ □ ○ … for free

  □○Loop-alloc :  ⊤' ⊢[ ι ][ i ]⇛ □○Loop
  □○Loop-alloc =  -∗-intro (∗-elimˡ » □-dup) » □○-alloc-rec

  ------------------------------------------------------------------------------
  -- Get any partial Hoare triple on loop
  -- This uses coinduction by thunk for the infinite execution of loop

  horᴾ-loop :  P ⊢[ ι ]⟨ loop ⟩ᴾ Q˙
  horᴾ-loop =  hor-[] λ{ .! → horᴾ-loop }

  ------------------------------------------------------------------------------
  -- Total Hoare triple on plus ◁ ∇ (3 , 4)

  horᵀ-plus◁3,4 :  ⊤'  ⊢[ ι ]⟨ plus◁3,4 ⟩ᵀ[ i ] λ n →  ⌜ n ≡ 7 ⌝
  horᵀ-plus◁3,4 =  hor-[] $ hor-val $ ⌜⌝-intro refl

  ------------------------------------------------------------------------------
  -- Total Hoare triple on decrloop θ, ensuring termination by induction over n

  horᵀ-decrloop :  θ ↦ (-, n)  ⊢[ ι ]⟨ decrloop θ ⟩ᵀ[ i ] λ _ →  θ ↦ (-, 0)
  horᵀ-decrloop' :  θ ↦ (-, n)  ⊢[ ι ]⟨ decrloop' θ n ⟩ᵀ[ i ] λ _ →  θ ↦ (-, 0)

  horᵀ-decrloop =  ∗⊤-intro » hor-🞰 $ hor-[] $ ∗-elimˡ » horᵀ-decrloop'

  horᵀ-decrloop' {n = 0} =  hor-val ⊢-refl
  horᵀ-decrloop' {n = ṡ _} =
    ∗⊤-intro » hor-← $ hor-[] $ ∗-elimˡ » horᵀ-decrloop

  -- Total Hoare triple on nddecrloop, ensuring termination
  -- Notably, the number of reduction steps is dynamically determined

  horᵀ-nddecrloop :  θ ↦ ᵗv  ⊢[ ι ]⟨ nddecrloop θ ⟩ᵀ[ i ] λ _ →  θ ↦ (-, 0)
  horᵀ-nddecrloop =  hor-nd λ _ →
    ∗⊤-intro » hor-← $ ∗-elimˡ » hor-[] horᵀ-decrloop
