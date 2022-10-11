--------------------------------------------------------------------------------
-- Example
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Example where

open import Base.Func using (_$_; it)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using ()
open import Base.Size using (Size; !)
open import Base.Prod using (_,_; -,_)
open import Base.Nat using (ℕ; ṡ_; _≤_; _⊔_; ≤-refl; ≤-trans; ⊔-introˡ; ⊔-comm)
open import Base.List using (List; []; _∷_)
open import Base.Seq using (Seq∞; _∷ˢ_; repˢ; rep²ˢ; takeˢ)
open import Syho.Lang.Expr using (Addr; TyVal; loop)
open import Syho.Lang.Example using (plus◁3,4; decrloop; decrloop'; nddecrloop;
  nddecrloop●-loop)
open import Syho.Logic.Prop using (Lft; Prop'; Prop∞; ¡ᴾ_; ∃-syntax; ⊤'; ⊥';
  ⌜_⌝∧_; ⌜_⌝; _∗_; □_; ○_; _↦_; _↦ˢ⟨_⟩_)
open import Syho.Logic.Core using (_⊢[_]_; Pers; ⊢-refl; _»_; ∃-intro; ∃-elim;
  ⊤-intro; ⌜⌝-intro; ∗-mono; ∗-monoʳ; ∗-comm; ∗-assocʳ; ?∗-comm; ∗-elimˡ;
  ∗-elimʳ; ∗⊤-intro; dup-Pers-∗; -∗-intro; □-mono; □-dup; ∃-Pers; □-elim;
  □-intro-Pers)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_; _ᵘ»ᵘ_; _ᵘ»_; ⇒⇛; ⇛-frameˡ)
open import Syho.Logic.Mem using (hor-🞰; hor-←)
open import Syho.Logic.Ind using (○-mono; □○-new-rec; ○-use)
open import Syho.Logic.Hor using (_⊢[_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ[_]_; _⊢[_][_]⟨_⟩∞;
  hor-val; hor-nd; hor-[]; ihor-[]●; hor-ihor-⁏-bind)
open import Syho.Logic.Bor using ()

private variable
  ι :  Size
  i k l m n :  ℕ
  θ θ' :  Addr
  ᵗv :  TyVal
  X :  Set₀
  P :  Prop∞
  Q˙ :  X → Prop∞
  α :  Lft
  nsˢ :  Seq∞ ℕ

-- □ ○ □ ○ □ ○ …

□○Loop :  Prop' ι
□○Loop =  □ ○ λ{ .! → □○Loop }

abstract

  ------------------------------------------------------------------------------
  -- Get □ ○ □ ○ □ ○ … for free

  □○Loop-new :  ⊤' ⊢[ ι ][ i ]⇛ □○Loop
  □○Loop-new =  -∗-intro (∗-elimˡ » □-dup) » □○-new-rec

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

  ------------------------------------------------------------------------------
  -- Infinite Hoare triple for nddecrloop●-loop

  ihor-nddecrloop●-loop :  θ ↦ ᵗv  ⊢[ ι ][ i ]⟨ nddecrloop●-loop θ ⟩∞
  ihor-nddecrloop●-loop =  hor-ihor-⁏-bind {e = nddecrloop _} {i = 0}
    horᵀ-nddecrloop λ _ → ihor-[]● λ{ .! → ihor-nddecrloop●-loop }

  ------------------------------------------------------------------------------
  -- Shared-borrowed singly-linked list

  -- Shared-borrowed singly-linked list over a list

  Slist :  List ℕ →  Lft →  Addr →  Prop∞
  Slist (n ∷ ns) α θ =  ∃ θ' , θ ↦ˢ⟨ α ⟩ (-, n , θ') ∗ Slist ns α θ'
  Slist [] _ _ =  ⊤'

  -- Shared-borrowed singly-linked list over a sequence
  -- We leverage here the coinductivity of the indirection modality ○,
  -- just like Iris's guarded recursion using the later modality ▷

  Slist∞ :  Seq∞ ℕ →  Lft →  Addr →  Prop' ι
  Slist∞ (n ∷ˢ nsˢ˂) α θ =
    ∃ θ' , θ ↦ˢ⟨ α ⟩ (-, n , θ') ∗ □ ○ λ{ .! → Slist∞ (nsˢ˂ .!) α θ' }

  -- Shared-borrowed singly-linked infinite list with a bound

  Slist∞≤ :  ℕ →  Lft →  Addr →  Prop' ι
  Slist∞≤ k α θ =  ∃ n , ∃ θ' , ⌜ n ≤ k ⌝∧
    θ ↦ˢ⟨ α ⟩ (-, n , θ') ∗ □ ○ λ{ .! → Slist∞≤ k α θ' }

  instance

    -- Slist∞ is persistent

    Slist∞-Pers :  Pers $ Slist∞ nsˢ α θ
    Slist∞-Pers {nsˢ = _ ∷ˢ _} =  ∃-Pers λ _ → it

  -- Turn Slist∞ nsˢ into Slist (takeˢ k nsˢ)
  -- This is under the super update ⇛, which is transitive,
  -- unlike the later modality ▷ in Iris

  Slist∞⇒Slist :  Slist∞ nsˢ α θ  ⊢[ ι ][ i ]⇛  Slist (takeˢ k nsˢ) α θ
  Slist∞⇒Slist {k = 0} =  ⇒⇛ ⊤-intro
  Slist∞⇒Slist {_ ∷ˢ _} {k = ṡ k'} =  ∃-elim λ θ' → ∗-monoʳ □-elim »
    ⇛-frameˡ (○-use ᵘ»ᵘ Slist∞⇒Slist {k = k'}) ᵘ» ∃-intro θ'

  -- Monotonicity of Slist∞≤

  Slist∞≤-mono :  k ≤ l  →   Slist∞≤ k α θ  ⊢[ ι ]  Slist∞≤ l α θ
  Slist∞≤-mono k≤l =  ∃-elim λ _ → ∃-elim λ _ → ∃-elim λ n≤k →
    ∗-monoʳ (□-mono $ ○-mono λ{ .! → Slist∞≤-mono k≤l }) »
    ∃-intro (≤-trans n≤k k≤l) » ∃-intro _ » ∃-intro _

  -- Turn a self-pointing pointer into Slist∞ (repˢ n)
  -- The key to this seemingly infinite construction is □○-new-rec

  Slist∞-repˢ-new :  θ ↦ˢ⟨ α ⟩ (-, n , θ)  ⊢[ ι ][ i ]⇛  Slist∞ (repˢ n) α θ
  Slist∞-repˢ-new =  -∗-intro (□-intro-Pers $ ∗-comm »
    ∗-monoʳ (□-mono $ ○-mono λ{ .! → ⊢-refl }) » ∃-intro _) »
    □○-new-rec {P˂ = ¡ᴾ _} ᵘ»ᵘ □-elim » ○-use

  -- Turn two mutually pointing pointers into Slist∞ (rep²ˢ - -) for both sides
  -- using □○-new-rec

  Slist∞-rep²ˢ-new :
    θ ↦ˢ⟨ α ⟩ (-, m , θ')  ∗  θ' ↦ˢ⟨ α ⟩ (-, n , θ)  ⊢[ ι ][ i ]⇛
      Slist∞ (rep²ˢ m n) α θ  ∗  Slist∞ (rep²ˢ n m) α θ'
  Slist∞-rep²ˢ-new =  -∗-intro (□-intro-Pers $ dup-Pers-∗ »
    ∗-monoʳ ?∗-comm » ∗-assocʳ » ∗-mono
    (∗-comm » ∗-monoʳ (□-mono $ ○-mono λ{ .! → ∗-elimʳ }) » ∃-intro _)
    (∗-comm » ∗-monoʳ (□-mono $ ○-mono λ{ .! → ∗-elimˡ }) » ∃-intro _)) »
    □○-new-rec {P˂ = ¡ᴾ _} ᵘ»ᵘ □-elim » ○-use

  -- Slist∞ (repˢ n) into Slist∞≤ n

  Slist∞-repˢ⇒Slist∞≤ :  Slist∞ (repˢ n) α θ  ⊢[ ι ]  Slist∞≤ n α θ
  Slist∞-repˢ⇒Slist∞≤ =  ∃-elim λ _ →
    ∗-monoʳ (□-mono $ ○-mono λ{ .! → Slist∞-repˢ⇒Slist∞≤ }) »
    ∃-intro ≤-refl » ∃-intro _ » ∃-intro _

  -- Slist∞ (rep²ˢ m n) into Slist∞≤ (m ⊔ n)

  Slist∞-rep²ˢ⇒Slist∞≤ :  Slist∞ (rep²ˢ m n) α θ  ⊢[ ι ]  Slist∞≤ (m ⊔ n) α θ
  Slist∞-rep²ˢ⇒Slist∞≤ =  ∃-elim λ _ → ∗-monoʳ (□-mono $ ○-mono λ{ .! → go }) »
    ∃-intro ⊔-introˡ » ∃-intro _ » ∃-intro _
   where
    go :  Slist∞ (rep²ˢ n m) α θ  ⊢[ ι ]  Slist∞≤ (m ⊔ n) α θ
    go {n} {m}  rewrite ⊔-comm {m} {n} =  Slist∞-rep²ˢ⇒Slist∞≤
