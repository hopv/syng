--------------------------------------------------------------------------------
-- Example
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Example where

open import Base.Func using (_$_; it)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using ()
open import Base.Size using (Size; !)
open import Base.Prod using (_×_; _,_; -,_)
open import Base.Nat using (ℕ; ṡ_; _≤_; _+_; _⊔_; ≤-refl; ≤-trans; ⊔-introˡ;
  ⊔-comm)
open import Base.List using (List; []; _∷_)
open import Base.RatPos using (ℚ⁺)
open import Base.Seq using (Seq∞; _∷ˢ_; hdˢ; tlˢ; repˢ; rep²ˢ; takeˢ)
open import Base.Sety using ()
open import Syho.Lang.Expr using (Addr; ◸_; _↷_; Expr˂∞; ∇_; 🞰_; TyVal; loop)
open import Syho.Lang.Example using (plus◁3,4; decrep; decrep'; ndecrep;
  ndecrep●∞; cntr←)
open import Syho.Logic.Prop using (Lft; Prop'; Prop∞; ¡ᴾ_; ∀-syntax; ∃-syntax;
  ⊤'; ⊥'; ⌜_⌝∧_; ⌜_⌝; _∗_; □_; ○_; _↦_; _↪⟨_⟩ᵀ[_]_; [_]ᴸ⟨_⟩; _↦ˢ⟨_⟩_)
open import Syho.Logic.Core using (_⊢[_]_; Pers; ⊢-refl; _»_; ∀-intro; ∃-elim;
  ∀-elim; ∃-intro; ⊤-intro; ⌜⌝-intro; ∗-mono; ∗-monoʳ; ∗-comm; ∗-assocˡ;
  ∗-assocʳ; ?∗-comm; ∗?-comm; ∗-elimˡ; ∗-elimʳ; ⊤∗-intro; ∗⊤-intro; ∃∗-elim;
  dup-Pers-∗; -∗-introˡ; -∗-introʳ; □-mono; □-dup; ∃-Pers; □-elim; □-intro-Pers)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_; _ᵘ»ᵘ_; _ᵘ»_; ⇒⇛; ⇛-frameˡ;
  ⇛-frameʳ)
open import Syho.Logic.Hor using (_⊢[_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ[_]_; _⊢[_][_]⟨_⟩∞;
  hor-valᵘ; hor-val; hor-nd; hor-[]; ihor-[]●; hor-ihor-⁏-bind)
open import Syho.Logic.Mem using (hor-🞰; hor-←)
open import Syho.Logic.Ind using (○-mono; ○-new; □○-new-rec; ○-use; ○⇒↪⟨⟩;
  ↪⟨⟩ᵀ-use)
open import Syho.Logic.Bor using (hor-↦ˢ-🞰)

private variable
  ι :  Size
  i k l m n :  ℕ
  θ θ' θᶜ :  Addr
  ᵗv :  TyVal
  X :  Set₀
  P :  Prop∞
  Q˙ :  X → Prop∞
  c :  ℕ → Expr˂∞ $ ◸ ℕ
  α :  Lft
  p :  ℚ⁺
  ns : List ℕ
  nsˢ :  Seq∞ ℕ

-- □ ○ □ ○ □ ○ …

□○∞ :  Prop' ι
□○∞ =  □ ○ λ{ .! → □○∞ }

abstract

  ------------------------------------------------------------------------------
  -- Get □○∞ for free

  □○∞-new :  ⊤' ⊢[ ι ][ i ]⇛ □○∞
  □○∞-new =  -∗-introˡ (∗-elimˡ » □-dup) » □○-new-rec

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
  -- Total Hoare triple on decrep θ, ensuring termination by induction over n

  horᵀ-decrep :  θ ↦ (-, n)  ⊢[ ι ]⟨ decrep θ ⟩ᵀ[ i ] λ _ →  θ ↦ (-, 0)
  horᵀ-decrep' :  θ ↦ (-, n)  ⊢[ ι ]⟨ decrep' θ n ⟩ᵀ[ i ] λ _ →  θ ↦ (-, 0)

  horᵀ-decrep =  ∗⊤-intro » hor-🞰 $ hor-[] $ ∗-elimˡ » horᵀ-decrep'

  horᵀ-decrep' {n = 0} =  hor-val ⊢-refl
  horᵀ-decrep' {n = ṡ _} =  ∗⊤-intro » hor-← $ hor-[] $ ∗-elimˡ » horᵀ-decrep

  -- Total Hoare triple on ndecrep, ensuring termination
  -- Notably, the number of reduction steps is dynamically determined

  horᵀ-ndecrep :  θ ↦ ᵗv  ⊢[ ι ]⟨ ndecrep θ ⟩ᵀ[ i ] λ _ →  θ ↦ (-, 0)
  horᵀ-ndecrep =  hor-nd λ _ → ∗⊤-intro » hor-← $ ∗-elimˡ » hor-[] horᵀ-decrep

  ------------------------------------------------------------------------------
  -- Infinite Hoare triple for ndecrep●∞

  ihor-ndecrep●∞ :  θ ↦ ᵗv  ⊢[ ι ][ i ]⟨ ndecrep●∞ θ ⟩∞
  ihor-ndecrep●∞ =  hor-ihor-⁏-bind {e = ndecrep _} {i = 0}
    horᵀ-ndecrep λ _ → ihor-[]● λ{ .! → ihor-ndecrep●∞ }

  ------------------------------------------------------------------------------
  -- Cntr

  -- Specification for a counter
  -- Thanks to the coinductivity of ↪⟨ ⟩ᵀ, we can construct here an infinite
  -- proposition, where Cntr c itself is returned after executing the counter c
  -- This amounts to construction of a recursive type over a function type
  -- Notably, this spec just states about the observable behaviors and abstracts
  -- the internal state of the function

  Cntr :  (ℕ → Expr˂∞ (◸ ℕ)) →  ℕ →  Prop' ι
  Cntr c n =  ∀' k ,
    ¡ᴾ ⊤' ↪⟨ c k .! ⟩ᵀ[ 0 ] λ{ m .! → ⌜ m ≡ n ⌝∧ Cntr c (k + n) }

  -- Use Cntr c to get a total Hoare triple on c
  -- The level of the total Hoare triple is 1, not 0

  Cntr-use :  Cntr c n  ⊢[ ι ]⟨ c k .! ⟩ᵀ[ 1 ] λ m →  ⌜ m ≡ n ⌝∧ Cntr c (k + n)
  Cntr-use =  ∀-elim _ » ⊤∗-intro » ↪⟨⟩ᵀ-use

  -- Get Cntr (cntr← θ) n from a full points-to token θ ↦ (-, n)
  -- Thanks to the coinductivity of ○⇒↪⟨⟩, we can successfully perform the
  -- infinite construction of Cntr

  cntr←-Cntr :  θ ↦ (-, n)  ⊢[ ι ][ i ]⇛  Cntr (cntr← θ) n
  cntr←-Cntr =  ○-new {P˂ = ¡ᴾ _} ᵘ» ∀-intro λ _ → ○⇒↪⟨⟩ λ{ .! →
    ∗-comm » hor-🞰 $ hor-[] $ hor-← $ hor-[] $ hor-valᵘ {i = 0} $
    ∗-elimˡ » cntr←-Cntr ᵘ» ∃-intro refl }

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
  -- Again, we leverage here the coinductivity of the indirection modality ○

  Slist∞≤ :  ℕ →  Lft →  Addr →  Prop' ι
  Slist∞≤ k α θ =  ∃ n , ∃ θ' , ⌜ n ≤ k ⌝∧
    θ ↦ˢ⟨ α ⟩ (-, n , θ') ∗ □ ○ λ{ .! → Slist∞≤ k α θ' }

  -- Slist is persistent

  Slist-Pers :  Pers $ Slist ns α θ
  Slist-Pers {[]} =  it
  Slist-Pers {_ ∷ ns'} =  let instance _ = Slist-Pers {ns'} in ∃-Pers λ _ → it

  instance

    -- Slist∞ is persistent

    Slist∞-Pers :  Pers $ Slist∞ nsˢ α θ
    Slist∞-Pers {_ ∷ˢ _} =  ∃-Pers λ _ → it

    -- Slist∞≤ is persistent

    Slist∞≤-Pers :  Pers $ Slist∞≤ n α θ
    Slist∞≤-Pers =  ∃-Pers λ _ → ∃-Pers λ _ → ∃-Pers λ _ → it

  -- Monotonicity of Slist∞≤
  -- Thanks to the coinductivity of ○-mono, we can get a pure sequent for the
  -- infinite proposition Slist∞≤

  Slist∞≤-mono :  k ≤ l  →   Slist∞≤ k α θ  ⊢[ ι ]  Slist∞≤ l α θ
  Slist∞≤-mono k≤l =  ∃-elim λ _ → ∃-elim λ _ → ∃-elim λ n≤k →
    ∗-monoʳ (□-mono $ ○-mono λ{ .! → Slist∞≤-mono k≤l }) »
    ∃-intro (≤-trans n≤k k≤l) » ∃-intro _ » ∃-intro _

  -- Slist∞ (repˢ n) into Slist∞≤ n
  -- Thanks to the coinductivity of ○-mono, we can get a pure sequent for the
  -- infinite propositions Slist∞ and Slist∞≤

  Slist∞-repˢ⇒Slist∞≤ :  Slist∞ (repˢ n) α θ  ⊢[ ι ]  Slist∞≤ n α θ
  Slist∞-repˢ⇒Slist∞≤ =  ∃-elim λ _ →
    ∗-monoʳ (□-mono $ ○-mono λ{ .! → Slist∞-repˢ⇒Slist∞≤ }) »
    ∃-intro ≤-refl » ∃-intro _ » ∃-intro _

  -- Slist∞ (rep²ˢ m n) into Slist∞≤ (m ⊔ n)
  -- Again, the coinductivity of ○-mono is the key

  Slist∞-rep²ˢ⇒Slist∞≤ :  Slist∞ (rep²ˢ m n) α θ  ⊢[ ι ]  Slist∞≤ (m ⊔ n) α θ
  Slist∞-rep²ˢ⇒Slist∞≤ =  ∃-elim λ _ → ∗-monoʳ (□-mono $ ○-mono λ{ .! → go }) »
    ∃-intro ⊔-introˡ » ∃-intro _ » ∃-intro _
   where
    go :  Slist∞ (rep²ˢ n m) α θ  ⊢[ ι ]  Slist∞≤ (m ⊔ n) α θ
    go {n} {m}  rewrite ⊔-comm {m} {n} =  Slist∞-rep²ˢ⇒Slist∞≤

  -- Turn Slist∞ nsˢ into Slist (takeˢ k nsˢ)
  -- This is under the super update ⇛, which is transitive,
  -- unlike the later modality ▷ in Iris

  Slist∞⇒Slist :  Slist∞ nsˢ α θ  ⊢[ ι ][ i ]⇛  Slist (takeˢ k nsˢ) α θ
  Slist∞⇒Slist {k = 0} =  ⇒⇛ ⊤-intro
  Slist∞⇒Slist {_ ∷ˢ _} {k = ṡ k'} =  ∃-elim λ θ' → ∗-monoʳ □-elim »
    ⇛-frameˡ (○-use ᵘ»ᵘ Slist∞⇒Slist {k = k'}) ᵘ» ∃-intro θ'

  -- Use Slist∞

  Slist∞-use :
    Slist∞ nsˢ α θ  ∗  [ α ]ᴸ⟨ p ⟩  ⊢[ ι ]⟨ 🞰_ {T = ◸ _} (∇ θ) ⟩ᵀ[ i ]
      λ (m , θ') →  ⌜ m ≡ hdˢ nsˢ ⌝∧ Slist∞ (tlˢ nsˢ .!) α θ'  ∗  [ α ]ᴸ⟨ p ⟩
  Slist∞-use {_ ∷ˢ _} =  ∃∗-elim λ _ → ∗?-comm » ∗-assocˡ » hor-↦ˢ-🞰 $
    hor-valᵘ {i = 0} $ ∗-comm » ⇛-frameʳ (□-elim » ○-use) ᵘ» ∃-intro refl

  -- Turn a self-pointing pointer into Slist∞ (repˢ n)
  -- The key to this seemingly infinite construction is □○-new-rec

  Slist∞-repˢ-new :  θ ↦ˢ⟨ α ⟩ (-, n , θ)  ⊢[ ι ][ i ]⇛  Slist∞ (repˢ n) α θ
  Slist∞-repˢ-new =  -∗-introʳ (□-intro-Pers $
    ∗-monoʳ (□-mono $ ○-mono λ{ .! → ⊢-refl }) » ∃-intro _) »
    □○-new-rec {P˂ = ¡ᴾ _} ᵘ»ᵘ □-elim » ○-use

  -- Turn two mutually pointing pointers into Slist∞ (rep²ˢ - -) for both sides
  -- using □○-new-rec

  Slist∞-rep²ˢ-new :
    θ ↦ˢ⟨ α ⟩ (-, m , θ')  ∗  θ' ↦ˢ⟨ α ⟩ (-, n , θ)  ⊢[ ι ][ i ]⇛
      Slist∞ (rep²ˢ m n) α θ  ∗  Slist∞ (rep²ˢ n m) α θ'
  Slist∞-rep²ˢ-new =  -∗-introˡ (□-intro-Pers $ dup-Pers-∗ »
    ∗-monoʳ ?∗-comm » ∗-assocʳ » ∗-mono
    (∗-comm » ∗-monoʳ (□-mono $ ○-mono λ{ .! → ∗-elimʳ }) » ∃-intro _)
    (∗-comm » ∗-monoʳ (□-mono $ ○-mono λ{ .! → ∗-elimˡ }) » ∃-intro _)) »
    □○-new-rec {P˂ = ¡ᴾ _} ᵘ»ᵘ □-elim » ○-use
