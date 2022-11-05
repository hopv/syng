--------------------------------------------------------------------------------
-- Example
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Symp.Logic.Example where

open import Base.Func using (_$_; it)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using ()
open import Base.Acc using (Acc; acc)
open import Base.Size using (𝕊; !)
open import Base.Prod using (_×_; _,_; -,_)
open import Base.Nat using (ℕ; ṡ_; _≤_; _<_; ṗ_; _+_; _⊔_; ≤-refl; ≤-trans;
  <-wf; ṗ-decr; ⊔-introˡ; ⊔-comm)
open import Base.List using (List; []; _∷_)
open import Base.Seq using (Seq∞; _∷ˢ_; hdˢ; tlˢ; repˢ; rep²ˢ; takeˢ)
open import Base.Sety using ()
open import Symp.Lang.Expr using (Addr; ◸_; _↷_; Expr˂∞; ∇_; 🞰_; Type; TyVal;
  loop)
open import Symp.Lang.Example using (plus◁3,4; decrep; decrep'; ndecrep;
  ndecrepev∞; fadᴿ; fad; fadrep; fadrep'; xfadrep; nxfadrep; cntr←)
open import Symp.Logic.Prop using (Name; strnm; SProp; SProp∞; SProp˂∞; ¡ᴾ_;
  ∀-syntax; ∃-syntax; ⊤'; ⊥'; ⌜_⌝∧_; ⌜_⌝; _∗_; □_; ○_; _↦_; _⊸[_]⇛_; _⊸⟨_⟩ᵀ[_]_;
  [^_]ᴺ; &ⁱ⟨_⟩_; static; _↦ⁱ_; #ᵁᵇ⟨_⟩_; ≤ᵁᵇ⟨_⟩_; ^ᶻᴺ-✔)
open import Symp.Logic.Core using (_⊢[_]_; Pers; ⊢-refl; _»_; ∀-intro; ∃-elim;
  ∀-elim; ∃-intro; ⊤-intro; retain-⌜⌝; ∗-mono; ∗-monoˡ; ∗-monoʳ; ∗-monoʳ²;
  ∗-comm; ∗-assocˡ; ∗-assocʳ; ?∗-comm; ∗-pullʳ²ˡ; ∗-pushʳ²ˡ; ∗-elimˡ; ∗-elimʳ;
  ⊤∗-intro; ∗⊤-intro; ∃∗-elim; ∗∃-elim; dup-Pers-∗; -∗-introˡ; -∗-introʳ;
  □-mono; ∃-Pers; □-elim; □-intro-Pers; dup-Pers)
open import Symp.Logic.Fupd using (_⊢[_][_]⇛_; ⤇⇒⇛; ⇒⇛; _ᵘ»ᵘ_; _ᵘ»_; ⇛-frameˡ;
  ⇛-frameʳ)
open import Symp.Logic.Hor using (_⊢[_][_]ᵃ⟨_⟩_; _⊢[_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ[_]_;
  _⊢[_][_]⟨_⟩∞; _ᵘ»ᵃʰ_; _ᵘ»ʰ_; _ᵃʰ»ᵘ_; ahor-frameˡ; ahor-frameʳ; ahor✔-hor;
  hor-valᵘ; hor-val; hor-val≡; hor-nd; hor-[]; ihor-[]●; hor-ihor-⁏-bind;
  hor-fork)
open import Symp.Logic.Heap using (ahor-fau; hor-🞰; hor-←)
open import Symp.Logic.Ind using (○-mono; ○-new; □○-new-Pers; □○-new-rec-Pers;
  ○-use; ○⇒⊸⇛; ⊸⇛-use; ○⇒⊸⟨⟩; ⊸⟨⟩ᵀ-use)
open import Symp.Logic.Inv using (&ⁱ-new; &ⁱ-open; ⅋ⁱ-close; hor-↦ⁱ-🞰)
open import Symp.Logic.Ub using (≤ᵁᵇ-#ᵁᵇ; #ᵁᵇ-new; #ᵁᵇ-upd)

private variable
  ι :  𝕊
  i j k l m m' n o :  ℕ
  nm :  Name
  θ θ' θᶜ :  Addr
  ᵗv :  TyVal
  X :  Set₀
  P :  SProp∞
  P˂ :  SProp˂∞
  Q˙ :  X → SProp∞
  T :  Type
  e˂˙ :  X → Expr˂∞ T
  ns : List ℕ
  nsˢ :  Seq∞ ℕ

-- □ ○ □ ○ □ ○ …

□○∞ :  SProp ι
□○∞ =  □ ○ λ{ .! → □○∞ }

abstract

  ------------------------------------------------------------------------------
  -- Get □○∞ for free

  □○∞-new :  ⊤' ⊢[ ι ][ i ]⇛ □○∞
  □○∞-new =  -∗-introˡ ∗-elimˡ » □○-new-rec-Pers

  ------------------------------------------------------------------------------
  -- Abstract &ⁱ by ⊸⇛

  &ⁱ-⊸⇛ :  &ⁱ⟨ nm ⟩ P˂  ⊢[ ι ][ i ]⇛
             □ (¡ᴾ [^ nm ]ᴺ  ⊸[ 0 ]⇛  ¡ᴾ (P˂ .!  ∗  (P˂ ⊸[ 0 ]⇛ ¡ᴾ [^ nm ]ᴺ)))
  &ⁱ-⊸⇛ =  □○-new-Pers {P˂ = ¡ᴾ _} ᵘ» □-mono $ ○⇒⊸⇛ λ{ .! → ∗-comm »
    &ⁱ-open ᵘ»ᵘ ⇛-frameʳ $ ○-new {P˂ = ¡ᴾ _} ᵘ» ○⇒⊸⇛ λ{ .! → ⅋ⁱ-close } }

  ------------------------------------------------------------------------------
  -- Get any partial Hoare triple for loop
  -- This uses coinduction by thunk for the infinite execution of loop

  horᴾ-loop :  P ⊢[ ι ]⟨ loop ⟩ᴾ Q˙
  horᴾ-loop =  hor-[] λ{ .! → horᴾ-loop }

  ------------------------------------------------------------------------------
  -- Total Hoare triple for plus ◁ ∇ (3 , 4)

  horᵀ-plus◁3,4 :  ⊤'  ⊢[ ι ]⟨ plus◁3,4 ⟩ᵀ[ i ] λ n →  ⌜ n ≡ 7 ⌝
  horᵀ-plus◁3,4 =  hor-[] hor-val≡

  ------------------------------------------------------------------------------
  -- Sequential decrement loop: Example for the total Hoare triple

  -- Total Hoare triple for decrep

  -- The proof guarantees termination by induction on n
  -- Notably, we take advantage of Agda's termination checker here

  horᵀ-decrep :  θ ↦ (-, n)  ⊢[ ι ]⟨ decrep θ ⟩ᵀ[ i ] λ _ →  θ ↦ (-, 0)
  horᵀ-decrep' :  θ ↦ (-, n)  ⊢[ ι ]⟨ decrep' θ n ⟩ᵀ[ i ] λ _ →  θ ↦ (-, 0)

  horᵀ-decrep =  ∗⊤-intro » hor-🞰 $ hor-[] $ ∗-elimˡ » horᵀ-decrep'

  horᵀ-decrep' {n = 0} =  hor-val ⊢-refl
  horᵀ-decrep' {n = ṡ _} =  ∗⊤-intro » hor-← $ hor-[] $ ∗-elimˡ » horᵀ-decrep

  -- Total Hoare triple for ndecrep, ensuring termination

  -- Notably, the number of reduction steps is dynamically determined
  -- Still, the proof here is totally natural; in particular, we don't need to
  -- craft a bound by an ordinal number, unlike Transfinite Iris

  horᵀ-ndecrep :  θ ↦ ᵗv  ⊢[ ι ]⟨ ndecrep θ ⟩ᵀ[ i ] λ _ →  θ ↦ (-, 0)
  horᵀ-ndecrep =  hor-nd λ _ → ∗⊤-intro » hor-← $ ∗-elimˡ » hor-[] horᵀ-decrep

  ------------------------------------------------------------------------------
  -- Infinite Hoare triple, for ndecrepev∞

  ihor-ndecrepev∞ :  θ ↦ ᵗv  ⊢[ ι ][ i ]⟨ ndecrepev∞ θ ⟩∞
  ihor-ndecrepev∞ =  hor-ihor-⁏-bind {e = ndecrep _} {i = 0}
    horᵀ-ndecrep λ _ → ihor-[]● λ{ .! → ihor-ndecrepev∞ }

  ------------------------------------------------------------------------------
  -- Concurrent decrement loop: Example for the total Hoare triple, the
  --                            impredicative invariant, and the upper bound

  -- &ub↦ :  Invariant that contains a full points-to token θ ↦ (-, n) for some
  --         number n under an upper-boundee token #ᵁᵇ⟨ i ⟩ n
  --         When we have &ub↦ θ i, any threads can freely decrease the value at
  --         θ, but never increase it

  ub :  Name
  ub =  strnm "ub"

  &ub↦ :  Addr →  ℕ →  SProp∞
  &ub↦ θ o =  &ⁱ⟨ ub ⟩ ¡ᴾ (∃ n , #ᵁᵇ⟨ o ⟩ n ∗ θ ↦ (-, n))

  -- Create ≤ᵁᵇ⟨ o ⟩ n and &ub↦ θ o out of θ ↦ (-, n)

  &ub↦-new :  θ ↦ (-, n)  ⊢[ ι ][ i ]⇛  ∃ o ,  ≤ᵁᵇ⟨ o ⟩ n  ∗  &ub↦ θ o
  &ub↦-new =  ⊤∗-intro » ⇛-frameˡ (#ᵁᵇ-new » ⤇⇒⇛) ᵘ»ᵘ ∃∗-elim λ o →
    ∗-assocʳ » ∗-monoʳ (∃-intro _) » ⇛-frameʳ &ⁱ-new ᵘ» ∃-intro o

  -- Atomic Hoare triple for fad under #ᵁᵇ and ↦, updating ≤ᵁᵇ

  ahor-fad-#ᵁᵇ-↦ :
    ≤ᵁᵇ⟨ o ⟩ n  ∗  #ᵁᵇ⟨ o ⟩ m' ∗ θ ↦ (-, m')  ⊢[ ι ][ i ]ᵃ⟨ fadᴿ θ ⟩ λ m →
      ⌜ m ≤ n ⌝∧  ≤ᵁᵇ⟨ o ⟩ ṗ m  ∗  #ᵁᵇ⟨ o ⟩ ṗ m  ∗ θ ↦ (-, ṗ m)
  ahor-fad-#ᵁᵇ-↦ =  ∗-assocˡ » ∗-monoˡ (retain-⌜⌝ ≤ᵁᵇ-#ᵁᵇ) » ∃∗-elim λ m≤n →
    ∗-monoˡ ∗-elimʳ » ahor-frameʳ ahor-fau ᵃʰ»ᵘ λ m → ∗∃-elim λ{ refl →
    ⇛-frameˡ {i = 0} (#ᵁᵇ-upd ṗ-decr » ⤇⇒⇛) ᵘ» ∗-assocʳ » ∃-intro m≤n }

  -- Atomic Hoare triple for fad under &ub↦, updating ≤ᵁᵇ

  ahor-fad-&ub↦ :
    [^ ub ]ᴺ  ∗  ≤ᵁᵇ⟨ o ⟩ n  ∗  &ub↦ θ o  ⊢[ ι ][ i ]ᵃ⟨ fadᴿ θ ⟩ λ m →
      [^ ub ]ᴺ  ∗  (⌜ m ≤ n ⌝∧  ≤ᵁᵇ⟨ o ⟩ ṗ m  ∗  &ub↦ θ o)
  ahor-fad-&ub↦ =  ∗-monoʳ² dup-Pers » ∗-pushʳ²ˡ » ∗-pushʳ²ˡ » ∗-assocˡ »
    ⇛-frameˡ {i = 0} &ⁱ-open ᵘ»ᵃʰ ∗-assocʳ » ∗-pullʳ²ˡ » ∗-assocˡ »
    ahor-frameˡ (∗∃-elim λ _ → ahor-fad-#ᵁᵇ-↦) ᵃʰ»ᵘ λ m → ∃∗-elim λ m≤n →
    ∗-assocʳ » ∗-pushʳ²ˡ » ∗-monoˡ (∃-intro _) » ∗-assocˡ »
    ⇛-frameˡ {i = 0} ⅋ⁱ-close ᵘ» ∗-monoʳ $ ∃-intro m≤n

  -- Total Hoare triple for fadrep under ≤ᵁᵇ and &ub↦
  -- The proof goes by well-founded induction on the upper bound n

  horᵀ-fadrep-&ub↦-Acc :  Acc _<_ n  →
    ≤ᵁᵇ⟨ o ⟩ n  ∗  &ub↦ θ o  ⊢[ ι ]⟨ fadrep θ ⟩ᵀ[ i ] λ _ →  ⊤'
  horᵀ-fadrep'-&ub↦-Acc :  Acc _<_ n  →   m ≤ n  →
    ≤ᵁᵇ⟨ o ⟩ ṗ m  ∗  &ub↦ θ o  ⊢[ ι ]⟨ fadrep' θ m ⟩ᵀ[ i ] λ _ →  ⊤'

  horᵀ-fadrep-&ub↦-Acc Accn =  ahor✔-hor {i = 0} ^ᶻᴺ-✔ ahor-fad-&ub↦ λ m →
    ∃-elim λ m≤n → hor-[] $ horᵀ-fadrep'-&ub↦-Acc Accn m≤n
  horᵀ-fadrep'-&ub↦-Acc {m = 0} _ _ =  hor-val ⊤-intro
  horᵀ-fadrep'-&ub↦-Acc {m = ṡ _} (acc <n⇒acc) m'<n =
    horᵀ-fadrep-&ub↦-Acc (<n⇒acc m'<n)

  horᵀ-fadrep-&ub↦ :
    ≤ᵁᵇ⟨ o ⟩ n  ∗  &ub↦ θ o  ⊢[ ι ]⟨ fadrep θ ⟩ᵀ[ i ] λ _ →  ⊤'
  horᵀ-fadrep-&ub↦ =  horᵀ-fadrep-&ub↦-Acc <-wf

  -- Total Hoare triple for xfadrep θ k, which forks k threads that perform
  -- fadrep θ

  horᵀ-xfadrep-&ub↦ :
    ≤ᵁᵇ⟨ o ⟩ n  ∗  &ub↦ θ o  ⊢[ ι ]⟨ xfadrep θ k ⟩ᵀ[ i ] λ _ →  ⊤'
  horᵀ-xfadrep-&ub↦ {k = 0} =  hor-val ⊤-intro
  horᵀ-xfadrep-&ub↦ {k = ṡ _} =  dup-Pers »
    hor-fork horᵀ-fadrep-&ub↦ $ hor-[] horᵀ-xfadrep-&ub↦

  horᵀ-xfadrep :  θ ↦ (-, n)  ⊢[ ι ]⟨ xfadrep θ k ⟩ᵀ[ i ] λ _ →  ⊤'
  horᵀ-xfadrep =  &ub↦-new {i = 0} ᵘ»ʰ ∃-elim λ _ → horᵀ-xfadrep-&ub↦

  -- Total Hoare triple for nxfadrep

  -- Notably, the number of threads and the number of iterations of each thread
  -- are dynamically determined; still the proof here is totally natural

  horᵀ-nxfadrep :  θ ↦ ᵗv  ⊢[ ι ]⟨ nxfadrep θ ⟩ᵀ[ i ] λ _ →  ⊤'
  horᵀ-nxfadrep =  hor-nd λ _ → ∗⊤-intro » hor-← $ hor-[] $ ∗-elimˡ »
    hor-nd λ _ → hor-[] horᵀ-xfadrep

  ------------------------------------------------------------------------------
  -- Counter: Example for the total Hoare triple precursor

  -- Specification for a counter e˂˙

  -- Thanks to the coinductivity of the total Hoare triple precursor ⊸⟨ ⟩ᵀ, we
  -- can construct the infinite proposition Cntr, which returns Cntr itself with
  -- an updated parameter k + n after executing the counter

  -- This amounts to construction of a recursive type over a function type
  -- Notably, this spec just states about the observable behaviors and abstracts
  -- the internal state of the function

  Cntr :  (ℕ → Expr˂∞ (◸ ℕ)) →  ℕ →  SProp ι
  Cntr e˂˙ n =  ∀' k ,
    ¡ᴾ ⊤' ⊸⟨ e˂˙ k .! ⟩ᵀ[ 0 ] λ{ m .! → ⌜ m ≡ n ⌝∧ Cntr e˂˙ (k + n) }

  -- Use Cntr e˂˙ to get a total Hoare triple for e˂˙
  -- The level of the total Hoare triple is 1, not 0

  Cntr-use :  Cntr e˂˙ n  ⊢[ ι ]⟨ e˂˙ k .! ⟩ᵀ[ 1 ] λ m →
                ⌜ m ≡ n ⌝∧ Cntr e˂˙ (k + n)
  Cntr-use =  ∀-elim _ » ⊤∗-intro » ⊸⟨⟩ᵀ-use

  -- Get Cntr (cntr← θ) n from a full points-to token θ ↦ (-, n)
  -- Thanks to the coinductivity of ○⇒⊸⟨⟩, we can successfully perform the
  -- infinite construction of Cntr

  cntr←-Cntr :  θ ↦ (-, n)  ⊢[ ι ][ i ]⇛  Cntr (cntr← θ) n
  cntr←-Cntr =  ○-new {P˂ = ¡ᴾ _} ᵘ» ∀-intro λ _ → ○⇒⊸⟨⟩ λ{ .! →
    ∗-comm » hor-🞰 $ hor-[] $ hor-← $ hor-[] $ hor-valᵘ {i = 0} $
    ∗-elimˡ » cntr←-Cntr ᵘ» ∃-intro refl }

  ------------------------------------------------------------------------------
  -- Static singly-linked list: Example for the indirection modality ○

  -- Static singly-linked list over a list

  Slist :  List ℕ →  Addr →  SProp∞
  Slist (n ∷ ns) θ =  ∃ θ' , θ ↦ⁱ (-, n , θ') ∗ Slist ns θ'
  Slist [] _ =  ⊤'

  -- Static singly-linked list over a sequence
  -- We leverage here the coinductivity of the indirection modality ○,
  -- just like Iris's guarded recursion using the later modality ▷

  Slist∞ :  Seq∞ ℕ →  Addr →  SProp ι
  Slist∞ (n ∷ˢ nsˢ˂) θ =
    ∃ θ' , θ ↦ⁱ (-, n , θ') ∗ □ ○ λ{ .! → Slist∞ (nsˢ˂ .!) θ' }

  -- Static singly-linked infinite list with a bound
  -- Again, we leverage here the coinductivity of the indirection modality ○

  Slist∞≤ :  ℕ →  Addr →  SProp ι
  Slist∞≤ k θ =  ∃ n , ∃ θ' , ⌜ n ≤ k ⌝∧
    θ ↦ⁱ (-, n , θ') ∗ □ ○ λ{ .! → Slist∞≤ k θ' }

  -- Slist is persistent

  Slist-Pers :  Pers $ Slist ns θ
  Slist-Pers {[]} =  it
  Slist-Pers {_ ∷ ns'} =  let instance _ = Slist-Pers {ns'} in ∃-Pers λ _ → it

  instance

    -- Slist∞ is persistent

    Slist∞-Pers :  Pers $ Slist∞ nsˢ θ
    Slist∞-Pers {_ ∷ˢ _} =  ∃-Pers λ _ → it

    -- Slist∞≤ is persistent

    Slist∞≤-Pers :  Pers $ Slist∞≤ n θ
    Slist∞≤-Pers =  ∃-Pers λ _ → ∃-Pers λ _ → ∃-Pers λ _ → it

  -- Monotonicity of Slist∞≤
  -- Thanks to the coinductivity of ○-mono, we can get a pure sequent for the
  -- infinite proposition Slist∞≤

  Slist∞≤-mono :  k ≤ l  →   Slist∞≤ k θ  ⊢[ ι ]  Slist∞≤ l θ
  Slist∞≤-mono k≤l =  ∃-elim λ _ → ∃-elim λ _ → ∃-elim λ n≤k →
    ∗-monoʳ (□-mono $ ○-mono λ{ .! → Slist∞≤-mono k≤l }) »
    ∃-intro (≤-trans n≤k k≤l) » ∃-intro _ » ∃-intro _

  -- Slist∞ (repˢ n) into Slist∞≤ n
  -- Thanks to the coinductivity of ○-mono, we can get a pure sequent for the
  -- infinite propositions Slist∞ and Slist∞≤

  Slist∞-repˢ⇒Slist∞≤ :  Slist∞ (repˢ n) θ  ⊢[ ι ]  Slist∞≤ n θ
  Slist∞-repˢ⇒Slist∞≤ =  ∃-elim λ _ →
    ∗-monoʳ (□-mono $ ○-mono λ{ .! → Slist∞-repˢ⇒Slist∞≤ }) »
    ∃-intro ≤-refl » ∃-intro _ » ∃-intro _

  -- Slist∞ (rep²ˢ m n) into Slist∞≤ (m ⊔ n)
  -- Again, the coinductivity of ○-mono is the key

  Slist∞-rep²ˢ⇒Slist∞≤ :  Slist∞ (rep²ˢ m n) θ  ⊢[ ι ]  Slist∞≤ (m ⊔ n) θ
  Slist∞-rep²ˢ⇒Slist∞≤ =  ∃-elim λ _ → ∗-monoʳ (□-mono $ ○-mono λ{ .! → go }) »
    ∃-intro ⊔-introˡ » ∃-intro _ » ∃-intro _
   where
    go :  Slist∞ (rep²ˢ n m) θ  ⊢[ ι ]  Slist∞≤ (m ⊔ n) θ
    go {n} {m}  rewrite ⊔-comm {m} {n} =  Slist∞-rep²ˢ⇒Slist∞≤

  -- Turn Slist∞ nsˢ into Slist (takeˢ k nsˢ)
  -- This is under the fancy update ⇛, which is transitive,
  -- unlike the later modality ▷ in Iris

  Slist∞⇒Slist :  Slist∞ nsˢ θ  ⊢[ ι ][ i ]⇛  Slist (takeˢ k nsˢ) θ
  Slist∞⇒Slist {k = 0} =  ⇒⇛ ⊤-intro
  Slist∞⇒Slist {_ ∷ˢ _} {k = ṡ k'} =  ∃-elim λ θ' → ∗-monoʳ □-elim »
    ⇛-frameʳ (○-use ᵘ»ᵘ Slist∞⇒Slist {k = k'}) ᵘ» ∃-intro θ'

  -- Use Slist∞

  Slist∞-use :  Slist∞ nsˢ θ  ⊢[ ι ]⟨ 🞰_ {T = ◸ _} (∇ θ) ⟩ᵀ[ i ] λ (m , θ') →
                  ⌜ m ≡ hdˢ nsˢ ⌝∧ Slist∞ (tlˢ nsˢ .!) θ'
  Slist∞-use {_ ∷ˢ _} =  ∃-elim λ _ → hor-↦ⁱ-🞰 $ hor-valᵘ {i = 0} $
    □-elim » ○-use ᵘ» ∃-intro refl

  -- Turn a self-pointing pointer into Slist∞ (repˢ n)
  -- The key to this seemingly infinite construction is □○-new-rec

  Slist∞-repˢ-new :  θ ↦ⁱ (-, n , θ)  ⊢[ ι ][ i ]⇛  Slist∞ (repˢ n) θ
  Slist∞-repˢ-new =
    -∗-introʳ (∗-monoʳ (□-mono $ ○-mono λ{ .! → ⊢-refl }) » ∃-intro _) »
    □○-new-rec-Pers {P˂ = ¡ᴾ _} ᵘ»ᵘ □-elim » ○-use

  -- Turn two mutually pointing pointers into Slist∞ (rep²ˢ - -) for both sides
  -- using □○-new-rec

  Slist∞-rep²ˢ-new :  θ ↦ⁱ (-, m , θ')  ∗  θ' ↦ⁱ (-, n , θ)  ⊢[ ι ][ i ]⇛
                        Slist∞ (rep²ˢ m n) θ  ∗  Slist∞ (rep²ˢ n m) θ'
  Slist∞-rep²ˢ-new =  -∗-introˡ (dup-Pers-∗ » ∗-monoʳ ?∗-comm » ∗-assocˡ »
    ∗-mono (∗-comm » ∗-monoʳ (□-mono $ ○-mono λ{ .! → ∗-elimʳ }) » ∃-intro _)
           (∗-comm » ∗-monoʳ (□-mono $ ○-mono λ{ .! → ∗-elimˡ }) » ∃-intro _)) »
    □○-new-rec-Pers {P˂ = ¡ᴾ _} ᵘ»ᵘ □-elim » ○-use
