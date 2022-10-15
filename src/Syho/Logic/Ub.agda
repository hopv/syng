--------------------------------------------------------------------------------
-- Proof rules on the upper bound
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Ub where

open import Base.Func using (_$_)
open import Base.Nat using (ℕ)
open import Syho.Logic.Prop using (≤ᵁᵇ⟨_⟩_)
open import Syho.Logic.Core using (Pers; Pers-⇒□)

-- Import and re-export
open import Syho.Logic.Judg public using (≤ᵁᵇ-mono; ≤ᵁᵇ-⇒□; ≤ᵁᵇ-#ᵁᵇ; #ᵁᵇ-new;
  #ᵁᵇ-upd)

private variable
  i n :  ℕ

abstract

  -->  ≤ᵁᵇ-mono :  m ≤ n  →   ≤ᵁᵇ⟨ i ⟩ m  ⊢[ ι ]  ≤ᵁᵇ⟨ i ⟩ n

  -->  ≤ᵁᵇ-#ᵁᵇ :  ≤ᵁᵇ⟨ i ⟩ m  ∗  #ᵁᵇ⟨ i ⟩ n  ⊢[ ι ]  ⌜ n ≤ m ⌝

  -->  #ᵁᵇ-new :  ⊤'  ⊢[ ι ] ⤇  ∃ i , ≤ᵁᵇ⟨ i ⟩ n  ∗  #ᵁᵇ⟨ i ⟩ n

  -->  #ᵁᵇ-upd :  m ≤ n  →   #ᵁᵇ⟨ i ⟩ n  ⊢[ ι ] ⤇  ≤ᵁᵇ⟨ i ⟩ m  ∗  #ᵁᵇ⟨ i ⟩ m

  instance

    -- The upper-bound token is persistent

    -->  ≤ᵁᵇ-⇒□ :  ≤ᵁᵇ⟨ i ⟩ n  ⊢[ ι ]  □ ≤ᵁᵇ⟨ i ⟩ n

    ≤ᵁᵇ-Pers :  Pers $ ≤ᵁᵇ⟨ i ⟩ n
    ≤ᵁᵇ-Pers .Pers-⇒□ =  ≤ᵁᵇ-⇒□
