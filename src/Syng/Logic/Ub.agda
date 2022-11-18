--------------------------------------------------------------------------------
-- Proof rules on the upper bound
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syng.Logic.Ub where

open import Base.Func using (_$_)
open import Base.Nat using (ℕ)
open import Syng.Logic.Prop using (≤ᵁᵇ⟨_⟩_)
open import Syng.Logic.Core using (Pers; Pers-⇒□)

-- Import and re-export
open import Syng.Logic.Judg public using (≤ᵁᵇ-mono; ≤ᵁᵇ-⇒□; ≤ᵁᵇ-#ᵁᵇ; #ᵁᵇ-new;
  #ᵁᵇ-upd)

private variable
  n o :  ℕ

abstract

  -->  ≤ᵁᵇ-mono :  m ≤ n  →   ≤ᵁᵇ⟨ o ⟩ m  ⊢[ ι ]  ≤ᵁᵇ⟨ o ⟩ n

  -->  ≤ᵁᵇ-#ᵁᵇ :  ≤ᵁᵇ⟨ o ⟩ m  ∗  #ᵁᵇ⟨ o ⟩ n  ⊢[ ι ]  ⌜ n ≤ m ⌝

  -->  #ᵁᵇ-new :  ⊤'  ⊢[ ι ] ⤇  ∃ o , ≤ᵁᵇ⟨ o ⟩ n  ∗  #ᵁᵇ⟨ o ⟩ n

  -->  #ᵁᵇ-upd :  m ≤ n  →   #ᵁᵇ⟨ o ⟩ n  ⊢[ ι ] ⤇  ≤ᵁᵇ⟨ o ⟩ m  ∗  #ᵁᵇ⟨ o ⟩ m

  instance

    -- The upper bound token is persistent

    -->  ≤ᵁᵇ-⇒□ :  ≤ᵁᵇ⟨ o ⟩ n  ⊢[ ι ]  □ ≤ᵁᵇ⟨ o ⟩ n

    ≤ᵁᵇ-Pers :  Pers $ ≤ᵁᵇ⟨ o ⟩ n
    ≤ᵁᵇ-Pers .Pers-⇒□ =  ≤ᵁᵇ-⇒□
