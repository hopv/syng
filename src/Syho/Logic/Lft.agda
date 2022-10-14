--------------------------------------------------------------------------------
-- Proof rules on the lifetime
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Lft where

open import Base.Func using (_$_)
open import Syho.Logic.Prop using (Lft; †ᴸ_)
open import Syho.Logic.Core using (Pers; Pers-⇒□)

-- Import and re-export
open import Syho.Logic.Judg public using ([]ᴸ⟨⟩-resp; []ᴸ⟨⟩-merge; []ᴸ⟨⟩-split;
  []ᴸ⟨⟩-≤1; †ᴸ-⇒□; []ᴸ⟨⟩-†ᴸ-no; []ᴸ-new)

private variable
  α :  Lft

abstract

  ------------------------------------------------------------------------------
  -- On the lifetime

  -->  []ᴸ⟨⟩-resp :  p ≈ᴿ⁺ q  →   [ α ]ᴸ⟨ p ⟩  ⊢[ ι ]  [ α ]ᴸ⟨ q ⟩

  -->  []ᴸ⟨⟩-merge :  [ α ]ᴸ⟨ p ⟩  ∗  [ α ]ᴸ⟨ q ⟩  ⊢[ ι ]  [ α ]ᴸ⟨ p +ᴿ⁺ q ⟩

  -->  []ᴸ⟨⟩-split :  [ α ]ᴸ⟨ p +ᴿ⁺ q ⟩  ⊢[ ι ]  [ α ]ᴸ⟨ p ⟩  ∗  [ α ]ᴸ⟨ q ⟩

  -->  []ᴸ⟨⟩-≤1 :  [ α ]ᴸ⟨ p ⟩  ⊢[ ι ]  ⌜ p ≤1ᴿ⁺ ⌝

  -->  []ᴸ⟨⟩-†ᴸ-no :  [ α ]ᴸ⟨ p ⟩  ∗  †ᴸ α  ⊢[ ι ]  ⊥'

  -->  []ᴸ-new :  ⊤'  ⊢[ ι ] ⤇  ∃ α , [ α ]ᴸ

  instance

    -- The dead lifetime token is persistent

    -->  †ᴸ-⇒□ :  †ᴸ α  ⊢[ ι ]  □ †ᴸ α

    †ᴸ-Pers :  Pers $ †ᴸ α
    †ᴸ-Pers .Pers-⇒□ =  †ᴸ-⇒□
