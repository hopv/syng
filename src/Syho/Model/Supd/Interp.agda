--------------------------------------------------------------------------------
-- Interpret the super update
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Interp where

open import Base.Level using (Level; _⊔ᴸ_; 2ᴸ)
open import Base.Func using (_$_; _›_)
open import Base.Eq using (_≡_; refl)
open import Base.Size using (∞)
open import Base.Prod using (_,_)
open import Base.Dec using (upd˙²-self; upd˙²-2)
open import Base.Nat using ()
open import Syho.Lang.Reduce using (Mem)
open import Syho.Model.Prop.Base using (Propᵒ; _⊨_; ⤇ᵒ_; ⤇ᵒ-intro)
open import Syho.Model.Supd.Base using (⟨_⟩[_]⇛ᵍ'⟨_⟩_; ⇛ᵍ≡⇛ᵍ'; ⤇ᵒ⇒⇛ᵍ; ⇛ᵍ-join)
open import Syho.Model.Supd.Ind using (envᴵⁿᵈ; updᴱᴵⁿᵈ; Invᴵⁿᵈ; ⟨_⟩⇛ᴵⁿᵈ⟨_⟩_)

private variable
  ł :  Level
  M M' M'' :  Mem
  Pᵒ :  Propᵒ ł

--------------------------------------------------------------------------------
-- Interpret the super update

infix 3 ⟨_⟩⇛ᵒ⟨_⟩_ ⟨_⟩⇛ᵒ'⟨_⟩_

-- ⇛ᵒ :  Interpret the super update

⟨_⟩⇛ᵒ⟨_⟩_ :  Mem →  Mem →  Propᵒ ł →  Propᵒ (2ᴸ ⊔ᴸ ł)
⟨ M ⟩⇛ᵒ⟨ M' ⟩ Pᵒ =  ⟨ M ⟩⇛ᴵⁿᵈ⟨ M' ⟩ Pᵒ

-- ⇛ᵒ' :  Non-abstract version of ⇛ᵒ

⟨_⟩⇛ᵒ'⟨_⟩_ :  Mem →  Mem →  Propᵒ ł →  Propᵒ (2ᴸ ⊔ᴸ ł)
⟨ M ⟩⇛ᵒ'⟨ M' ⟩ Pᵒ =  ⟨ M ⟩[ envᴵⁿᵈ , updᴱᴵⁿᵈ , Invᴵⁿᵈ ]⇛ᵍ'⟨ M' ⟩ Pᵒ

abstract

  -- ⤇ᵒ into ⇛ᵒ

  ⤇ᵒ⇒⇛ᵒ :  ⤇ᵒ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ
  ⤇ᵒ⇒⇛ᵒ =  ⤇ᵒ⇒⇛ᵍ $ upd˙²-self λ ()

  -- Introduce ⇛ᵒ

  ⇛ᵒ-intro :  Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M ⟩ Pᵒ
  ⇛ᵒ-intro =  ⤇ᵒ-intro › ⤇ᵒ⇒⇛ᵒ

  -- Join ⇛ᵒ

  ⇛ᵒ-join :  ⟨ M ⟩⇛ᵒ⟨ M' ⟩ ⟨ M' ⟩⇛ᵒ⟨ M'' ⟩ Pᵒ  ⊨  ⟨ M ⟩⇛ᵒ⟨ M'' ⟩ Pᵒ
  ⇛ᵒ-join =  ⇛ᵍ-join refl $ upd˙²-2 λ ()
