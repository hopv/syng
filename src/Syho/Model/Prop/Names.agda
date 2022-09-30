--------------------------------------------------------------------------------
-- Interpret the name set token
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Names where

open import Base.Level using (1ᴸ)
open import Base.Func using (_$_; _›_)
open import Base.Eq using (_≡˙_)
open import Base.Prod using (-,_)
open import Base.Zoi using (Zoi; _⊎ᶻ_; ✔ᶻ_)
open import Syho.Logic.Prop using (Name)
open import Syho.Model.ERA.Inv using ([_]ᴺʳ; []ᴺʳ-cong; []ᴺʳ-✔)
open import Syho.Model.ERA.Glob using (iᴵⁿᵛ)
open import Syho.Model.Prop.Base using (Propᵒ; _⊨✓_; _⊨_; ⌜_⌝ᵒ; _∗ᵒ_; ◎⟨_⟩_;
  ◎⟨⟩-resp; ◎⟨⟩-∗ᵒ⇒∙; ◎⟨⟩-∙⇒∗ᵒ; ◎⟨⟩-✓)

private variable
  Nm Nm' :  Name → Zoi

--------------------------------------------------------------------------------
-- [ ]ᴺᵒ :  Interpret the name set token

[_]ᴺᵒ :  (Name → Zoi) →  Propᵒ 1ᴸ
[ Nm ]ᴺᵒ  =  ◎⟨ iᴵⁿᵛ ⟩ [ Nm ]ᴺʳ

abstract

  -- Change the set of [ ]ᴺᵒ

  []ᴺᵒ-resp :  Nm ≡˙ Nm' →  [ Nm ]ᴺᵒ ⊨ [ Nm' ]ᴺᵒ
  []ᴺᵒ-resp =  []ᴺʳ-cong › ◎⟨⟩-resp

  -- Merge and split [ ]ᴺᵒ

  []ᴺᵒ-merge :  [ Nm ]ᴺᵒ  ∗ᵒ  [ Nm' ]ᴺᵒ  ⊨  [ Nm ⊎ᶻ Nm' ]ᴺᵒ
  []ᴺᵒ-merge =  ◎⟨⟩-∗ᵒ⇒∙

  []ᴺᵒ-split :  [ Nm ⊎ᶻ Nm' ]ᴺᵒ  ⊨  [ Nm ]ᴺᵒ  ∗ᵒ  [ Nm' ]ᴺᵒ
  []ᴺᵒ-split =  ◎⟨⟩-∙⇒∗ᵒ

  -- The set of [ ]ᴺᵒ is valid

  []ᴺᵒ-✔ :  [ Nm ]ᴺᵒ  ⊨✓  ⌜ ✔ᶻ Nm ⌝ᵒ
  []ᴺᵒ-✔ ✓∙ =   ◎⟨⟩-✓ ✓∙ › λ (-, ✓[Nm]) → []ᴺʳ-✔ ✓[Nm]
