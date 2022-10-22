--------------------------------------------------------------------------------
-- Interpret the name set token
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Symp.Model.Prop.Names where

open import Base.Level using (1ᴸ)
open import Base.Func using (_$_; _›_)
open import Base.Eq using (_≡˙_)
open import Base.Zoi using (Zoi; ✔ᶻ_; ⊤ᶻ; ^ᶻ_; _⊎ᶻ_; ^ᶻ-no2)
open import Base.Prod using (-,_)
open import Base.Sum using ()
open import Base.Nat using ()
open import Base.List using ()
open import Base.Str using ()
open import Symp.Logic.Prop using (Name)
open import Symp.Model.ERA.Names using ([_]ᴺʳ; []ᴺʳ-cong; []ᴺʳ-✔)
open import Symp.Model.ERA.Glob using (iᴺᵃᵐᵉˢ)
open import Symp.Model.Prop.Base using (Propᵒ; _⊨✓_; _⊨_; ⌜_⌝ᵒ; ⊥ᵒ₀; _∗ᵒ_;
  ◎⟨_⟩_; ◎⟨⟩-resp; ◎⟨⟩-∗ᵒ⇒∙; ◎⟨⟩-∙⇒∗ᵒ; ◎⟨⟩-✓)

private variable
  Nm Nm' :  Name → Zoi
  nm :  Name

--------------------------------------------------------------------------------
-- [ ]ᴺᵒ :  Interpret the name set token

[_]ᴺᵒ :  (Name → Zoi) →  Propᵒ 1ᴸ
[ Nm ]ᴺᵒ  =  ◎⟨ iᴺᵃᵐᵉˢ ⟩ [ Nm ]ᴺʳ

-- [⊤]ᴺᵒ :  Interpret the universal name set token

[⊤]ᴺᵒ :  Propᵒ 1ᴸ
[⊤]ᴺᵒ =  [ ⊤ᶻ ]ᴺᵒ

-- [^ ]ᴺᵒ :  Interpret the name token

[^_]ᴺᵒ :  Name →  Propᵒ 1ᴸ
[^ Nm ]ᴺᵒ  =  [ ^ᶻ Nm ]ᴺᵒ

abstract

  -- Change the set of [ ]ᴺᵒ

  []ᴺᵒ-resp :  Nm ≡˙ Nm' →  [ Nm ]ᴺᵒ ⊨ [ Nm' ]ᴺᵒ
  []ᴺᵒ-resp =  []ᴺʳ-cong › ◎⟨⟩-resp

  -- Merge and split [ ]ᴺᵒ w.r.t. ⊎ᶻ

  []ᴺᵒ-merge :  [ Nm ]ᴺᵒ  ∗ᵒ  [ Nm' ]ᴺᵒ  ⊨  [ Nm ⊎ᶻ Nm' ]ᴺᵒ
  []ᴺᵒ-merge =  ◎⟨⟩-∗ᵒ⇒∙

  []ᴺᵒ-split :  [ Nm ⊎ᶻ Nm' ]ᴺᵒ  ⊨  [ Nm ]ᴺᵒ  ∗ᵒ  [ Nm' ]ᴺᵒ
  []ᴺᵒ-split =  ◎⟨⟩-∙⇒∗ᵒ

  -- The set of [ ]ᴺᵒ is valid

  []ᴺᵒ-✔ :  [ Nm ]ᴺᵒ  ⊨✓  ⌜ ✔ᶻ Nm ⌝ᵒ
  []ᴺᵒ-✔ ✓∙ =   ◎⟨⟩-✓ ✓∙ › λ (-, ✓[Nm]) → []ᴺʳ-✔ ✓[Nm]

  -- [^ ]ᴺᵒ cannot overlap

  [^]ᴺᵒ-no2 :  [^ nm ]ᴺᵒ  ∗ᵒ  [^ nm ]ᴺᵒ  ⊨✓  ⊥ᵒ₀
  [^]ᴺᵒ-no2 ✓a =  []ᴺᵒ-merge › []ᴺᵒ-✔ ✓a › ^ᶻ-no2
