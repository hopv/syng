--------------------------------------------------------------------------------
-- Interpreting basic propositions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Model.Basic where

open import Base.Size using (∞)
open import Base.Func using (_$_)
open import Base.Prod using (_,_)
open import Shog.Logic.Prop using (Prop'; ∀₁˙; ∃₁˙; _∗_; □_; IsBasic;
  ∀₁-IsBasic; ∃₁-IsBasic; ∗-IsBasic; □-IsBasic; Basic; isBasic)
open import Shog.Model.RA using (RA)
open import Shog.Model.RA.Glob using (GlobRA)
open RA GlobRA using (⊑-trans; ⌞⌟-∙; ⌞⌟-mono)
open import Shog.Model.Prop GlobRA using (Propᵒ; monoᵒ; _⊨'_; ∀₁ᵒ-syntax;
  ∃₁ᵒ-syntax; _∗ᵒ_; □ᵒ_)

private variable
  P :  Prop' ∞

--------------------------------------------------------------------------------
-- ⸨ ⸩ᴮ[ ] : Interpreting IsBasic propositions

⸨_⸩ᴮ[_] :  (P : Prop' ∞) →  IsBasic P →  Propᵒ
⸨ ∀₁˙ P˙ ⸩ᴮ[ ∀₁-IsBasic IsBaP˙ ] =  ∀₁ᵒ x , ⸨ P˙ x ⸩ᴮ[ IsBaP˙ x ]
⸨ ∃₁˙ P˙ ⸩ᴮ[ ∃₁-IsBasic IsBaP˙ ] =  ∃₁ᵒ x , ⸨ P˙ x ⸩ᴮ[ IsBaP˙ x ]
⸨ P ∗ Q ⸩ᴮ[ ∗-IsBasic IsBaP IsBaQ ] =  ⸨ P ⸩ᴮ[ IsBaP ] ∗ᵒ ⸨ Q ⸩ᴮ[ IsBaQ ]
⸨ □ P ⸩ᴮ[ □-IsBasic IsBaP ] =  □ᵒ ⸨ P ⸩ᴮ[ IsBaP ]

abstract

  -- ⸨ P ⸩ᴮ[ ... ] is persistent

  ⸨⸩ᴮ'-⇒□ :  ∀ IsBaP →  ⸨ P ⸩ᴮ[ IsBaP ] ⊨' □ᵒ ⸨ P ⸩ᴮ[ IsBaP ]
  ⸨⸩ᴮ'-⇒□ (∀₁-IsBasic IsBaP˙) ∀xPxa x =  ⸨⸩ᴮ'-⇒□ (IsBaP˙ x) (∀xPxa x)
  ⸨⸩ᴮ'-⇒□ (∃₁-IsBasic IsBaP˙) (x , Pxa) =  x , ⸨⸩ᴮ'-⇒□ (IsBaP˙ x) Pxa
  ⸨⸩ᴮ'-⇒□ (∗-IsBasic {P} {Q} IsBaP IsBaQ) (_ , _ , b∙c⊑a , Pb , Qc) =
    _ , _ , ⊑-trans ⌞⌟-∙ (⌞⌟-mono b∙c⊑a) , ⸨⸩ᴮ'-⇒□ IsBaP Pb , ⸨⸩ᴮ'-⇒□ IsBaQ Qc
  ⸨⸩ᴮ'-⇒□ (□-IsBasic IsBaP) P⌞a⌟ =  ⸨⸩ᴮ'-⇒□ IsBaP P⌞a⌟

--------------------------------------------------------------------------------
-- ⸨ ⸩ᴮ : Interpreting Basic propositions

⸨_⸩ᴮ :  (P : Prop' ∞) →  {{Basic P}} →  Propᵒ
⸨ P ⸩ᴮ =  ⸨ P ⸩ᴮ[ isBasic ]

abstract

  -- ⸨ P ⸩ᴮ is persistent

  ⸨⸩ᴮ-⇒□ :  {{_ : Basic P}} →  ⸨ P ⸩ᴮ ⊨' □ᵒ ⸨ P ⸩ᴮ
  ⸨⸩ᴮ-⇒□ =  ⸨⸩ᴮ'-⇒□ isBasic
