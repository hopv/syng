--------------------------------------------------------------------------------
-- Interpreting basic propositions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Model.Basic (ℓ : Level) where

open import Base.Size using (∞)
open import Base.Func using (_$_)
open import Base.Prod using (_,_)
open import Shog.Logic.Prop ℓ using (Prop'; ∀˙; ∃˙; _∗_; IsBasic; ∀-IsBasic;
  ∃-IsBasic; ∗-IsBasic; Basic; isBasic)
open import Shog.Model.RA using (RA)
open import Shog.Model.RA.Glob ℓ using (Globᴿᴬ)
open RA Globᴿᴬ using (_⊑_; ✓_; _∙_; ⌞_⌟; _»˜_; ∙-comm; ⌞⌟-dup; ✓-⌞⌟)
open import Shog.Model.Prop Globᴿᴬ using (Propᵒ; monoᵒ; _⊨_; ∀ᵒ-syntax;
  ∃ᵒ-syntax; _∗ᵒ_; □ᵒ_)

private variable
  P :  Prop' ∞

--------------------------------------------------------------------------------
-- [| |]ᴮ[ ] : Interpreting IsBasic propositions

[|_|]ᴮ[_] :  (P : Prop' ∞) →  IsBasic P →  Propᵒ
[| ∀˙ _ P˙ |]ᴮ[ ∀-IsBasic IsBaP˙ ] =  ∀ᵒ x , [| P˙ x |]ᴮ[ IsBaP˙ x ]
[| ∃˙ _ P˙ |]ᴮ[ ∃-IsBasic IsBaP˙ ] =  ∃ᵒ x , [| P˙ x |]ᴮ[ IsBaP˙ x ]
[| P ∗ Q |]ᴮ[ ∗-IsBasic IsBaP IsBaQ ] =  [| P |]ᴮ[ IsBaP ] ∗ᵒ [| Q |]ᴮ[ IsBaQ ]

abstract

  [||]ᴮ'-⇒□ :  ∀ IsBaP →  [| P |]ᴮ[ IsBaP ] ⊨ □ᵒ [| P |]ᴮ[ IsBaP ]
  [||]ᴮ'-⇒□ (∀-IsBasic IsBaP˙) ∀xPxa x =  [||]ᴮ'-⇒□ (IsBaP˙ x) (∀xPxa x)
  [||]ᴮ'-⇒□ (∃-IsBasic IsBaP˙) (x , Pxa) =  x , [||]ᴮ'-⇒□ (IsBaP˙ x) Pxa
  [||]ᴮ'-⇒□ (∗-IsBasic {P} {Q} IsBaP IsBaQ) {a = a} {✓a = ✓a}
    (b , c , _ , _ , b∙c≈a , Pb , Qc) =
    ⌞ a ⌟ , ⌞ a ⌟ , ✓⌞a⌟ , ✓⌞a⌟ , ⌞⌟-dup {a} ,
    [||]ᴮ'-⇒□ IsBaP ([| P |]ᴮ[ IsBaP ] .monoᵒ b⊑a Pb) ,
    [||]ᴮ'-⇒□ IsBaQ ([| Q |]ᴮ[ IsBaQ ] .monoᵒ (b , b∙c≈a) Qc)
   where
    ✓⌞a⌟ :  ✓ ⌞ a ⌟
    ✓⌞a⌟ =  ✓-⌞⌟ {a} ✓a
    b⊑a :  b ⊑ a
    b⊑a =  c , (_»˜_ {c ∙ b} {b ∙ c} {a} (∙-comm {c} {b}) b∙c≈a)

--------------------------------------------------------------------------------
-- [| |]ᴮ : Interpreting Basic propositions

[|_|]ᴮ :  (P : Prop' ∞) →  {{Basic P}} →  Propᵒ
[| P |]ᴮ =  [| P |]ᴮ[ isBasic ]

abstract

  [||]ᴮ-⇒□ :  ∀ {{BaP}} →  [| P |]ᴮ {{BaP}} ⊨ □ᵒ [| P |]ᴮ {{BaP}}
  [||]ᴮ-⇒□ =  [||]ᴮ'-⇒□ isBasic
