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
open import Shog.Model.Prop Globᴿᴬ using (Propᵒ; monoᵒ; renewᵒ; _⊨_; ∀ᵒ-syntax;
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
  [||]ᴮ'-⇒□ (∗-IsBasic {P} {Q} IsBaP IsBaQ) {a = a} {✓a}
   (b , c , b∙c≈a , Pb , Qc) =  ⌞ a ⌟ , ⌞ a ⌟ , ⌞⌟-dup {a} ,
    let P' = [| P |]ᴮ[ IsBaP ] in  let Q' = [| Q |]ᴮ[ IsBaQ ] in
    renewᵒ P'
      ([||]ᴮ'-⇒□ IsBaP {✓a = ✓a} $ P' .monoᵒ (c , (∙-comm »˜ b∙c≈a)) Pb) ,
    renewᵒ Q' ([||]ᴮ'-⇒□ IsBaQ {✓a = ✓a} $ Q' .monoᵒ (b , b∙c≈a) Qc)

--------------------------------------------------------------------------------
-- [| |]ᴮ : Interpreting Basic propositions

[|_|]ᴮ :  (P : Prop' ∞) →  {{Basic P}} →  Propᵒ
[| P |]ᴮ =  [| P |]ᴮ[ isBasic ]

abstract

  [||]ᴮ-⇒□ :  {{_ : Basic P}} →  [| P |]ᴮ ⊨ □ᵒ [| P |]ᴮ
  [||]ᴮ-⇒□ =  [||]ᴮ'-⇒□ isBasic
