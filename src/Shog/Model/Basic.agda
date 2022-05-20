--------------------------------------------------------------------------------
-- Interpreting basic propositions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Model.Basic (ℓ : Level) where

open import Base.Size using (∞)
open import Base.Level using (↓ˡ_)
open import Base.Func using (_$_)
open import Shog.Logic.Prop ℓ using (Prop'; ∀˙; ∃˙; _∗_; IsBasic; ∀-IsBasic;
  ∃-IsBasic; ∗-IsBasic; Basic; isBasic)
open import Shog.Model.RA using (RA)
open import Shog.Model.RA.Glob ℓ using (Globᴿᴬ)
open import Shog.Model.Prop Globᴿᴬ using (Propᵒ; ∀ᵒ-syntax; ∃ᵒ-syntax; _∗ᵒ_)

--------------------------------------------------------------------------------
-- [| |]ᴮ[ ] : Interpreting IsBasic propositions

[|_|]ᴮ[_] :  (P : Prop' ∞) →  IsBasic P →  Propᵒ
[| ∀˙ _ P˙ |]ᴮ[ ∀-IsBasic IsBaP˙ ] =  ∀ᵒ x , [| P˙ (↓ˡ x) |]ᴮ[ IsBaP˙ (↓ˡ x) ]
[| ∃˙ _ P˙ |]ᴮ[ ∃-IsBasic IsBaP˙ ] =  ∃ᵒ x , [| P˙ (↓ˡ x) |]ᴮ[ IsBaP˙ (↓ˡ x) ]
[| P ∗ Q |]ᴮ[ ∗-IsBasic IsBaP IsBaQ ] =  [| P |]ᴮ[ IsBaP ] ∗ᵒ [| Q |]ᴮ[ IsBaQ ]

--------------------------------------------------------------------------------
-- [| |]ᴮ : Interpreting Basic propositions

[|_|]ᴮ :  (P : Prop' ∞) →  {{Basic P}} →  Propᵒ
[| P |]ᴮ =  [| P |]ᴮ[ isBasic ]
