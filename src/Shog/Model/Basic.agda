--------------------------------------------------------------------------------
-- Interpreting basic propositions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Model.Basic (ℓ : Level) where

open import Base.Size using (∞)
open import Base.Level using (Upˡ; upˡ)
open import Base.Func using (_$_)
open import Shog.Logic.Prop ℓ using (Prop'; ∀˙; ∃˙; _∗_; IsBasic; ∀-IsBasic;
  ∃-IsBasic; ∗-IsBasic; Basic; isBasic)
open import Shog.Model.RA using (RA)
open import Shog.Model.RA.Glob ℓ using (Globᴿᴬ)
open import Shog.Model.Prop Globᴿᴬ using (Propᵒ; ∀ᵒ˙; ∃ᵒ˙; _∗ᵒ_)

--------------------------------------------------------------------------------
-- [| |]ᴮ[ ] : Interpreting IsBasic propositions

[|_|]ᴮ[_] :  (P : Prop' ∞) →  IsBasic P →  Propᵒ
[| ∀˙ X P˙ |]ᴮ[ ∀-IsBasic IsBaP˙ ] =
  ∀ᵒ˙ (Upˡ X) $ λ (upˡ x) → [| P˙ x |]ᴮ[ IsBaP˙ x ]
[| ∃˙ X P˙ |]ᴮ[ ∃-IsBasic IsBaP˙ ] =
  ∃ᵒ˙ (Upˡ X) $ λ (upˡ x) → [| P˙ x |]ᴮ[ IsBaP˙ x ]
[| P ∗ Q |]ᴮ[ ∗-IsBasic IsBaP IsBaQ ] =  [| P |]ᴮ[ IsBaP ] ∗ᵒ [| Q |]ᴮ[ IsBaQ ]

--------------------------------------------------------------------------------
-- [| |]ᴮ : Interpreting Basic propositions

[|_|]ᴮ :  (P : Prop' ∞) →  {{Basic P}} →  Propᵒ
[| P |]ᴮ =  [| P |]ᴮ[ isBasic ]
