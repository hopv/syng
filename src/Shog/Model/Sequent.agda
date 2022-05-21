--------------------------------------------------------------------------------
-- Interpreting propositions and proving semantic soundness of the sequent
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Model.Sequent (ℓ : Level) where

open import Base.Size using (Size; ∞)
open import Base.Func using (_$_)
open import Base.Thunk using (!)
open import Base.Prod using (_,_)
open import Shog.Logic.Prop ℓ using (Prop'; ∀˙; ∃˙; _→'_; _∗_; _-∗_; |=>_; □_;
  saveˣ; save□; IsBasic; ∀-IsBasic; ∃-IsBasic; ∗-IsBasic; Basic; isBasic)
open import Shog.Logic.Judg.All ℓ using (_⊢[_]_; pure; refl; _»_;
  ∀-intro; ∃-elim; ∀-elim; ∃-intro; choice; →-intro; →-elim;
  ⊤∗-elim; ⊤∗-intro; ∗-comm; ∗-assocˡ; ∗-monoˡ; -∗-intro; -∗-elim;
  |=>-mono; |=>-intro; |=>-join; |=>-frameˡ; |=>-∃-out;
  □-mono; □-elim; □-dup; □ˡ-∧⇒∗; □-∀-in; □-∃-out; save□-□)
open import Shog.Model.RA.Glob ℓ using (Globᴿᴬ)
open import Shog.Model.Prop Globᴿᴬ using (Propᵒ; _⊨_; ∀ᵒ-syntax; ∃ᵒ-syntax;
  _→ᵒ_; _∗ᵒ_; _-∗ᵒ_; |=>ᵒ_; □ᵒ_)
open import Shog.Model.Save.X ℓ using (saveˣᵒ)
open import Shog.Model.Save.P ℓ using (save□ᵒ)
open import Shog.Model.Basic ℓ using ([|_|]ᴮ[_]; [|_|]ᴮ)

private variable
  P Q :  Prop' ∞
  ι :  Size

--------------------------------------------------------------------------------
-- [| |]: Interpreting propositions

[|_|] :  (P : Prop' ∞) →  Propᵒ
[| ∀˙ _ P˙ |] =  ∀ᵒ x , [| P˙ x |]
[| ∃˙ _ P˙ |] =  ∃ᵒ x , [| P˙ x |]
[| P →' Q |] =  [| P |] →ᵒ [| Q |]
[| P ∗ Q |] =  [| P |] ∗ᵒ [| Q |]
[| P -∗ Q |] =  [| P |] -∗ᵒ [| Q |]
[| |=> P |] =  |=>ᵒ [| P |]
[| □ P |] =  □ᵒ [| P |]
[| saveˣ P^ |] =  saveˣᵒ (P^ .!)
[| save□ P^ |] =  save□ᵒ (P^ .!)

abstract

  -- [| |]ᴮ[ ] / [| |]ᴮ agrees with [| |]

  [||]-ᴮ'⇒ :  (IsBaP : IsBasic P) →  [| P |]ᴮ[ IsBaP ] ⊨ [| P |]
  [||]-ᴮ'⇒ (∀-IsBasic IsBaP˙) ∀xPxa x =  [||]-ᴮ'⇒ (IsBaP˙ x) (∀xPxa x)
  [||]-ᴮ'⇒ (∃-IsBasic IsBaP˙) (x , Pxa) =  x , [||]-ᴮ'⇒ (IsBaP˙ x) Pxa
  [||]-ᴮ'⇒ (∗-IsBasic IsBaP IsBaQ) (b , c , _ , _ , bc≈a , Pb , Qc) =
    b , c , _ , _ , bc≈a , [||]-ᴮ'⇒ IsBaP Pb , [||]-ᴮ'⇒ IsBaQ Qc

  [||]-⇒ᴮ' :  (IsBaP : IsBasic P) →  [| P |] ⊨ [| P |]ᴮ[ IsBaP ]
  [||]-⇒ᴮ' (∀-IsBasic IsBaP˙) ∀xPxa x =  [||]-⇒ᴮ' (IsBaP˙ x) (∀xPxa x)
  [||]-⇒ᴮ' (∃-IsBasic IsBaP˙) (x , Pxa) =  x , [||]-⇒ᴮ' (IsBaP˙ x) Pxa
  [||]-⇒ᴮ' (∗-IsBasic IsBaP IsBaQ) (b , c , _ , _ , bc≈a , Pb , Qc) =
    b , c , _ , _ , bc≈a , [||]-⇒ᴮ' IsBaP Pb , [||]-⇒ᴮ' IsBaQ Qc

  [||]-ᴮ⇒ :  {{BaP : Basic P}} →  [| P |]ᴮ {{BaP}} ⊨ [| P |]
  [||]-ᴮ⇒ =  [||]-ᴮ'⇒ isBasic

  [||]-⇒ᴮ :  {{BaP : Basic P}} →  [| P |] ⊨ [| P |]ᴮ {{BaP}}
  [||]-⇒ᴮ =  [||]-⇒ᴮ' isBasic
