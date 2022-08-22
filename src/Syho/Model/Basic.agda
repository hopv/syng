--------------------------------------------------------------------------------
-- Interpreting basic propositions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Basic where

open import Base.Size using (∞)
open import Base.Few using (⊤)
open import Syho.Logic.Prop using (Prop'; ∀₁˙; ∃₁˙; _→'_; _∗_; _-∗_; ⤇_; □_;
  _↦⟨_⟩_; Free; Basic; ∀₁-Basic; ∃₁-Basic; →-Basic; ∗-Basic; -∗-Basic;
  ⤇-Basic; □-Basic; ↦⟨⟩-Basic; Free-Basic)
open import Syho.Model.Prop using (Propᵒ; ∀₁ᵒ-syntax; ∃₁ᵒ-syntax; _→ᵒ_; _∗ᵒ_;
  _-∗ᵒ_; ⤇ᵒ_; □ᵒ_)

--------------------------------------------------------------------------------
-- ⸨ ⸩ᴮ :  Interpreting Basic propositions

⸨_⸩ᴮ :  (P : Prop' ∞) →  {{Basic P}} →  Propᵒ
⸨ ∀₁˙ P˙ ⸩ᴮ {{∀₁-Basic BasicP˙}} =  ∀₁ᵒ x , ⸨ P˙ x ⸩ᴮ {{BasicP˙ x}}
⸨ ∃₁˙ P˙ ⸩ᴮ {{∃₁-Basic BasicP˙}} =  ∃₁ᵒ x , ⸨ P˙ x ⸩ᴮ {{BasicP˙ x}}
⸨ P →' Q ⸩ᴮ {{→-Basic}} =  ⸨ P ⸩ᴮ →ᵒ ⸨ Q ⸩ᴮ
⸨ P ∗ Q ⸩ᴮ {{∗-Basic}} =  ⸨ P ⸩ᴮ ∗ᵒ ⸨ Q ⸩ᴮ
⸨ P -∗ Q ⸩ᴮ {{ -∗-Basic}} =  ⸨ P ⸩ᴮ -∗ᵒ ⸨ Q ⸩ᴮ
⸨ ⤇ P ⸩ᴮ {{⤇-Basic}} =  ⤇ᵒ ⸨ P ⸩ᴮ
⸨ □ P ⸩ᴮ {{□-Basic}} =  □ᵒ ⸨ P ⸩ᴮ
⸨ θ ↦⟨ q⁺ ⟩ av ⸩ᴮ {{↦⟨⟩-Basic}} =  λ _ → ⊤
⸨ Free n θ ⸩ᴮ {{Free-Basic}} =  λ _ → ⊤
