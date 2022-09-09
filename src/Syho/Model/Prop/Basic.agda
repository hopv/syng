--------------------------------------------------------------------------------
-- Interpreting basic propositions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Basic where

open import Base.Level using (2ᴸ)
open import Base.Size using (∞)
open import Base.Func using (_$_)
open import Syho.Logic.Prop using (Prop'; ∀₁˙; ∃₁˙; _→'_; _∗_; _-∗_; ⤇_; □_;
  _↦⟨_⟩_; Free; Basic; ∀₁-Basic; ∃₁-Basic; →-Basic; ∗-Basic; -∗-Basic;
  ⤇-Basic; □-Basic; ↦⟨⟩-Basic; Free-Basic)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; ∀ᵒ-syntax; ∃ᵒ-syntax;
  ⊥ᵒ; _→ᵒ_; _∗ᵒ_; _-∗ᵒ_; ⤇ᵒ_; □ᵒ_; ∀ᵒ-Mono; ∃ᵒ-Mono; →ᵒ-Mono; ∗ᵒ-Mono;
  -∗ᵒ-Mono; ⤇ᵒ-Mono; □ᵒ-Mono)

private variable
  P :  Prop' ∞

--------------------------------------------------------------------------------
-- ⸨ ⸩ᴮ :  Interpret Basic propositions

⸨_⸩ᴮ :  (P : Prop' ∞) →  {{Basic P}} →  Propᵒ 2ᴸ
⸨ ∀₁˙ P˙ ⸩ᴮ {{∀₁-Basic BasicP˙}} =  ∀ᵒ x , ⸨ P˙ x ⸩ᴮ {{BasicP˙ x}}
⸨ ∃₁˙ P˙ ⸩ᴮ {{∃₁-Basic BasicP˙}} =  ∃ᵒ x , ⸨ P˙ x ⸩ᴮ {{BasicP˙ x}}
⸨ P →' Q ⸩ᴮ {{→-Basic}} =  ⸨ P ⸩ᴮ →ᵒ ⸨ Q ⸩ᴮ
⸨ P ∗ Q ⸩ᴮ {{∗-Basic}} =  ⸨ P ⸩ᴮ ∗ᵒ ⸨ Q ⸩ᴮ
⸨ P -∗ Q ⸩ᴮ {{ -∗-Basic}} =  ⸨ P ⸩ᴮ -∗ᵒ ⸨ Q ⸩ᴮ
⸨ ⤇ P ⸩ᴮ {{⤇-Basic}} =  ⤇ᵒ ⸨ P ⸩ᴮ
⸨ □ P ⸩ᴮ {{□-Basic}} =  □ᵒ ⸨ P ⸩ᴮ
⸨ θ ↦⟨ q⁺ ⟩ av ⸩ᴮ {{↦⟨⟩-Basic}} =  ⊥ᵒ  -- For now
⸨ Free n θ ⸩ᴮ {{Free-Basic}} =  ⊥ᵒ  -- For now

abstract

  -- ⸨ ⸩ᴮ satisfies monotonicity

  ⸨⸩ᴮ-Mono :  {{_ : Basic P}} →  Monoᵒ ⸨ P ⸩ᴮ
  ⸨⸩ᴮ-Mono {{∀₁-Basic BasicP˙}} =  ∀ᵒ-Mono (λ x → ⸨⸩ᴮ-Mono {{BasicP˙ x}})
  ⸨⸩ᴮ-Mono {{∃₁-Basic BasicP˙}} =  ∃ᵒ-Mono (λ x → ⸨⸩ᴮ-Mono {{BasicP˙ x}})
  ⸨⸩ᴮ-Mono {{→-Basic}} =  →ᵒ-Mono
  ⸨⸩ᴮ-Mono {{∗-Basic}} =  ∗ᵒ-Mono
  ⸨⸩ᴮ-Mono {{ -∗-Basic {Q = Q}}} =  -∗ᵒ-Mono {Qᵒ = ⸨ Q ⸩ᴮ}
  ⸨⸩ᴮ-Mono {{⤇-Basic}} =  ⤇ᵒ-Mono
  ⸨⸩ᴮ-Mono {{□-Basic {P}}} =  □ᵒ-Mono $ ⸨⸩ᴮ-Mono {P}
  ⸨⸩ᴮ-Mono {{↦⟨⟩-Basic}} _ ()  -- For now
  ⸨⸩ᴮ-Mono {{Free-Basic}} _ ()  -- For now
