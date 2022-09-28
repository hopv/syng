--------------------------------------------------------------------------------
-- Interpret basic propositions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Basic where

open import Base.Level using (1ᴸ)
open import Base.Size using (∞)
open import Base.Func using (_$_)
open import Syho.Logic.Prop using (Prop'; ∀˙; ∃˙; _→'_; _∗_; _-∗_; ⤇_; □_; [_]ᴵ;
  _↦⟨_⟩_; Free; Basic; ∀-Basic; ∃-Basic; →-Basic; ∗-Basic; -∗-Basic; ⤇-Basic;
  □-Basic; []ᴵ-Basic; ↦⟨⟩-Basic; Free-Basic)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; ∀ᵒ-syntax; ∃ᵒ-syntax;
  ⊥ᵒ; _→ᵒ_; _∗ᵒ_; _-∗ᵒ_; ⤇ᵒ_; □ᵒ_; ∀ᵒ-Mono; ∃ᵒ-Mono; →ᵒ-Mono; ∗ᵒ-Mono;
  -∗ᵒ-Mono; ⤇ᵒ-Mono; □ᵒ-Mono; ◎-Mono)
open import Syho.Model.Prop.Mem using (_↦⟨_⟩ᵒ_; Freeᵒ; Freeᵒ-Mono)

private variable
  P :  Prop' ∞

--------------------------------------------------------------------------------
-- ⸨ ⸩ᴮ :  Interpret Basic propositions

⸨_⸩ᴮ :  (P : Prop' ∞) →  {{Basic P}} →  Propᵒ 1ᴸ
⸨ ∀˙ P˙ ⸩ᴮ {{∀-Basic BasicP˙}} =  ∀ᵒ x , ⸨ P˙ x ⸩ᴮ {{BasicP˙ x}}
⸨ ∃˙ P˙ ⸩ᴮ {{∃-Basic BasicP˙}} =  ∃ᵒ x , ⸨ P˙ x ⸩ᴮ {{BasicP˙ x}}
⸨ P →' Q ⸩ᴮ {{→-Basic}} =  ⸨ P ⸩ᴮ →ᵒ ⸨ Q ⸩ᴮ
⸨ P ∗ Q ⸩ᴮ {{∗-Basic}} =  ⸨ P ⸩ᴮ ∗ᵒ ⸨ Q ⸩ᴮ
⸨ P -∗ Q ⸩ᴮ {{ -∗-Basic}} =  ⸨ P ⸩ᴮ -∗ᵒ ⸨ Q ⸩ᴮ
⸨ ⤇ P ⸩ᴮ {{⤇-Basic}} =  ⤇ᵒ ⸨ P ⸩ᴮ
⸨ □ P ⸩ᴮ {{□-Basic}} =  □ᵒ ⸨ P ⸩ᴮ
⸨ [ Nm ]ᴵ ⸩ᴮ {{[]ᴵ-Basic}} =  ⊥ᵒ  -- For now
⸨ θ ↦⟨ p ⟩ ᵗv ⸩ᴮ {{↦⟨⟩-Basic}} =  θ ↦⟨ p ⟩ᵒ ᵗv
⸨ Free n θ ⸩ᴮ {{Free-Basic}} =  Freeᵒ n θ

abstract

  -- ⸨ ⸩ᴮ satisfies monotonicity

  ⸨⸩ᴮ-Mono :  {{_ : Basic P}} →  Monoᵒ ⸨ P ⸩ᴮ
  ⸨⸩ᴮ-Mono {{∀-Basic BasicP˙}} =  ∀ᵒ-Mono (λ x → ⸨⸩ᴮ-Mono {{BasicP˙ x}})
  ⸨⸩ᴮ-Mono {{∃-Basic BasicP˙}} =  ∃ᵒ-Mono (λ x → ⸨⸩ᴮ-Mono {{BasicP˙ x}})
  ⸨⸩ᴮ-Mono {{→-Basic}} =  →ᵒ-Mono
  ⸨⸩ᴮ-Mono {{∗-Basic}} =  ∗ᵒ-Mono
  ⸨⸩ᴮ-Mono {{ -∗-Basic {Q = Q}}} =  -∗ᵒ-Mono {Qᵒ = ⸨ Q ⸩ᴮ}
  ⸨⸩ᴮ-Mono {{⤇-Basic}} =  ⤇ᵒ-Mono
  ⸨⸩ᴮ-Mono {{□-Basic {P}}} =  □ᵒ-Mono $ ⸨⸩ᴮ-Mono {P}
  ⸨⸩ᴮ-Mono {{↦⟨⟩-Basic}} =  ◎-Mono
  ⸨⸩ᴮ-Mono {{Free-Basic}} =  Freeᵒ-Mono
