--------------------------------------------------------------------------------
-- Interpret basic propositions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Basic where

open import Base.Level using (1ᴸ)
open import Base.Func using (_$_)
open import Syho.Logic.Prop using (Prop∞; ∀˙; ∃˙; _→'_; _∗_; _-∗_; ⤇_; □_; [_]ᴺ;
  _↦⟨_⟩_; Free; [_]ᴸ⟨_⟩; †ᴸ_; #ᵁᵇ⟨_⟩_; ≤ᵁᵇ⟨_⟩_; Basic; ∀-Basic; ∃-Basic;
  →-Basic; ∗-Basic; -∗-Basic; ⤇-Basic; □-Basic; []ᴺ-Basic; ↦⟨⟩-Basic;
  Free-Basic; []ᴸ⟨⟩-Basic; †ᴸ-Basic; #ᵁᵇ-Basic; ≤ᵁᵇ-Basic)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; ∀ᵒ-syntax; ∃ᵒ-syntax;
  _→ᵒ_; _∗ᵒ_; _-∗ᵒ_; ⤇ᵒ_; □ᵒ_; ∀ᵒ-Mono; ∃ᵒ-Mono; →ᵒ-Mono; ∗ᵒ-Mono; -∗ᵒ-Mono;
  ⤇ᵒ-Mono; □ᵒ-Mono; ◎-Mono)
open import Syho.Model.Prop.Names using ([_]ᴺᵒ)
open import Syho.Model.Prop.Mem using (_↦⟨_⟩ᵒ_; Freeᵒ; Freeᵒ-Mono)
open import Syho.Model.Prop.Lft using ([_]ᴸ⟨_⟩ᵒ; †ᴸᵒ_)
open import Syho.Model.Prop.Ub using (#ᵁᵇ⟨_⟩ᵒ_; ≤ᵁᵇ⟨_⟩ᵒ_)

private variable
  P :  Prop∞

--------------------------------------------------------------------------------
-- ⸨ ⸩ᴮ :  Interpret Basic propositions

⸨_⸩ᴮ :  (P : Prop∞) →  {{Basic P}} →  Propᵒ 1ᴸ
⸨ ∀˙ P˙ ⸩ᴮ {{∀-Basic BasicP˙}} =  ∀ᵒ x , ⸨ P˙ x ⸩ᴮ {{BasicP˙ x}}
⸨ ∃˙ P˙ ⸩ᴮ {{∃-Basic BasicP˙}} =  ∃ᵒ x , ⸨ P˙ x ⸩ᴮ {{BasicP˙ x}}
⸨ P →' Q ⸩ᴮ {{→-Basic}} =  ⸨ P ⸩ᴮ →ᵒ ⸨ Q ⸩ᴮ
⸨ P ∗ Q ⸩ᴮ {{∗-Basic}} =  ⸨ P ⸩ᴮ ∗ᵒ ⸨ Q ⸩ᴮ
⸨ P -∗ Q ⸩ᴮ {{ -∗-Basic}} =  ⸨ P ⸩ᴮ -∗ᵒ ⸨ Q ⸩ᴮ
⸨ ⤇ P ⸩ᴮ {{⤇-Basic}} =  ⤇ᵒ ⸨ P ⸩ᴮ
⸨ □ P ⸩ᴮ {{□-Basic}} =  □ᵒ ⸨ P ⸩ᴮ
⸨ [ Nm ]ᴺ ⸩ᴮ {{[]ᴺ-Basic}} =  [ Nm ]ᴺᵒ
⸨ θ ↦⟨ p ⟩ ᵗv ⸩ᴮ {{↦⟨⟩-Basic}} =  θ ↦⟨ p ⟩ᵒ ᵗv
⸨ Free n θ ⸩ᴮ {{Free-Basic}} =  Freeᵒ n θ
⸨ [ α ]ᴸ⟨ p ⟩ ⸩ᴮ {{[]ᴸ⟨⟩-Basic}} =  [ α ]ᴸ⟨ p ⟩ᵒ
⸨ †ᴸ α ⸩ᴮ {{†ᴸ-Basic}} =  †ᴸᵒ α
⸨ #ᵁᵇ⟨ i ⟩ n ⸩ᴮ {{#ᵁᵇ-Basic}} =  #ᵁᵇ⟨ i ⟩ᵒ n
⸨ ≤ᵁᵇ⟨ i ⟩ n ⸩ᴮ {{≤ᵁᵇ-Basic}} =  ≤ᵁᵇ⟨ i ⟩ᵒ n

abstract

  -- ⸨ ⸩ᴮ satisfies monotonicity

  ⸨⸩ᴮ-Mono :  {{_ : Basic P}} →  Monoᵒ ⸨ P ⸩ᴮ
  ⸨⸩ᴮ-Mono {{∀-Basic BasicP˙}} =  ∀ᵒ-Mono λ x → ⸨⸩ᴮ-Mono {{BasicP˙ x}}
  ⸨⸩ᴮ-Mono {{∃-Basic BasicP˙}} =  ∃ᵒ-Mono λ x → ⸨⸩ᴮ-Mono {{BasicP˙ x}}
  ⸨⸩ᴮ-Mono {{→-Basic}} =  →ᵒ-Mono
  ⸨⸩ᴮ-Mono {{∗-Basic}} =  ∗ᵒ-Mono
  ⸨⸩ᴮ-Mono {{ -∗-Basic {Q = Q}}} =  -∗ᵒ-Mono {Qᵒ = ⸨ Q ⸩ᴮ}
  ⸨⸩ᴮ-Mono {{⤇-Basic}} =  ⤇ᵒ-Mono
  ⸨⸩ᴮ-Mono {{□-Basic {P}}} =  □ᵒ-Mono $ ⸨⸩ᴮ-Mono {P}
  ⸨⸩ᴮ-Mono {{[]ᴺ-Basic}} =  ◎-Mono
  ⸨⸩ᴮ-Mono {{↦⟨⟩-Basic}} =  ◎-Mono
  ⸨⸩ᴮ-Mono {{Free-Basic}} =  Freeᵒ-Mono
  ⸨⸩ᴮ-Mono {{[]ᴸ⟨⟩-Basic}} =  ◎-Mono
  ⸨⸩ᴮ-Mono {{†ᴸ-Basic}} =  ◎-Mono
  ⸨⸩ᴮ-Mono {{#ᵁᵇ-Basic}} =  ◎-Mono
  ⸨⸩ᴮ-Mono {{≤ᵁᵇ-Basic}} =  ◎-Mono
