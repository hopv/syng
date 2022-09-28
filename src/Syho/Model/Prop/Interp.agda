--------------------------------------------------------------------------------
-- Interpret all syntactic propositions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Interp where

open import Base.Level using (1ᴸ)
open import Base.Func using (id)
open import Base.Size using (∞; !)
open import Syho.Logic.Prop using (Prop'; ∀˙; ∃˙; _→'_; _∗_; _-∗_; ⤇_; □_; ○_;
  [_]ᴵ; Inv; OInv; _↪[_]⇛_; _↪[_]ᵃ⟨_⟩_; _↪⟨_⟩ᴾ_; _↪⟨_⟩ᵀ[_]_; _↦⟨_⟩_; Free;
  Basic; ∀-Basic; ∃-Basic; →-Basic; ∗-Basic; -∗-Basic; ⤇-Basic; □-Basic;
  ↦⟨⟩-Basic; Free-Basic)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨_; ∀ᵒ-syntax; ∃ᵒ-syntax;
  _→ᵒ_; _∗ᵒ_; _-∗ᵒ_; ⤇ᵒ_; □ᵒ_; ∀ᵒ-Mono; ∀ᵒ-mono; ∃ᵒ-Mono; ∃ᵒ-mono; →ᵒ-Mono;
  →ᵒ-mono; ∗ᵒ-Mono; ∗ᵒ-mono; -∗ᵒ-Mono; -∗ᵒ-mono; ⤇ᵒ-Mono; ⤇ᵒ-mono; □ᵒ-Mono;
  □ᵒ-mono; ◎-Mono; ⊥ᵒ {- For now -})
open import Syho.Model.Prop.Mem using (_↦⟨_⟩ᵒ_; Freeᵒ; Freeᵒ-Mono)
open import Syho.Model.Prop.Ind using (○ᵒ_; _↪[_]⇛ᵒ_; _↪[_]ᵃ⟨_⟩ᵒ_; _↪⟨_⟩ᴾᵒ_;
  _↪⟨_⟩ᵀ[_]ᵒ_; ○ᵒ-Mono; ↪⇛ᵒ-Mono; ↪ᵃ⟨⟩ᵒ-Mono; ↪⟨⟩ᴾᵒ-Mono; ↪⟨⟩ᵀᵒ-Mono)
open import Syho.Model.Prop.Basic using (⸨_⸩ᴮ)

private variable
  P :  Prop' ∞

--------------------------------------------------------------------------------
-- ⸨ ⸩ :  Interpret syntactic propositions

⸨_⸩ :  Prop' ∞ →  Propᵒ 1ᴸ
⸨ ∀˙ P˙ ⸩ =  ∀ᵒ x , ⸨ P˙ x ⸩
⸨ ∃˙ P˙ ⸩ =  ∃ᵒ x , ⸨ P˙ x ⸩
⸨ P →' Q ⸩ =  ⸨ P ⸩ →ᵒ ⸨ Q ⸩
⸨ P ∗ Q ⸩ =  ⸨ P ⸩ ∗ᵒ ⸨ Q ⸩
⸨ P -∗ Q ⸩ =  ⸨ P ⸩ -∗ᵒ ⸨ Q ⸩
⸨ ⤇ P ⸩ =  ⤇ᵒ ⸨ P ⸩
⸨ □ P ⸩ =  □ᵒ ⸨ P ⸩
⸨ ○ P˂ ⸩ =  ○ᵒ P˂ .!
⸨ P˂ ↪[ i ]⇛ Q˂ ⸩ =  P˂ .! ↪[ i ]⇛ᵒ Q˂ .!
⸨ P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙ ⸩ =  P˂ .! ↪[ i ]ᵃ⟨ red ⟩ᵒ λ v → Q˂˙ v .!
⸨ P˂ ↪⟨ e ⟩ᴾ Q˂˙ ⸩ =  P˂ .! ↪⟨ e ⟩ᴾᵒ λ v → Q˂˙ v .!
⸨ P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙ ⸩ =  P˂ .! ↪⟨ e ⟩ᵀ[ i ]ᵒ λ v → Q˂˙ v .!
⸨ [ Nm ]ᴵ ⸩ =  ⊥ᵒ -- For now
⸨ Inv nm P˂ ⸩ =  ⊥ᵒ -- For now
⸨ OInv nm P˂ ⸩ =  ⊥ᵒ -- For now
⸨ θ ↦⟨ p ⟩ ᵗv ⸩ =  θ ↦⟨ p ⟩ᵒ ᵗv
⸨ Free n θ ⸩ =  Freeᵒ n θ

abstract

  -- ⸨ ⸩ᴮ agrees with ⸨ ⸩
  -- ⸨⸩-ᴮ⇒ and ⸨⸩-⇒ᴮ are mutually recursive

  ⸨⸩-ᴮ⇒ :  {{_ : Basic P}} →  ⸨ P ⸩ᴮ ⊨ ⸨ P ⸩
  ⸨⸩-⇒ᴮ :  {{_ : Basic P}} →  ⸨ P ⸩ ⊨ ⸨ P ⸩ᴮ

  ⸨⸩-ᴮ⇒ {{∀-Basic BasicP˙}} {a} =  ∀ᵒ-mono (λ x → ⸨⸩-ᴮ⇒ {{BasicP˙ x}} {a}) {a}
  ⸨⸩-ᴮ⇒ {{∃-Basic BasicP˙}} {a} =  ∃ᵒ-mono (λ x → ⸨⸩-ᴮ⇒ {{BasicP˙ x}} {a}) {a}
  ⸨⸩-ᴮ⇒ {{→-Basic {P} {Q}}} =  →ᵒ-mono (⸨⸩-⇒ᴮ {P}) (⸨⸩-ᴮ⇒ {Q})
  ⸨⸩-ᴮ⇒ {{∗-Basic {P} {Q}}} =  ∗ᵒ-mono (⸨⸩-ᴮ⇒ {P}) (⸨⸩-ᴮ⇒ {Q})
  ⸨⸩-ᴮ⇒ {{ -∗-Basic {P} {Q}}} =  -∗ᵒ-mono (⸨⸩-⇒ᴮ {P}) (⸨⸩-ᴮ⇒ {Q})
  ⸨⸩-ᴮ⇒ {{⤇-Basic {P}}} =  ⤇ᵒ-mono (⸨⸩-ᴮ⇒ {P})
  ⸨⸩-ᴮ⇒ {{□-Basic {P}}} =  □ᵒ-mono λ{a} → ⸨⸩-ᴮ⇒ {P} {a}
  ⸨⸩-ᴮ⇒ {{↦⟨⟩-Basic}} =  id
  ⸨⸩-ᴮ⇒ {{Free-Basic}} =  id

  ⸨⸩-⇒ᴮ {{∀-Basic BasicP˙}} =  ∀ᵒ-mono λ x {a} → ⸨⸩-⇒ᴮ {{BasicP˙ x}} {a}
  ⸨⸩-⇒ᴮ {{∃-Basic BasicP˙}} =  ∃ᵒ-mono λ x {a} → ⸨⸩-⇒ᴮ {{BasicP˙ x}} {a}
  ⸨⸩-⇒ᴮ {{→-Basic {P} {Q}}} =  →ᵒ-mono (⸨⸩-ᴮ⇒ {P}) (⸨⸩-⇒ᴮ {Q})
  ⸨⸩-⇒ᴮ {{∗-Basic {P} {Q}}} =  ∗ᵒ-mono (⸨⸩-⇒ᴮ {P}) (⸨⸩-⇒ᴮ {Q})
  ⸨⸩-⇒ᴮ {{ -∗-Basic {P} {Q}}} =  -∗ᵒ-mono (⸨⸩-ᴮ⇒ {P}) (⸨⸩-⇒ᴮ {Q})
  ⸨⸩-⇒ᴮ {{⤇-Basic {P}}} =  ⤇ᵒ-mono (⸨⸩-⇒ᴮ {P})
  ⸨⸩-⇒ᴮ {{□-Basic {P}}} =  □ᵒ-mono λ{a} → ⸨⸩-⇒ᴮ {P} {a}
  ⸨⸩-⇒ᴮ {{↦⟨⟩-Basic}} =  id
  ⸨⸩-⇒ᴮ {{Free-Basic}} =  id

  --  ⸨ P ⸩ satisfies monotonicity

  ⸨⸩-Mono :  Monoᵒ ⸨ P ⸩
  ⸨⸩-Mono {∀˙ P˙} =  ∀ᵒ-Mono λ x → ⸨⸩-Mono {P˙ x}
  ⸨⸩-Mono {∃˙ P˙} =  ∃ᵒ-Mono λ x → ⸨⸩-Mono {P˙ x}
  ⸨⸩-Mono {_ →' _} =  →ᵒ-Mono
  ⸨⸩-Mono {_ ∗ _} =  ∗ᵒ-Mono
  ⸨⸩-Mono {_ -∗ _} =  -∗ᵒ-Mono
  ⸨⸩-Mono {⤇ _} =  ⤇ᵒ-Mono
  ⸨⸩-Mono {□ P} =  □ᵒ-Mono (⸨⸩-Mono {P})
  ⸨⸩-Mono {○ _} =  ○ᵒ-Mono
  ⸨⸩-Mono {_ ↪[ _ ]⇛ _} =  ↪⇛ᵒ-Mono
  ⸨⸩-Mono {_ ↪[ _ ]ᵃ⟨ _ ⟩ _} =  ↪ᵃ⟨⟩ᵒ-Mono
  ⸨⸩-Mono {_ ↪⟨ _ ⟩ᴾ _} =  ↪⟨⟩ᴾᵒ-Mono
  ⸨⸩-Mono {_ ↪⟨ _ ⟩ᵀ[ _ ] _} =  ↪⟨⟩ᵀᵒ-Mono
  ⸨⸩-Mono {_ ↦⟨ _ ⟩ _} =  ◎-Mono
  ⸨⸩-Mono {Free _ _} =  Freeᵒ-Mono
