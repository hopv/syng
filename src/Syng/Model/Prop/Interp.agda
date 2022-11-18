--------------------------------------------------------------------------------
-- Interpret all syntactic propositions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syng.Model.Prop.Interp where

open import Base.Level using (1ᴸ)
open import Base.Func using (id)
open import Base.Size using (!)
open import Base.Prod using (_,_)
open import Syng.Logic.Prop using (SProp∞; ∀˙; ∃˙; _→'_; _∗_; _-∗_; ⤇_; □_;
  [_]ᴺ; _↦⟨_⟩_; Free; ○_; &ⁱ⟨_⟩_; ⅋ⁱ⟨_⟩_; _⊸[_]⇛_; _⊸[_]ᵃ⟨_⟩_; _⊸⟨_⟩[_]_;
  _⊸[_]⟨_⟩∞; [_]ᴸ⟨_⟩; †ᴸ_; &ᵐ⟨_⟩_; ⅋ᵐ⟨_⟩_; ⟨†_⟩_; #ᵁᵇ⟨_⟩_; ≤ᵁᵇ⟨_⟩_; Basic;
  ∀-Basic; ∃-Basic; →-Basic; ∗-Basic; -∗-Basic; ⤇-Basic; □-Basic; []ᴺ-Basic;
  ↦⟨⟩-Basic; Free-Basic; []ᴸ⟨⟩-Basic; †ᴸ-Basic; #ᵁᵇ-Basic; ≤ᵁᵇ-Basic)
open import Syng.Model.ERA.Glob using (Globᴱᴿᴬ)
open import Syng.Model.Prop.Base using (SPropᵒ; Monoᵒ; _⊨_; ∀ᵒ-syntax;
  ∃ᵒ-syntax; _→ᵒ_; _∗ᵒ_; _-∗ᵒ_; ⤇ᵒ_; □ᵒ_; ∀ᵒ-Mono; ∀ᵒ-mono; ∃ᵒ-Mono; ∃ᵒ-mono;
  →ᵒ-Mono; →ᵒ-mono; ∗ᵒ-Mono; ∗ᵒ-mono; -∗ᵒ-Mono; -∗ᵒ-mono; ⤇ᵒ-Mono; ⤇ᵒ-mono;
  □ᵒ-Mono; □ᵒ-mono; ◎-Mono)
open import Syng.Model.Prop.Names using ([_]ᴺᵒ)
open import Syng.Model.Prop.Heap using (_↦⟨_⟩ᵒ_; Freeᵒ; Freeᵒ-Mono)
open import Syng.Model.Prop.Lft using ([_]ᴸ⟨_⟩ᵒ; †ᴸᵒ_)
open import Syng.Model.Prop.Basic using (⸨_⸩ᴮ)
open import Syng.Model.Prop.Ind using (○ᵒ_; _⊸[_]⇛ˢ_; _⊸[_]ᵃ⟨_⟩ᵒ_; _⊸⟨_⟩[_]ᵒ_;
  _⊸[_]⟨_⟩∞ᵒ; ○ᵒ-Mono; ⊸⇛ᵒ-Mono; ⊸ᵃ⟨⟩ᵒ-Mono; ⊸⟨⟩ᵒ-Mono; ⊸⟨⟩∞ᵒ-Mono)
open import Syng.Model.Prop.Inv using (&ⁱ⟨_⟩ᵒ_; ⅋ⁱ⟨_⟩ᵒ_; &ⁱᵒ-Mono; ⅋ⁱᵒ-Mono)
open import Syng.Model.Prop.Bor using (&ᵐ⟨_⟩ᵒ_; ⅋ᵐ⟨_⟩ᵒ_; ⟨†_⟩ᵒ_; &ᵐᵒ-Mono;
  ⅋ᵐᵒ-Mono; ⟨†⟩ᵒ-Mono)
open import Syng.Model.Prop.Ub using (#ᵁᵇ⟨_⟩ᵒ_; ≤ᵁᵇ⟨_⟩ᵒ_)

private variable
  P :  SProp∞

--------------------------------------------------------------------------------
-- ⸨ ⸩ :  Interpret syntactic propositions

⸨_⸩ :  SProp∞ →  SPropᵒ 1ᴸ
⸨ ∀˙ P˙ ⸩ =  ∀ᵒ x , ⸨ P˙ x ⸩
⸨ ∃˙ P˙ ⸩ =  ∃ᵒ x , ⸨ P˙ x ⸩
⸨ P →' Q ⸩ =  ⸨ P ⸩ →ᵒ ⸨ Q ⸩
⸨ P ∗ Q ⸩ =  ⸨ P ⸩ ∗ᵒ ⸨ Q ⸩
⸨ P -∗ Q ⸩ =  ⸨ P ⸩ -∗ᵒ ⸨ Q ⸩
⸨ ⤇ P ⸩ =  ⤇ᵒ ⸨ P ⸩
⸨ □ P ⸩ =  □ᵒ ⸨ P ⸩
⸨ [ Nm ]ᴺ ⸩ =  [ Nm ]ᴺᵒ
⸨ θ ↦⟨ p ⟩ ᵗv ⸩ =  θ ↦⟨ p ⟩ᵒ ᵗv
⸨ Free n θ ⸩ =  Freeᵒ n θ
⸨ ○ P˂ ⸩ =  ○ᵒ P˂ .!
⸨ P˂ ⊸[ i ]⇛ Q˂ ⸩ =  P˂ .! ⊸[ i ]⇛ˢ Q˂ .!
⸨ P˂ ⊸[ i ]ᵃ⟨ red ⟩ Q˂˙ ⸩ =  P˂ .! ⊸[ i ]ᵃ⟨ red ⟩ᵒ λ v → Q˂˙ v .!
⸨ P˂ ⊸⟨ e ⟩[ κ ] Q˂˙ ⸩ =  P˂ .! ⊸⟨ e ⟩[ κ ]ᵒ λ v → Q˂˙ v .!
⸨ P˂ ⊸[ i ]⟨ e ⟩∞ ⸩ =  P˂ .! ⊸[ i ]⟨ e ⟩∞ᵒ
⸨ &ⁱ⟨ nm ⟩ P˂ ⸩ =  &ⁱ⟨ nm ⟩ᵒ P˂ .!
⸨ ⅋ⁱ⟨ nm ⟩ P˂ ⸩ =  ⅋ⁱ⟨ nm ⟩ᵒ P˂ .!
⸨ [ α ]ᴸ⟨ p ⟩ ⸩ =  [ α ]ᴸ⟨ p ⟩ᵒ
⸨ †ᴸ α ⸩ =  †ᴸᵒ α
⸨ &ᵐ⟨ α ⟩ P˂ ⸩ =  &ᵐ⟨ α ⟩ᵒ P˂ .!
⸨ ⅋ᵐ⟨ α , p ⟩ P˂ ⸩ =  ⅋ᵐ⟨ α , p ⟩ᵒ P˂ .!
⸨ ⟨† α ⟩ P˂ ⸩ =  ⟨† α ⟩ᵒ P˂ .!
⸨ #ᵁᵇ⟨ i ⟩ n ⸩ =  #ᵁᵇ⟨ i ⟩ᵒ n
⸨ ≤ᵁᵇ⟨ i ⟩ n ⸩ =  ≤ᵁᵇ⟨ i ⟩ᵒ n

abstract

  --  ⸨ P ⸩ satisfies monotonicity

  ⸨⸩-Mono :  Monoᵒ ⸨ P ⸩
  ⸨⸩-Mono {∀˙ P˙} =  ∀ᵒ-Mono λ x → ⸨⸩-Mono {P˙ x}
  ⸨⸩-Mono {∃˙ P˙} =  ∃ᵒ-Mono λ x → ⸨⸩-Mono {P˙ x}
  ⸨⸩-Mono {_ →' _} =  →ᵒ-Mono
  ⸨⸩-Mono {_ ∗ _} =  ∗ᵒ-Mono
  ⸨⸩-Mono {_ -∗ _} =  -∗ᵒ-Mono
  ⸨⸩-Mono {⤇ _} =  ⤇ᵒ-Mono
  ⸨⸩-Mono {□ P} =  □ᵒ-Mono (⸨⸩-Mono {P})
  ⸨⸩-Mono {[ _ ]ᴺ} =  ◎-Mono
  ⸨⸩-Mono {_ ↦⟨ _ ⟩ _} =  ◎-Mono
  ⸨⸩-Mono {Free _ _} =  Freeᵒ-Mono
  ⸨⸩-Mono {○ _} =  ○ᵒ-Mono
  ⸨⸩-Mono {_ ⊸[ _ ]⇛ _} =  ⊸⇛ᵒ-Mono
  ⸨⸩-Mono {_ ⊸[ _ ]ᵃ⟨ _ ⟩ _} =  ⊸ᵃ⟨⟩ᵒ-Mono
  ⸨⸩-Mono {_ ⊸⟨ _ ⟩[ _ ] _} =  ⊸⟨⟩ᵒ-Mono
  ⸨⸩-Mono {_ ⊸[ _ ]⟨ _ ⟩∞} =  ⊸⟨⟩∞ᵒ-Mono
  ⸨⸩-Mono {&ⁱ⟨ _ ⟩ _} =  &ⁱᵒ-Mono
  ⸨⸩-Mono {⅋ⁱ⟨ _ ⟩ _} =  ⅋ⁱᵒ-Mono
  ⸨⸩-Mono {[ _ ]ᴸ⟨ _ ⟩} =  ◎-Mono
  ⸨⸩-Mono {†ᴸ _} =  ◎-Mono
  ⸨⸩-Mono {&ᵐ⟨ _ ⟩ _} =  &ᵐᵒ-Mono
  ⸨⸩-Mono {⅋ᵐ⟨ _ , p ⟩ _} =  ⅋ᵐᵒ-Mono {p = p}
  ⸨⸩-Mono {⟨† _ ⟩ _} =  ⟨†⟩ᵒ-Mono
  ⸨⸩-Mono {#ᵁᵇ⟨ _ ⟩ _} =  ◎-Mono
  ⸨⸩-Mono {≤ᵁᵇ⟨ _ ⟩ _} =  ◎-Mono

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
  ⸨⸩-ᴮ⇒ {{[]ᴺ-Basic}} =  id
  ⸨⸩-ᴮ⇒ {{↦⟨⟩-Basic}} =  id
  ⸨⸩-ᴮ⇒ {{Free-Basic}} =  id
  ⸨⸩-ᴮ⇒ {{[]ᴸ⟨⟩-Basic}} =  id
  ⸨⸩-ᴮ⇒ {{†ᴸ-Basic}} =  id
  ⸨⸩-ᴮ⇒ {{#ᵁᵇ-Basic}} =  id
  ⸨⸩-ᴮ⇒ {{≤ᵁᵇ-Basic}} =  id

  ⸨⸩-⇒ᴮ {{∀-Basic BasicP˙}} =  ∀ᵒ-mono λ x {a} → ⸨⸩-⇒ᴮ {{BasicP˙ x}} {a}
  ⸨⸩-⇒ᴮ {{∃-Basic BasicP˙}} =  ∃ᵒ-mono λ x {a} → ⸨⸩-⇒ᴮ {{BasicP˙ x}} {a}
  ⸨⸩-⇒ᴮ {{→-Basic {P} {Q}}} =  →ᵒ-mono (⸨⸩-ᴮ⇒ {P}) (⸨⸩-⇒ᴮ {Q})
  ⸨⸩-⇒ᴮ {{∗-Basic {P} {Q}}} =  ∗ᵒ-mono (⸨⸩-⇒ᴮ {P}) (⸨⸩-⇒ᴮ {Q})
  ⸨⸩-⇒ᴮ {{ -∗-Basic {P} {Q}}} =  -∗ᵒ-mono (⸨⸩-ᴮ⇒ {P}) (⸨⸩-⇒ᴮ {Q})
  ⸨⸩-⇒ᴮ {{⤇-Basic {P}}} =  ⤇ᵒ-mono (⸨⸩-⇒ᴮ {P})
  ⸨⸩-⇒ᴮ {{□-Basic {P}}} =  □ᵒ-mono λ{a} → ⸨⸩-⇒ᴮ {P} {a}
  ⸨⸩-⇒ᴮ {{[]ᴺ-Basic}} =  id
  ⸨⸩-⇒ᴮ {{↦⟨⟩-Basic}} =  id
  ⸨⸩-⇒ᴮ {{Free-Basic}} =  id
  ⸨⸩-⇒ᴮ {{[]ᴸ⟨⟩-Basic}} =  id
  ⸨⸩-⇒ᴮ {{†ᴸ-Basic}} =  id
  ⸨⸩-⇒ᴮ {{#ᵁᵇ-Basic}} =  id
  ⸨⸩-⇒ᴮ {{≤ᵁᵇ-Basic}} =  id
