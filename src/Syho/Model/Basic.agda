--------------------------------------------------------------------------------
-- Interpreting basic propositions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Basic where

open import Base.Size using (∞)
open import Base.Few using (⊤)
open import Base.Prod using (∑-syntax; _×_; _,_)
open import Syho.Logic.Prop using (Prop'; ∀₁˙; ∃₁˙; _→'_; _∗_; _-∗_; |=>_; □_;
  _↦⟨_⟩_; Free; Basic; ∀₁-Basic; ∃₁-Basic; →-Basic; ∗-Basic; -∗-Basic;
  |=>-Basic; □-Basic; ↦⟨⟩-Basic; Free-Basic)
open import Syho.Model.ERA using (ERA)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ)
open import Syho.Model.Prop using (Propᵒ)

open ERA Globᴱᴿᴬ using (_⊑_; _✓_; _∙_; ⌞_⌟)

private variable
  P :  Prop' ∞
  X₁ :  Set₁

--------------------------------------------------------------------------------
-- Interpreting ∀₁, ∃₁, →', ∗, -∗, |=>, □

∀₁ᵒ˙ ∃₁ᵒ˙ ∀₁ᵒ-syntax ∃₁ᵒ-syntax : (X₁ → Propᵒ) →  Propᵒ
∀₁ᵒ˙ Pᵒ˙ a =  ∀ x →  Pᵒ˙ x a
∃₁ᵒ˙ Pᵒ˙ a =  ∑ x ,  Pᵒ˙ x a
∀₁ᵒ-syntax =  ∀₁ᵒ˙
∃₁ᵒ-syntax =  ∃₁ᵒ˙
infix 3 ∀₁ᵒ-syntax ∃₁ᵒ-syntax
syntax ∀₁ᵒ-syntax (λ x → Pᵒ) =  ∀₁ᵒ x , Pᵒ
syntax ∃₁ᵒ-syntax (λ x → Pᵒ) =  ∃₁ᵒ x , Pᵒ

infixr 5 _→ᵒ_
_→ᵒ_ :  Propᵒ → Propᵒ → Propᵒ
(Pᵒ →ᵒ Qᵒ) a =  ∀ {E b} →  a ⊑ b →  E ✓ b →  Pᵒ b →  Qᵒ b

infixr 7 _∗ᵒ_
_∗ᵒ_ :  Propᵒ → Propᵒ → Propᵒ
(Pᵒ ∗ᵒ Qᵒ) a =  ∑ b , ∑ c ,  b ∙ c ⊑ a × Pᵒ b  ×  Qᵒ c

infixr 5 _-∗ᵒ_
_-∗ᵒ_ :  Propᵒ → Propᵒ → Propᵒ
(Pᵒ -∗ᵒ Qᵒ) a =  ∀ {E b c} →  a ⊑ b →  E ✓ c ∙ b →  Pᵒ c → Qᵒ (c ∙ b)

infix 8 |=>ᵒ_
|=>ᵒ_ :  Propᵒ → Propᵒ
(|=>ᵒ Pᵒ) a =  ∀ {E c} →  E ✓ c ∙ a →  ∑ b ,  E ✓ c ∙ b  ×  Pᵒ b

infix 8 □ᵒ_
□ᵒ_ :  Propᵒ → Propᵒ
(□ᵒ Pᵒ) a =  Pᵒ ⌞ a ⌟

--------------------------------------------------------------------------------
-- ⸨ ⸩ᴮ :  Interpreting Basic propositions

⸨_⸩ᴮ :  (P : Prop' ∞) →  {{Basic P}} →  Propᵒ
⸨ ∀₁˙ P˙ ⸩ᴮ {{∀₁-Basic IsBaP˙}} =  ∀₁ᵒ x , ⸨ P˙ x ⸩ᴮ {{IsBaP˙ x}}
⸨ ∃₁˙ P˙ ⸩ᴮ {{∃₁-Basic IsBaP˙}} =  ∃₁ᵒ x , ⸨ P˙ x ⸩ᴮ {{IsBaP˙ x}}
⸨ P →' Q ⸩ᴮ {{→-Basic}} =  ⸨ P ⸩ᴮ →ᵒ ⸨ Q ⸩ᴮ
⸨ P ∗ Q ⸩ᴮ {{∗-Basic}} =  ⸨ P ⸩ᴮ ∗ᵒ ⸨ Q ⸩ᴮ
⸨ P -∗ Q ⸩ᴮ {{ -∗-Basic}} =  ⸨ P ⸩ᴮ -∗ᵒ ⸨ Q ⸩ᴮ
⸨ □ P ⸩ᴮ {{□-Basic}} =  □ᵒ ⸨ P ⸩ᴮ
⸨ |=> P ⸩ᴮ {{|=>-Basic}} =  |=>ᵒ ⸨ P ⸩ᴮ
⸨ θ ↦⟨ q⁺ ⟩ av ⸩ᴮ {{↦⟨⟩-Basic}} =  λ _ → ⊤
⸨ Free n θ ⸩ᴮ {{Free-Basic}} =  λ _ → ⊤
