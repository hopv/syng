--------------------------------------------------------------------------------
-- Interpret the invariant and open invariant tokens
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Inv where

open import Base.Level using (1ᴸ)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Few using (binary; absurd)
open import Base.Eq using (refl)
open import Base.Size using (∞)
open import Base.Prod using (_×_; _,_; -,_; -ᴵ,_)
open import Base.Nat using (ℕ)
open import Syho.Logic.Prop using (Name; Prop∞; _∧_; ⊤'; _∗_; _-∗_; Basic)
open import Syho.Logic.Core using (_⊢[_]_; _»_; ∧-monoˡ; ∧-monoʳ; ∧-comm;
  ∧-assocˡ; ∧-elimʳ; ∗-monoˡ; ∗-monoʳ; ∗-comm; ∗-assocˡ; ∗?-comm; -∗-apply)
open import Syho.Model.ERA.Inv using (_∙ᴵⁿᵛ_; inv; invk; inv-⌞⌟; invk-no2)
open import Syho.Model.ERA.Glob using (iᴵⁿᵛ)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; ∃ᵒ-syntax;
  ∃ᴵ-syntax; ⌜_⌝ᵒ×_; _×ᵒ_; ⊥ᵒ₀; _∗ᵒ_; □ᵒ_; ◎⟨_⟩_; ∃ᵒ-Mono; ∃ᴵ-Mono; ×ᵒ-Mono;
  ∗ᵒ-Mono; ∗ᵒ⇒∗ᵒ'; ∗ᵒ'⇒∗ᵒ; ∗ᵒ-mono; ∗ᵒ-monoˡ; ∗ᵒ-assocʳ; □ᵒ-Mono; □ᵒ-elim;
  □ᵒ-dup; dup-□ᵒ; ◎-Mono; ◎⟨⟩-∗ᵒ⇒∙; ◎⟨⟩-∙⇒∗ᵒ; ◎⟨⟩-⌞⌟≈-□ᵒ; ◎⟨⟩-✓)
open import Syho.Model.Prop.Basic using (⸨_⸩ᴮ; ⸨⸩ᴮ-Mono)

private variable
  i :  ℕ
  nm :  Name
  P Q R :  Prop∞

--------------------------------------------------------------------------------
-- Invᵒ :  Interpret the invariant token

Invᵒ :  Name →  Prop∞ →  Propᵒ 1ᴸ
Invᵒ nm P =  ∃ᵒ i , ∃ᵒ Q , ∃ᴵ BasicQ , ∃ᵒ R ,
  ⌜ Q ∧ R ⊢[ ∞ ] P  ×  Q ∧ P ⊢[ ∞ ] R ⌝ᵒ×
  □ᵒ ⸨ Q ⸩ᴮ {{BasicQ}}  ×ᵒ  ◎⟨ iᴵⁿᵛ ⟩ inv i nm R

abstract

  -- Monoᵒ for Invᵒ

  Invᵒ-Mono :  Monoᵒ $ Invᵒ nm P
  Invᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ Q → ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ →
    ∃ᵒ-Mono λ _ → ×ᵒ-Mono (□ᵒ-Mono $ ⸨⸩ᴮ-Mono {Q}) ◎-Mono

  -- Invᵒ nm P is persistent

  Invᵒ-⇒□ᵒ :  Invᵒ nm P  ⊨  □ᵒ Invᵒ nm P
  Invᵒ-⇒□ᵒ (-, Q , -ᴵ, -, Q∧|R⊣⊢P , □Qa , invRa) =  -, -, -ᴵ, -, Q∧|R⊣⊢P ,
    □ᵒ-dup (⸨⸩ᴮ-Mono {Q}) □Qa , ◎⟨⟩-⌞⌟≈-□ᵒ inv-⌞⌟ invRa

  -- Change the proposition of Invᵒ with a persistent basic proposition

  Invᵒ-resp-□ᵒ×ᵒ :  {{_ : Basic R}} →
    R  ∧  P  ⊢[ ∞ ]  Q  →   R  ∧  Q  ⊢[ ∞ ]  P  →
    □ᵒ ⸨ R ⸩ᴮ  ×ᵒ  Invᵒ nm P  ⊨✓  Invᵒ nm Q
  Invᵒ-resp-□ᵒ×ᵒ {R = R} R∧P⊢Q R∧Q⊢P ✓a
    (□Ra , -, -, -ᴵ, -, (S∧T⊢P , S∧P⊢T) , □Sa , invTa) = -, -, -ᴵ, -,
    -- (R∧S)∧T ⊢ R∧(S∧T) ⊢ R∧P ⊢ Q
    (∧-assocˡ » ∧-monoʳ S∧T⊢P » R∧P⊢Q ,
    -- (R∧S)∧Q ⊢ (S∧R)∧Q ⊢ S∧(R∧Q) ⊢ S∧P ⊢ T
    ∧-monoˡ ∧-comm » ∧-assocˡ » ∧-monoʳ R∧Q⊢P » S∧P⊢T) ,
    binary □Ra □Sa , invTa

  -- Make Invᵒ

  Invᵒ-make :  ◎⟨ iᴵⁿᵛ ⟩ inv i nm P  ⊨  Invᵒ nm P
  Invᵒ-make inva =  -, ⊤' , -ᴵ, -, (∧-elimʳ , ∧-elimʳ) , absurd , inva

  -- Dubplicate Invᵒ

  dup-Invᵒ :  Invᵒ nm P  ⊨  Invᵒ nm P  ∗ᵒ  Invᵒ nm P
  dup-Invᵒ =  Invᵒ-⇒□ᵒ › dup-□ᵒ Invᵒ-Mono ›
    ∗ᵒ-mono (□ᵒ-elim Invᵒ-Mono) (□ᵒ-elim Invᵒ-Mono)

--------------------------------------------------------------------------------
-- Invk :  Invariant key

Invk :  ℕ →  Name →  Prop∞ →  Propᵒ 1ᴸ
Invk i nm P =  ◎⟨ iᴵⁿᵛ ⟩ invk i nm P

abstract

  -- Invk cannot overlap

  Invk-no2 :  Invk i nm P  ∗ᵒ  Invk i nm P  ⊨✓  ⊥ᵒ₀
  Invk-no2 ✓a =  ◎⟨⟩-∗ᵒ⇒∙ › ◎⟨⟩-✓ ✓a › λ (-, ✓invk²) →  invk-no2 ✓invk²

  -- Make Invᵒ ∗ᵒ Invk

  Invᵒ∗ᵒInvk-make :
    ◎⟨ iᴵⁿᵛ ⟩ (inv i nm P ∙ᴵⁿᵛ invk i nm P)  ⊨  Invᵒ nm P  ∗ᵒ  Invk i nm P
  Invᵒ∗ᵒInvk-make =  ◎⟨⟩-∙⇒∗ᵒ › ∗ᵒ-monoˡ Invᵒ-make

--------------------------------------------------------------------------------
-- OInvᵒ :  Interpret the open invariant token

OInvᵒ :  Name →  Prop∞ →  Propᵒ 1ᴸ
OInvᵒ nm P =  ∃ᵒ i , ∃ᵒ Q , ∃ᴵ BasicQ , ∃ᵒ R ,
  ⌜ Q ∗ P ⊢[ ∞ ] R ⌝ᵒ×  ⸨ Q ⸩ᴮ {{BasicQ}}  ∗ᵒ  Invk i nm R

abstract

  -- Monoᵒ for OInvᵒ

  OInvᵒ-Mono :  Monoᵒ $ OInvᵒ nm P
  OInvᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ Q → ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ →
    ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- Monotonicity of OInvᵒ

  OInvᵒ-mono :  P  ⊢[ ∞ ]  Q  →   OInvᵒ nm Q  ⊨  OInvᵒ nm P
  OInvᵒ-mono P⊢Q (-, -, -ᴵ, -, R∗Q⊢S , R∗InvkSa) =  -, -, -ᴵ, -,
    ∗-monoʳ P⊢Q » R∗Q⊢S , R∗InvkSa

  -- Let OInvᵒ eat a basic proposition

  OInvᵒ-eatˡ :  {{_ : Basic Q}} →  ⸨ Q ⸩ᴮ  ∗ᵒ  OInvᵒ nm P  ⊨  OInvᵒ nm (Q -∗ P)
  OInvᵒ-eatˡ =  ∗ᵒ⇒∗ᵒ' ›
    λ{ (-, -, b∙c⊑a , Qb , -, -, -ᴵ, -, R∗P⊢S , R∗InvkSc) →
    -, -, -ᴵ, -,
    -- (Q∗R)∗(Q-∗P) ⊢ (Q∗(Q-∗P))∗R ⊢ P∗R ⊢ R∗P ⊢ S
    ∗?-comm » ∗-monoˡ -∗-apply » ∗-comm » R∗P⊢S ,
    ∗ᵒ-assocʳ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Qb , R∗InvkSc) }
