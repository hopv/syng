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
  ∧-assocʳ; ∧-elimʳ; ∗-monoˡ; ∗-monoʳ; ∗-comm; ∗?-comm; -∗-applyˡ)
open import Syho.Model.ERA.Inv using (_∙ᴵⁿᵛ_; inv; invk; inv-⌞⌟; invk-no2)
open import Syho.Model.ERA.Glob using (iᴵⁿᵛ)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; ∃ᵒ-syntax;
  ∃ᴵ-syntax; ⌜_⌝ᵒ×_; _×ᵒ_; ⊥ᵒ₀; _∗ᵒ_; □ᵒ_; ◎⟨_⟩_; ∃ᵒ-Mono; ∃ᴵ-Mono; ×ᵒ-Mono;
  ∗ᵒ⇒∗ᵒ'; ∗ᵒ'⇒∗ᵒ; ∗ᵒ-Mono; ∗ᵒ-mono; ∗ᵒ-monoˡ; ∗ᵒ-assocˡ; □ᵒ-Mono; □ᵒ-elim;
  □ᵒ-dup; dup-□ᵒ; ◎-Mono; ◎⟨⟩-∗ᵒ⇒∙; ◎⟨⟩-∙⇒∗ᵒ; ◎⟨⟩-⌞⌟≈-□ᵒ; ◎⟨⟩-✓)
open import Syho.Model.Prop.Basic using (⸨_⸩ᴮ; ⸨⸩ᴮ-Mono)

private variable
  i :  ℕ
  nm :  Name
  P Q R :  Prop∞

--------------------------------------------------------------------------------
-- &ⁱᵒ :  Interpret the invariant token

Inv :  ℕ →  Name →  Prop∞ →  Propᵒ 1ᴸ
Inv i nm P =  ◎⟨ iᴵⁿᵛ ⟩ inv i nm P

infix 8 &ⁱ⟨_⟩ᵒ_
&ⁱ⟨_⟩ᵒ_ :  Name →  Prop∞ →  Propᵒ 1ᴸ
&ⁱ⟨ nm ⟩ᵒ P =  ∃ᵒ i , ∃ᵒ Q , ∃ᴵ BasicQ , ∃ᵒ R ,
  ⌜ Q ∧ R ⊢[ ∞ ] P  ×  Q ∧ P ⊢[ ∞ ] R ⌝ᵒ×
  □ᵒ ⸨ Q ⸩ᴮ {{BasicQ}}  ×ᵒ  Inv i nm R

abstract

  -- Monoᵒ for &ⁱᵒ

  &ⁱᵒ-Mono :  Monoᵒ $ &ⁱ⟨ nm ⟩ᵒ P
  &ⁱᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ Q → ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ →
    ∃ᵒ-Mono λ _ → ×ᵒ-Mono (□ᵒ-Mono $ ⸨⸩ᴮ-Mono {Q}) ◎-Mono

  -- &ⁱ⟨ nm ⟩ᵒ P is persistent

  &ⁱᵒ-⇒□ᵒ :  &ⁱ⟨ nm ⟩ᵒ P  ⊨  □ᵒ &ⁱ⟨ nm ⟩ᵒ P
  &ⁱᵒ-⇒□ᵒ (-, Q , -ᴵ, -, Q∧|R⊣⊢P , □Qa , InvRa) =  -, -, -ᴵ, -, Q∧|R⊣⊢P ,
    □ᵒ-dup (⸨⸩ᴮ-Mono {Q}) □Qa , ◎⟨⟩-⌞⌟≈-□ᵒ inv-⌞⌟ InvRa

  -- Modify &ⁱᵒ using a persistent basic proposition

  &ⁱᵒ-resp-□ᵒ×ᵒ :  {{_ : Basic R}} →
    R  ∧  P  ⊢[ ∞ ]  Q  →   R  ∧  Q  ⊢[ ∞ ]  P  →
    □ᵒ ⸨ R ⸩ᴮ  ×ᵒ  &ⁱ⟨ nm ⟩ᵒ P  ⊨✓  &ⁱ⟨ nm ⟩ᵒ Q
  &ⁱᵒ-resp-□ᵒ×ᵒ {R = R} R∧P⊢Q R∧Q⊢P ✓a
    (□Ra , -, -, -ᴵ, -, (S∧T⊢P , S∧P⊢T) , □Sa , InvTa) = -, -, -ᴵ, -,
    -- (R∧S)∧T ⊢ R∧(S∧T) ⊢ R∧P ⊢ Q
    (∧-assocʳ » ∧-monoʳ S∧T⊢P » R∧P⊢Q ,
    -- (R∧S)∧Q ⊢ (S∧R)∧Q ⊢ S∧(R∧Q) ⊢ S∧P ⊢ T
    ∧-monoˡ ∧-comm » ∧-assocʳ » ∧-monoʳ R∧Q⊢P » S∧P⊢T) ,
    binary □Ra □Sa , InvTa

  -- Make &ⁱᵒ

  &ⁱᵒ-make :  Inv i nm P  ⊨  &ⁱ⟨ nm ⟩ᵒ P
  &ⁱᵒ-make Inva =  -, ⊤' , -ᴵ, -, (∧-elimʳ , ∧-elimʳ) , absurd , Inva

  -- Dubplicate &ⁱᵒ

  dup-&ⁱᵒ :  &ⁱ⟨ nm ⟩ᵒ P  ⊨  &ⁱ⟨ nm ⟩ᵒ P  ∗ᵒ  &ⁱ⟨ nm ⟩ᵒ P
  dup-&ⁱᵒ =  &ⁱᵒ-⇒□ᵒ › dup-□ᵒ &ⁱᵒ-Mono ›
    ∗ᵒ-mono (□ᵒ-elim &ⁱᵒ-Mono) (□ᵒ-elim &ⁱᵒ-Mono)

--------------------------------------------------------------------------------
-- Invk :  Invariant key

Invk :  ℕ →  Name →  Prop∞ →  Propᵒ 1ᴸ
Invk i nm P =  ◎⟨ iᴵⁿᵛ ⟩ invk i nm P

abstract

  -- Invk cannot overlap

  Invk-no2 :  Invk i nm P  ∗ᵒ  Invk i nm P  ⊨✓  ⊥ᵒ₀
  Invk-no2 ✓a =  ◎⟨⟩-∗ᵒ⇒∙ › ◎⟨⟩-✓ ✓a › λ (-, ✓invk²) →  invk-no2 ✓invk²

  -- Make &ⁱᵒ and Invk

  &ⁱᵒ-Invk-make :
    ◎⟨ iᴵⁿᵛ ⟩ (inv i nm P ∙ᴵⁿᵛ invk i nm P)  ⊨  &ⁱ⟨ nm ⟩ᵒ P  ∗ᵒ  Invk i nm P
  &ⁱᵒ-Invk-make =  ◎⟨⟩-∙⇒∗ᵒ › ∗ᵒ-monoˡ &ⁱᵒ-make

--------------------------------------------------------------------------------
-- %ⁱᵒ :  Interpret the open invariant token

infix 8 %ⁱ⟨_⟩ᵒ_
%ⁱ⟨_⟩ᵒ_ :  Name →  Prop∞ →  Propᵒ 1ᴸ
%ⁱ⟨ nm ⟩ᵒ P =  ∃ᵒ i , ∃ᵒ Q , ∃ᴵ BasicQ , ∃ᵒ R ,
  ⌜ Q ∗ P ⊢[ ∞ ] R ⌝ᵒ×  ⸨ Q ⸩ᴮ {{BasicQ}}  ∗ᵒ  Invk i nm R

abstract

  -- Monoᵒ for %ⁱᵒ

  %ⁱᵒ-Mono :  Monoᵒ $ %ⁱ⟨ nm ⟩ᵒ P
  %ⁱᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ Q → ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ →
    ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- Monotonicity of %ⁱᵒ

  %ⁱᵒ-mono :  P  ⊢[ ∞ ]  Q  →   %ⁱ⟨ nm ⟩ᵒ Q  ⊨  %ⁱ⟨ nm ⟩ᵒ P
  %ⁱᵒ-mono P⊢Q (-, -, -ᴵ, -, R∗Q⊢S , R∗InvkSa) =  -, -, -ᴵ, -,
    ∗-monoʳ P⊢Q » R∗Q⊢S , R∗InvkSa

  -- Let %ⁱᵒ eat a basic proposition

  %ⁱᵒ-eatˡ :  {{_ : Basic Q}} →  ⸨ Q ⸩ᴮ  ∗ᵒ  %ⁱ⟨ nm ⟩ᵒ P  ⊨  %ⁱ⟨ nm ⟩ᵒ (Q -∗ P)
  %ⁱᵒ-eatˡ =  ∗ᵒ⇒∗ᵒ' ›
    λ{ (-, -, b∙c⊑a , Qb , -, -, -ᴵ, -, R∗P⊢S , R∗InvkSc) →
    -, -, -ᴵ, -,
    -- (Q∗R)∗(Q-∗P) ⊢ (Q∗(Q-∗P))∗R ⊢ P∗R ⊢ R∗P ⊢ S
    ∗?-comm » ∗-monoˡ -∗-applyˡ » ∗-comm » R∗P⊢S ,
    ∗ᵒ-assocˡ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Qb , R∗InvkSc) }
