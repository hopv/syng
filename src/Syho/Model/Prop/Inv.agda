--------------------------------------------------------------------------------
-- Interpret the invariant and open invariant tokens
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Inv where

open import Base.Level using (1ᴸ)
open import Base.Func using (_$_; _▷_)
open import Base.Few using (binary)
open import Base.Eq using (refl)
open import Base.Size using (∞)
open import Base.Prod using (_×_; _,_; -,_; -ᴵ,_)
open import Syho.Logic.Prop using (Name; Prop∞; _∧_; Basic)
open import Syho.Logic.Core using (_⊢[_]_; _»_; ∧-monoˡ; ∧-monoʳ; ∧-comm;
  ∧-assocˡ)
open import Syho.Model.ERA.Inv using (inv; invk; inv-⌞⌟)
open import Syho.Model.ERA.Glob using (iᴵⁿᵛ)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; ∃ᵒ-syntax;
  ∃ᴵ-syntax; ⌜_⌝ᵒ×_; _×ᵒ_; □ᵒ_; ◎⟨_⟩_; ∃ᵒ-Mono; ∃ᴵ-Mono; ×ᵒ-Mono; □ᵒ-Mono;
  □ᵒ-dup; ◎-Mono; ◎⟨⟩-⌞⌟≈-□ᵒ)
open import Syho.Model.Prop.Basic using (⸨_⸩ᴮ; ⸨⸩ᴮ-Mono)

private variable
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
