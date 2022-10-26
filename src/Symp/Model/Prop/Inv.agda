--------------------------------------------------------------------------------
-- Interpret the invariant and open invariant tokens
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Symp.Model.Prop.Inv where

open import Base.Level using (1ᴸ)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Few using (⊤₀; absurd)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using (upd˙)
open import Base.Size using (∞)
open import Base.Option using (¿_; š_)
open import Base.Prod using (_×_; _,_; -,_; -ᴵ,_)
open import Base.Nat using (ℕ; ṡ_; _<_)
open import Symp.Logic.Prop using (Name; SProp∞; ⊤'; _∗_; _-∗_; Basic)
open import Symp.Logic.Core using (_⊢[_]_; _»_; ∗-monoˡ; ∗-monoʳ; ∗-comm;
  ∗-assocʳ; ∗?-comm; ∗-elimʳ; -∗-applyˡ)
open import Symp.Model.ERA.Inv using (NameProp; _∙ᴵⁿᵛ_; inv; invk; inv-⌞⌟;
  invk-no2; inv-invk-new; inv-agree; invk-agree)
open import Symp.Model.ERA.Glob using (Envᴳ; iᴵⁿᵛ)
open import Symp.Model.Prop.Base using (SPropᵒ; Monoᵒ; _⊨✓_; _⊨_; ⊨_; ∃ᵒ-syntax;
  ∃ᴵ-syntax; ⌜_⌝ᵒ×_; _×ᵒ_; ⊥ᵒ₀; _∗ᵒ_; □ᵒ_; ⤇ᴱ⟨⟩; ◎⟨_⟩_; ∃ᵒ-Mono; ∃ᴵ-Mono;
  ×ᵒ-Mono; ∗ᵒ⇒∗ᵒ'; ∗ᵒ'⇒∗ᵒ; ∗ᵒ-Mono; ∗ᵒ-mono; ∗ᵒ-monoˡ; ∗ᵒ-assocˡ; ?∗ᵒ-intro;
  □ᵒ-dup; dup-⇒□ᵒ; □ᵒ-∗ᵒ-in; ⤇ᴱ⟨⟩-mono; ◎⟨⟩-∗ᵒ⇒∙; ◎⟨⟩-∙⇒∗ᵒ; ◎⟨⟩-⌞⌟≈-□ᵒ; ◎⟨⟩-✓;
  ↝-◎⟨⟩-⤇ᴱ⟨⟩; ε↝-◎⟨⟩-⤇ᴱ⟨⟩)
open import Symp.Model.Prop.Basic using (⸨_⸩ᴮ; ⸨⸩ᴮ-Mono)

private variable
  i n :  ℕ
  nm :  Name
  P Q R :  SProp∞
  ⁿQˇ˙ :  ℕ → ¿ NameProp

--------------------------------------------------------------------------------
-- &ⁱᵒ :  Interpret the invariant token

Inv :  ℕ →  Name →  SProp∞ →  SPropᵒ 1ᴸ
Inv i nm P =  ◎⟨ iᴵⁿᵛ ⟩ inv i nm P

infix 8 &ⁱ⟨_⟩ᵒ_
&ⁱ⟨_⟩ᵒ_ :  Name →  SProp∞ →  SPropᵒ 1ᴸ
&ⁱ⟨ nm ⟩ᵒ P =  ∃ᵒ i , ∃ᵒ Q , ∃ᴵ BasicQ , ∃ᵒ R ,
  ⌜ Q ∗ R ⊢[ ∞ ] P  ×  Q ∗ P ⊢[ ∞ ] R ⌝ᵒ×
  □ᵒ ⸨ Q ⸩ᴮ {{BasicQ}}  ∗ᵒ  Inv i nm R

abstract

  -- Monoᵒ for &ⁱᵒ

  &ⁱᵒ-Mono :  Monoᵒ $ &ⁱ⟨ nm ⟩ᵒ P
  &ⁱᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ →
    ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- &ⁱ⟨ nm ⟩ᵒ P is persistent

  &ⁱᵒ-⇒□ᵒ :  &ⁱ⟨ nm ⟩ᵒ P  ⊨  □ᵒ &ⁱ⟨ nm ⟩ᵒ P
  &ⁱᵒ-⇒□ᵒ (-, Q , -ᴵ, -, Q|R⊣⊢P , □Q∗InvRa) =  -, -, -ᴵ, -, Q|R⊣⊢P ,
    □Q∗InvRa ▷ ∗ᵒ-mono (□ᵒ-dup (⸨⸩ᴮ-Mono {Q})) (◎⟨⟩-⌞⌟≈-□ᵒ inv-⌞⌟) ▷ □ᵒ-∗ᵒ-in

  -- Modify &ⁱᵒ using a persistent basic proposition

  &ⁱᵒ-resp-□ᵒ∗ᵒ :  {{_ : Basic R}} →
    R  ∗  P  ⊢[ ∞ ]  Q  →   R  ∗  Q  ⊢[ ∞ ]  P  →
    □ᵒ ⸨ R ⸩ᴮ  ∗ᵒ  &ⁱ⟨ nm ⟩ᵒ P  ⊨  &ⁱ⟨ nm ⟩ᵒ Q
  &ⁱᵒ-resp-□ᵒ∗ᵒ R∗P⊢Q R∗Q⊢P =  ∗ᵒ⇒∗ᵒ' › λ{ (-, -, ∙⊑ , □Rb ,
    -, -, -ᴵ, -, (S∗T⊢P , S∗P⊢T) , □S*InvTc) →
    -, -, -ᴵ, -,
    -- (R∗S)∗T ⊢ R∗(S∗T) ⊢ R∗P ⊢ Q
    (∗-assocʳ » ∗-monoʳ S∗T⊢P » R∗P⊢Q ,
    -- (R∗S)∗Q ⊢ (S∗R)∗Q ⊢ S∗(R∗Q) ⊢ S∗P ⊢ T
    ∗-monoˡ ∗-comm » ∗-assocʳ » ∗-monoʳ R∗Q⊢P » S∗P⊢T) ,
    ∗ᵒ'⇒∗ᵒ (-, -, ∙⊑ , □Rb , □S*InvTc) ▷ ∗ᵒ-assocˡ ▷ ∗ᵒ-monoˡ □ᵒ-∗ᵒ-in }

  -- Make &ⁱᵒ

  &ⁱᵒ-make :  Inv i nm P  ⊨  &ⁱ⟨ nm ⟩ᵒ P
  &ⁱᵒ-make Inva =  -, ⊤' , -ᴵ, -, (∗-elimʳ , ∗-elimʳ) , ?∗ᵒ-intro absurd Inva

  -- Dubplicate &ⁱᵒ

  dup-&ⁱᵒ :  &ⁱ⟨ nm ⟩ᵒ P  ⊨  &ⁱ⟨ nm ⟩ᵒ P  ∗ᵒ  &ⁱ⟨ nm ⟩ᵒ P
  dup-&ⁱᵒ =  dup-⇒□ᵒ &ⁱᵒ-Mono &ⁱᵒ-⇒□ᵒ

  -- Agreement by Inv

  Inv-agree :
    Inv i nm P  ⊨ (ⁿQˇ˙ , n) ⤇ᴱ⟨ iᴵⁿᵛ ⟩ λ (_ :  i < n  ×  ⁿQˇ˙ i ≡ š (nm , P)) →
      (ⁿQˇ˙ , n) ,  Inv i nm P
  Inv-agree =  ↝-◎⟨⟩-⤇ᴱ⟨⟩ inv-agree

--------------------------------------------------------------------------------
-- Invk :  Invariant key

Invk :  ℕ →  Name →  SProp∞ →  SPropᵒ 1ᴸ
Invk i nm P =  ◎⟨ iᴵⁿᵛ ⟩ invk i nm P

abstract

  -- Invk cannot overlap

  Invk-no2 :  Invk i nm P  ∗ᵒ  Invk i nm P  ⊨✓  ⊥ᵒ₀
  Invk-no2 ✓a =  ◎⟨⟩-∗ᵒ⇒∙ › ◎⟨⟩-✓ ✓a › λ (-, ✓invk²) →  invk-no2 ✓invk²

  -- Create &ⁱᵒ and Invk

  &ⁱᵒ-Invk-new :
    ⊨ (ⁿQˇ˙ , n) ⤇ᴱ⟨ iᴵⁿᵛ ⟩ λ (_ : ⊤₀) → (upd˙ n (š (nm , P)) ⁿQˇ˙ , ṡ n) ,
      &ⁱ⟨ nm ⟩ᵒ P  ∗ᵒ  Invk n nm P
  &ⁱᵒ-Invk-new =  ε↝-◎⟨⟩-⤇ᴱ⟨⟩ inv-invk-new ▷
    ⤇ᴱ⟨⟩-mono λ _ → ◎⟨⟩-∙⇒∗ᵒ › ∗ᵒ-monoˡ &ⁱᵒ-make

  -- Agreement by Invk

  Invk-agree :
    Invk i nm P  ⊨ (ⁿQˇ˙ , n) ⤇ᴱ⟨ iᴵⁿᵛ ⟩
      λ (_ :  i < n  ×  ⁿQˇ˙ i ≡ š (nm , P)) → (ⁿQˇ˙ , n) ,  Invk i nm P
  Invk-agree =  ↝-◎⟨⟩-⤇ᴱ⟨⟩ invk-agree

--------------------------------------------------------------------------------
-- ⅋ⁱᵒ :  Interpret the open invariant token

infix 8 ⅋ⁱ⟨_⟩ᵒ_
⅋ⁱ⟨_⟩ᵒ_ :  Name →  SProp∞ →  SPropᵒ 1ᴸ
⅋ⁱ⟨ nm ⟩ᵒ P =  ∃ᵒ i , ∃ᵒ Q , ∃ᴵ BasicQ , ∃ᵒ R ,
  ⌜ Q ∗ P ⊢[ ∞ ] R ⌝ᵒ×  ⸨ Q ⸩ᴮ {{BasicQ}}  ∗ᵒ  Invk i nm R

abstract

  -- Monoᵒ for ⅋ⁱᵒ

  ⅋ⁱᵒ-Mono :  Monoᵒ $ ⅋ⁱ⟨ nm ⟩ᵒ P
  ⅋ⁱᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ →
    ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- Monotonicity of ⅋ⁱᵒ

  ⅋ⁱᵒ-mono :  P  ⊢[ ∞ ]  Q  →   ⅋ⁱ⟨ nm ⟩ᵒ Q  ⊨  ⅋ⁱ⟨ nm ⟩ᵒ P
  ⅋ⁱᵒ-mono P⊢Q (-, -, -ᴵ, -, R∗Q⊢S , R∗InvkSa) =  -, -, -ᴵ, -,
    ∗-monoʳ P⊢Q » R∗Q⊢S , R∗InvkSa

  -- Let ⅋ⁱᵒ eat a basic proposition

  ⅋ⁱᵒ-eatˡ :  {{_ : Basic Q}} →  ⸨ Q ⸩ᴮ  ∗ᵒ  ⅋ⁱ⟨ nm ⟩ᵒ P  ⊨  ⅋ⁱ⟨ nm ⟩ᵒ (Q -∗ P)
  ⅋ⁱᵒ-eatˡ =  ∗ᵒ⇒∗ᵒ' › λ{ (-, -, b∙c⊑a , Qb , -, -, -ᴵ, -, R∗P⊢S , R∗InvkSc) →
    -, -, -ᴵ, -,
    -- (Q∗R)∗(Q-∗P) ⊢ (Q∗(Q-∗P))∗R ⊢ P∗R ⊢ R∗P ⊢ S
    ∗?-comm » ∗-monoˡ -∗-applyˡ » ∗-comm » R∗P⊢S ,
    ∗ᵒ-assocˡ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Qb , R∗InvkSc) }
