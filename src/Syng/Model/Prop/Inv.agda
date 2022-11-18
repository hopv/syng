--------------------------------------------------------------------------------
-- Interpret the invariant and open invariant tokens
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syng.Model.Prop.Inv where

open import Base.Level using (1ᴸ)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Few using (⊤₀; absurd)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using (upd˙)
open import Base.Size using (∞)
open import Base.Option using (¿_; š_)
open import Base.Prod using (_×_; _,_; -,_; -ᴵ,_)
open import Base.Nat using (ℕ; ṡ_; _<_)
open import Syng.Logic.Prop using (Name; SProp∞; ⊤'; _∗_; _-∗_; Basic)
open import Syng.Logic.Core using (_⊢[_]_; _»_; ∗-monoˡ; ∗-monoʳ; ∗-comm;
  ∗-assocʳ; ∗?-comm; ∗-elimʳ; -∗-applyˡ)
open import Syng.Model.ERA.Inv using (NameSProp; _∙ᴵⁿᵛ_; inv; kinv; inv-⌞⌟;
  kinv-no2; inv-kinv-new; inv-agree; kinv-agree)
open import Syng.Model.ERA.Glob using (Envᴳ; iᴵⁿᵛ)
open import Syng.Model.Prop.Base using (SPropᵒ; Monoᵒ; _⊨✓_; _⊨_; ⊨_; ∃ᵒ-syntax;
  ∃ᴵ-syntax; ⌜_⌝ᵒ×_; _×ᵒ_; ⊥ᵒ₀; _∗ᵒ_; □ᵒ_; ⤇ᴱ⟨⟩; ◎⟨_⟩_; ∃ᵒ-Mono; ∃ᴵ-Mono;
  ×ᵒ-Mono; ∗ᵒ⇒∗ᵒ'; ∗ᵒ'⇒∗ᵒ; ∗ᵒ-Mono; ∗ᵒ-mono; ∗ᵒ-monoˡ; ∗ᵒ-assocˡ; ?∗ᵒ-intro;
  □ᵒ-dup; dup-⇒□ᵒ; □ᵒ-∗ᵒ-in; ⤇ᴱ⟨⟩-mono; ◎⟨⟩-∗ᵒ⇒∙; ◎⟨⟩-∙⇒∗ᵒ; ◎⟨⟩-⌞⌟≈-□ᵒ; ◎⟨⟩-✓;
  ↝-◎⟨⟩-⤇ᴱ⟨⟩; ε↝-◎⟨⟩-⤇ᴱ⟨⟩)
open import Syng.Model.Prop.Basic using (⸨_⸩ᴮ; ⸨⸩ᴮ-Mono)

private variable
  i n :  ℕ
  nm :  Name
  P Q R :  SProp∞
  ⁿQˇ˙ :  ℕ → ¿ NameSProp

--------------------------------------------------------------------------------
-- &ⁱᵒ :  Interpret the invariant token

-- Basic invariant token
Binv :  ℕ →  Name →  SProp∞ →  SPropᵒ 1ᴸ
Binv i nm P =  ◎⟨ iᴵⁿᵛ ⟩ inv i nm P

infix 8 &ⁱ⟨_⟩ᵒ_
&ⁱ⟨_⟩ᵒ_ :  Name →  SProp∞ →  SPropᵒ 1ᴸ
&ⁱ⟨ nm ⟩ᵒ P =  ∃ᵒ i , ∃ᵒ Q , ∃ᴵ BasicQ , ∃ᵒ R ,
  ⌜ Q ∗ R ⊢[ ∞ ] P  ×  Q ∗ P ⊢[ ∞ ] R ⌝ᵒ×
  □ᵒ ⸨ Q ⸩ᴮ {{BasicQ}}  ∗ᵒ  Binv i nm R

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

  &ⁱᵒ-make :  Binv i nm P  ⊨  &ⁱ⟨ nm ⟩ᵒ P
  &ⁱᵒ-make Inva =  -, ⊤' , -ᴵ, -, (∗-elimʳ , ∗-elimʳ) , ?∗ᵒ-intro absurd Inva

  -- Dubplicate &ⁱᵒ

  dup-&ⁱᵒ :  &ⁱ⟨ nm ⟩ᵒ P  ⊨  &ⁱ⟨ nm ⟩ᵒ P  ∗ᵒ  &ⁱ⟨ nm ⟩ᵒ P
  dup-&ⁱᵒ =  dup-⇒□ᵒ &ⁱᵒ-Mono &ⁱᵒ-⇒□ᵒ

  -- Agreement by Binv

  Binv-agree :  Binv i nm P  ⊨ (ⁿQˇ˙ , n) ⤇ᴱ⟨ iᴵⁿᵛ ⟩
    λ (_ :  i < n  ×  ⁿQˇ˙ i ≡ š (nm , P)) →  (ⁿQˇ˙ , n) ,  Binv i nm P
  Binv-agree =  ↝-◎⟨⟩-⤇ᴱ⟨⟩ inv-agree

--------------------------------------------------------------------------------
-- Kinv :  Invariant key

Kinv :  ℕ →  Name →  SProp∞ →  SPropᵒ 1ᴸ
Kinv i nm P =  ◎⟨ iᴵⁿᵛ ⟩ kinv i nm P

abstract

  -- Kinv cannot overlap

  Kinv-no2 :  Kinv i nm P  ∗ᵒ  Kinv i nm P  ⊨✓  ⊥ᵒ₀
  Kinv-no2 ✓a =  ◎⟨⟩-∗ᵒ⇒∙ › ◎⟨⟩-✓ ✓a › λ (-, ✓kinv²) →  kinv-no2 ✓kinv²

  -- Create &ⁱᵒ and Kinv

  &ⁱᵒ-Kinv-new :
    ⊨ (ⁿQˇ˙ , n) ⤇ᴱ⟨ iᴵⁿᵛ ⟩ λ (_ : ⊤₀) → (upd˙ n (š (nm , P)) ⁿQˇ˙ , ṡ n) ,
      &ⁱ⟨ nm ⟩ᵒ P  ∗ᵒ  Kinv n nm P
  &ⁱᵒ-Kinv-new =  ε↝-◎⟨⟩-⤇ᴱ⟨⟩ inv-kinv-new ▷
    ⤇ᴱ⟨⟩-mono λ _ → ◎⟨⟩-∙⇒∗ᵒ › ∗ᵒ-monoˡ &ⁱᵒ-make

  -- Agreement by Kinv

  Kinv-agree :
    Kinv i nm P  ⊨ (ⁿQˇ˙ , n) ⤇ᴱ⟨ iᴵⁿᵛ ⟩
      λ (_ :  i < n  ×  ⁿQˇ˙ i ≡ š (nm , P)) → (ⁿQˇ˙ , n) ,  Kinv i nm P
  Kinv-agree =  ↝-◎⟨⟩-⤇ᴱ⟨⟩ kinv-agree

--------------------------------------------------------------------------------
-- ⅋ⁱᵒ :  Interpret the open invariant token

infix 8 ⅋ⁱ⟨_⟩ᵒ_
⅋ⁱ⟨_⟩ᵒ_ :  Name →  SProp∞ →  SPropᵒ 1ᴸ
⅋ⁱ⟨ nm ⟩ᵒ P =  ∃ᵒ i , ∃ᵒ Q , ∃ᴵ BasicQ , ∃ᵒ R ,
  ⌜ Q ∗ P ⊢[ ∞ ] R ⌝ᵒ×  ⸨ Q ⸩ᴮ {{BasicQ}}  ∗ᵒ  Kinv i nm R

abstract

  -- Monoᵒ for ⅋ⁱᵒ

  ⅋ⁱᵒ-Mono :  Monoᵒ $ ⅋ⁱ⟨ nm ⟩ᵒ P
  ⅋ⁱᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ →
    ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- Monotonicity of ⅋ⁱᵒ

  ⅋ⁱᵒ-mono :  Q  ⊢[ ∞ ]  P  →   ⅋ⁱ⟨ nm ⟩ᵒ P  ⊨  ⅋ⁱ⟨ nm ⟩ᵒ Q
  ⅋ⁱᵒ-mono Q⊢P (-, -, -ᴵ, -, R∗P⊢S , R∗KinvSa) =  -, -, -ᴵ, -,
    ∗-monoʳ Q⊢P » R∗P⊢S , R∗KinvSa

  -- Let ⅋ⁱᵒ eat a basic proposition

  ⅋ⁱᵒ-eatˡ :  {{_ : Basic Q}} →  ⸨ Q ⸩ᴮ  ∗ᵒ  ⅋ⁱ⟨ nm ⟩ᵒ P  ⊨  ⅋ⁱ⟨ nm ⟩ᵒ (Q -∗ P)
  ⅋ⁱᵒ-eatˡ =  ∗ᵒ⇒∗ᵒ' › λ{ (-, -, b∙c⊑a , Qb , -, -, -ᴵ, -, R∗P⊢S , R∗KinvSc) →
    -, -, -ᴵ, -,
    -- (Q∗R)∗(Q-∗P) ⊢ (Q∗(Q-∗P))∗R ⊢ P∗R ⊢ R∗P ⊢ S
    ∗?-comm » ∗-monoˡ -∗-applyˡ » ∗-comm » R∗P⊢S ,
    ∗ᵒ-assocˡ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Qb , R∗KinvSc) }
