--------------------------------------------------------------------------------
-- Interpret the borrow-related tokens
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Bor where

open import Base.Level using (1ᴸ)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Few using (⊤₀; absurd)
open import Base.Eq using (_≡_)
open import Base.Dec using (upd˙)
open import Base.Size using (∞)
open import Base.Bool using (tt; ff)
open import Base.Option using (š_; ň)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_; _,-; -ᴵ,_)
open import Base.Nat using (ℕ; ṡ_; _<_)
open import Base.Ratp using (ℚ⁺; _≈ᴿ⁺_; _/2⁺; ≈ᴿ⁺-sym; ≈ᴿ⁺-trans)
open import Syho.Logic.Prop using (Lft; Prop∞; ⊤'; _∗_; _-∗_; Basic)
open import Syho.Logic.Core using (_⊢[_]_; _»_; ∗-monoˡ; ∗-monoʳ; ∗-comm;
  ∗-assocʳ; ∗?-comm; ∗-elimʳ; -∗-applyˡ)
open import Syho.Model.ERA.Bor using (Envᴮᵒʳᵇ; εᴮᵒʳ; borᵐ; oborᵐ; lend;
  borᵐ-new; borᵐ-open; oborᵐ-close; lend-back)
open import Syho.Model.ERA.Glob using (iᴮᵒʳ)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; ⊨_; ∃ᵒ-syntax;
  ∃ᴵ-syntax; ⌜_⌝ᵒ×_; ⊤ᵒ₀; _∗ᵒ_; □ᵒ_; ⤇ᴱ⟨⟩; ◎⟨_⟩_; ∃ᵒ-Mono; ∃ᴵ-Mono; ∗ᵒ⇒∗ᵒ';
  ∗ᵒ'⇒∗ᵒ; ∗ᵒ-Mono; ∗ᵒ-mono; ∗ᵒ-monoˡ; ∗ᵒ-assocˡ; ?∗ᵒ-intro; □ᵒ-∗ᵒ-in; ⤇ᴱ⟨⟩-mono;
  ◎⟨⟩-∙⇒∗ᵒ; ↝-◎⟨⟩-⤇ᴱ⟨⟩; ε↝-◎⟨⟩-⤇ᴱ⟨⟩)
open import Syho.Model.Prop.Lft using ([_]ᴸ⟨_⟩ᵒ)
open import Syho.Model.Prop.Basic using (⸨_⸩ᴮ; ⸨⸩ᴮ-Mono)

private variable
  i n :  ℕ
  α :  Lft
  p q :  ℚ⁺
  P Q R :  Prop∞
  E˙ :  ℕ → Envᴮᵒʳᵇ

--------------------------------------------------------------------------------
-- &ᵐᵒ :  Interpret the mutable borrow token

Borᵐ :  ℕ →  Lft →  Prop∞ →  Propᵒ 1ᴸ
Borᵐ i α P =  ◎⟨ iᴮᵒʳ ⟩ borᵐ i α P

infix 8 &ᵐ⟨_⟩ᵒ_
&ᵐ⟨_⟩ᵒ_ :  Lft →  Prop∞ →  Propᵒ 1ᴸ
&ᵐ⟨ α ⟩ᵒ P =  ∃ᵒ i , ∃ᵒ Q , ∃ᴵ BasicQ , ∃ᵒ R ,
  ⌜ Q ∗ R ⊢[ ∞ ] P  ×  Q ∗ P ⊢[ ∞ ] R ⌝ᵒ×
  □ᵒ ⸨ Q ⸩ᴮ {{BasicQ}}  ∗ᵒ  Borᵐ i α R

abstract

  -- Monoᵒ for &ᵐᵒ

  &ᵐᵒ-Mono :  Monoᵒ $ &ᵐ⟨ α ⟩ᵒ P
  &ᵐᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ →
    ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- Modify &ᵐᵒ using a persistent basic proposition

  &ᵐᵒ-resp-□ᵒ∗ᵒ :  {{_ : Basic R}} →
    R  ∗  P  ⊢[ ∞ ]  Q  →   R  ∗  Q  ⊢[ ∞ ]  P  →
    □ᵒ ⸨ R ⸩ᴮ  ∗ᵒ  &ᵐ⟨ α ⟩ᵒ P  ⊨  &ᵐ⟨ α ⟩ᵒ Q
  &ᵐᵒ-resp-□ᵒ∗ᵒ R∗P⊢Q R∗Q⊢P =  ∗ᵒ⇒∗ᵒ' › λ{ (-, -, ∙⊑ , □Rb ,
    -, -, -ᴵ, -, (S∗T⊢P , S∗P⊢T) , □S*BorTc) →
    -, -, -ᴵ, -,
    -- (R∗S)∗T ⊢ R∗(S∗T) ⊢ R∗P ⊢ Q
    (∗-assocʳ » ∗-monoʳ S∗T⊢P » R∗P⊢Q ,
    -- (R∗S)∗Q ⊢ (S∗R)∗Q ⊢ S∗(R∗Q) ⊢ S∗P ⊢ T
    ∗-monoˡ ∗-comm » ∗-assocʳ » ∗-monoʳ R∗Q⊢P » S∗P⊢T) ,
    ∗ᵒ'⇒∗ᵒ (-, -, ∙⊑ , □Rb , □S*BorTc) ▷ ∗ᵒ-assocˡ ▷ ∗ᵒ-monoˡ □ᵒ-∗ᵒ-in }

  -- Make &ᵐᵒ out of Borᵐ

  &ᵐᵒ-make :  Borᵐ i α P  ⊨  &ᵐ⟨ α ⟩ᵒ P
  &ᵐᵒ-make Bora =  -, ⊤' , -ᴵ, -, (∗-elimʳ , ∗-elimʳ) , ?∗ᵒ-intro absurd Bora

--------------------------------------------------------------------------------
-- %ᵐᵒ :  Interpret the open mutable borrow token

Oborᵐ :  ℕ →  Lft →  ℚ⁺ →  Prop∞ →  Propᵒ 1ᴸ
Oborᵐ i α p P =  ◎⟨ iᴮᵒʳ ⟩ oborᵐ i α p P

infix 8 %ᵐ⟨_⟩ᵒ_
%ᵐ⟨_⟩ᵒ_ :  Lft × ℚ⁺ →  Prop∞ →  Propᵒ 1ᴸ
%ᵐ⟨ α , p ⟩ᵒ P =  ∃ᵒ i , ∃ᵒ q , ∃ᵒ Q , ∃ᴵ BasicQ , ∃ᵒ R ,
  ⌜ p ≈ᴿ⁺ q  ×  Q ∗ R ⊢[ ∞ ] P  ×  Q ∗ P ⊢[ ∞ ] R ⌝ᵒ×
  □ᵒ ⸨ Q ⸩ᴮ {{BasicQ}}  ∗ᵒ  [ α ]ᴸ⟨ q /2⁺ ⟩ᵒ  ∗ᵒ  Oborᵐ i α q R

abstract

  -- Monoᵒ for %ᵐᵒ

  %ᵐᵒ-Mono :  Monoᵒ $ %ᵐ⟨ α , p ⟩ᵒ P
  %ᵐᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ →
    ∃ᵒ-Mono λ _ → ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- Modify the fraction of %ᵐᵒ

  %ᵐᵒ-respᴿ :  p ≈ᴿ⁺ q  →   %ᵐ⟨ α , p ⟩ᵒ P  ⊨  %ᵐ⟨ α , q ⟩ᵒ P
  %ᵐᵒ-respᴿ {p} {q} p≈q (-, r , -, -ᴵ, -, (p≈r , Q|R⊢⊣P) , QαObor) =  -, -, -,
    -ᴵ, -, (≈ᴿ⁺-trans {q} {p} {r} (≈ᴿ⁺-sym {p} {q} p≈q) p≈r , Q|R⊢⊣P) , QαObor

  -- Modify %ᵐᵒ using a persistent basic proposition

  %ᵐᵒ-respᴾ-□ᵒ∗ᵒ :  {{_ : Basic R}} →
    R  ∗  P  ⊢[ ∞ ]  Q  →   R  ∗  Q  ⊢[ ∞ ]  P  →
    □ᵒ ⸨ R ⸩ᴮ  ∗ᵒ  %ᵐ⟨ α , p ⟩ᵒ P  ⊨  %ᵐ⟨ α , p ⟩ᵒ Q
  %ᵐᵒ-respᴾ-□ᵒ∗ᵒ R∗P⊢Q R∗Q⊢P =  ∗ᵒ⇒∗ᵒ' › λ{ (-, -, ∙⊑ , □Rb ,
    -, -, -, -ᴵ, -, (p≈q , S∗T⊢P , S∗P⊢T) , □S∗α∗OborTc) →
    -, -, -, -ᴵ, -, (p≈q ,
    -- (R∗S)∗T ⊢ R∗(S∗T) ⊢ R∗P ⊢ Q
    ∗-assocʳ » ∗-monoʳ S∗T⊢P » R∗P⊢Q ,
    -- (R∗S)∗Q ⊢ (S∗R)∗Q ⊢ S∗(R∗Q) ⊢ S∗P ⊢ T
    ∗-monoˡ ∗-comm » ∗-assocʳ » ∗-monoʳ R∗Q⊢P » S∗P⊢T) ,
    ∗ᵒ'⇒∗ᵒ (-, -, ∙⊑ , □Rb , □S∗α∗OborTc) ▷ ∗ᵒ-assocˡ ▷ ∗ᵒ-monoˡ □ᵒ-∗ᵒ-in }

  -- Open using Borᵐ

  Borᵐ-open' :
    Borᵐ i α P  ⊨ (E˙ , n) ⤇ᴱ⟨ iᴮᵒʳ ⟩
      λ ((-, (b ,-)) :  i < n  ×  (∑ b , E˙ i ≡ š (ň , b , α , P))) →
      (upd˙ i (š (š p , b , α , P)) E˙ , n) , Oborᵐ i α p P
  Borᵐ-open' =  ↝-◎⟨⟩-⤇ᴱ⟨⟩ borᵐ-open

  -- Close using Oborᵐ

  Oborᵐ-close' :
    Oborᵐ i α p P  ⊨ (E˙ , n) ⤇ᴱ⟨ iᴮᵒʳ ⟩
      λ ((-, (b ,-)) :  i < n  ×  (∑ b , E˙ i ≡ š (š p , b , α , P))) →
      (upd˙ i (š (ň , b , α , P)) E˙ , n) , Borᵐ i α P
  Oborᵐ-close' =  ↝-◎⟨⟩-⤇ᴱ⟨⟩ oborᵐ-close

--------------------------------------------------------------------------------
-- ⟨†⟩ᵒ :  Interpret the lending token

Lend :  ℕ →  Lft →  Prop∞ →  Propᵒ 1ᴸ
Lend i α P =  ◎⟨ iᴮᵒʳ ⟩ lend i α P

infix 8 ⟨†_⟩ᵒ_
⟨†_⟩ᵒ_ :  Lft →  Prop∞ →  Propᵒ 1ᴸ
⟨† α ⟩ᵒ P =  ∃ᵒ i , ∃ᵒ Q , ∃ᴵ BasicQ , ∃ᵒ R ,
  ⌜ Q ∗ R ⊢[ ∞ ] P ⌝ᵒ×  ⸨ Q ⸩ᴮ {{BasicQ}}  ∗ᵒ  Lend i α R

abstract

  -- Monoᵒ for ⟨†⟩ᵒ

  ⟨†⟩ᵒ-Mono :  Monoᵒ $ ⟨† α ⟩ᵒ P
  ⟨†⟩ᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ →
    ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- Monotonicity of ⟨†⟩ᵒ

  ⟨†⟩ᵒ-mono :  P ⊢[ ∞ ] Q  →   ⟨† α ⟩ᵒ P  ⊨  ⟨† α ⟩ᵒ Q
  ⟨†⟩ᵒ-mono P⊢Q (-, -, -ᴵ, -, R∗S⊢P , R∗LendSa) =
    -, -, -ᴵ, -, R∗S⊢P » P⊢Q , R∗LendSa

  -- Let ⟨†⟩ᵒ eat a proposition under ∗ᵒ

  ⟨†⟩ᵒ-eatˡ :  {{_ : Basic Q}}  →  ⸨ Q ⸩ᴮ  ∗ᵒ  ⟨† α ⟩ᵒ P  ⊨  ⟨† α ⟩ᵒ (Q ∗ P)
  ⟨†⟩ᵒ-eatˡ =  ∗ᵒ⇒∗ᵒ' › λ{ (-, -, b∙c⊑a , Qb , -, -, -ᴵ, -, R∗S⊢P , R∗LendSc) →
    -, -, -ᴵ, -, ∗-assocʳ » ∗-monoʳ R∗S⊢P ,
    ∗ᵒ-assocˡ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Qb , R∗LendSc) }

  -- Make ⟨†⟩ᵒ out of Lend

  ⟨†⟩ᵒ-make :  Lend i α P  ⊨  ⟨† α ⟩ᵒ P
  ⟨†⟩ᵒ-make LendPa =  -, ⊤' , -ᴵ, -, ∗-elimʳ , ?∗ᵒ-intro absurd LendPa

  -- Create &ᵐᵒ and ⟨†⟩ᵒ

  &ᵐᵒ-new' :
    ⊨ (E˙ , n) ⤇ᴱ⟨ iᴮᵒʳ ⟩ λ (_ : ⊤₀) → (upd˙ n (š (ň , tt , α , P)) E˙ , ṡ n) ,
      &ᵐ⟨ α ⟩ᵒ P  ∗ᵒ  ⟨† α ⟩ᵒ P
  &ᵐᵒ-new' =  ε↝-◎⟨⟩-⤇ᴱ⟨⟩ borᵐ-new ▷
    ⤇ᴱ⟨⟩-mono λ _ → ◎⟨⟩-∙⇒∗ᵒ › ∗ᵒ-mono &ᵐᵒ-make ⟨†⟩ᵒ-make

  -- Update the state using Lend

  Lend-back' :
    Lend i α P  ⊨ (E˙ , n) ⤇ᴱ⟨ iᴮᵒʳ ⟩
      λ ((-, (pˇ ,-)) :  i < n  ×  (∑ pˇ , E˙ i ≡ š (pˇ , tt , α , P))) →
      (upd˙ i (š (pˇ , ff , α , P)) E˙ , n) , ⊤ᵒ₀
  Lend-back' =  ↝-◎⟨⟩-⤇ᴱ⟨⟩ {bⁱ˙ = λ _ → εᴮᵒʳ} lend-back › ⤇ᴱ⟨⟩-mono _
