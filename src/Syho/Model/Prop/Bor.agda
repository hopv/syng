--------------------------------------------------------------------------------
-- Interpret the borrow-related tokens
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Bor where

open import Base.Level using (1ᴸ)
open import Base.Func using (_$_; _›_)
open import Base.Few using (binary; absurd)
open import Base.Size using (∞)
open import Base.Prod using (_×_; _,_; -,_; -ᴵ,_)
open import Base.Nat using (ℕ)
open import Base.Ratp using (ℚ⁺; _≈ᴿ⁺_; _/2⁺; ≈ᴿ⁺-sym; ≈ᴿ⁺-trans)
open import Syho.Logic.Prop using (Lft; Prop∞; _∧_; ⊤'; _∗_; _-∗_; Basic)
open import Syho.Logic.Core using (_⊢[_]_; _»_; ∧-monoˡ; ∧-monoʳ; ∧-comm;
  ∧-assocʳ; ∧-elimʳ; ∗-monoˡ; ∗-monoʳ; ∗-comm; ∗-assocʳ; ∗?-comm; ∗-elimʳ;
  -∗-applyˡ)
open import Syho.Model.ERA.Bor using (_∙ᴮᵒʳ_; borᵐ; oborᵐ; lend; borᵐ-lend-new;
  borᵐ-open; oborᵐ-close; lend-back)
open import Syho.Model.ERA.Glob using (iᴮᵒʳ)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; ∃ᵒ-syntax;
  ∃ᴵ-syntax; ⌜_⌝ᵒ×_; _×ᵒ_; _∗ᵒ_; □ᵒ_; ◎⟨_⟩_; ∃ᵒ-Mono; ∃ᴵ-Mono; ×ᵒ-Mono; □ᵒ-Mono;
  ∗ᵒ⇒∗ᵒ'; ∗ᵒ'⇒∗ᵒ; ∗ᵒ-Mono; ∗ᵒ-mono; ∗ᵒ-assocˡ; ?∗ᵒ-intro; ◎-Mono; ◎⟨⟩-∙⇒∗ᵒ)
open import Syho.Model.Prop.Lft using ([_]ᴸ⟨_⟩ᵒ)
open import Syho.Model.Prop.Basic using (⸨_⸩ᴮ; ⸨⸩ᴮ-Mono)

private variable
  i :  ℕ
  α :  Lft
  p q :  ℚ⁺
  P Q R :  Prop∞

--------------------------------------------------------------------------------
-- &ᵐᵒ :  Interpret the mutable borrow token

Borᵐ :  ℕ →  Lft →  Prop∞ →  Propᵒ 1ᴸ
Borᵐ i α P =  ◎⟨ iᴮᵒʳ ⟩ borᵐ i α P

infix 8 &ᵐ⟨_⟩ᵒ_
&ᵐ⟨_⟩ᵒ_ :  Lft →  Prop∞ →  Propᵒ 1ᴸ
&ᵐ⟨ α ⟩ᵒ P =  ∃ᵒ i , ∃ᵒ Q , ∃ᴵ BasicQ , ∃ᵒ R ,
  ⌜ Q ∧ R ⊢[ ∞ ] P  ×  Q ∧ P ⊢[ ∞ ] R ⌝ᵒ×
  □ᵒ ⸨ Q ⸩ᴮ {{BasicQ}}  ×ᵒ  Borᵐ i α R

abstract

  -- Monoᵒ for &ᵐᵒ

  &ᵐᵒ-Mono :  Monoᵒ $ &ᵐ⟨ α ⟩ᵒ P
  &ᵐᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ Q → ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ →
    ∃ᵒ-Mono λ _ → ×ᵒ-Mono (□ᵒ-Mono $ ⸨⸩ᴮ-Mono {Q}) ◎-Mono

  -- Modify &ᵐᵒ using a persistent basic proposition

  &ᵐᵒ-resp-□ᵒ×ᵒ :  {{_ : Basic R}} →
    R  ∧  P  ⊢[ ∞ ]  Q  →   R  ∧  Q  ⊢[ ∞ ]  P  →
    □ᵒ ⸨ R ⸩ᴮ  ×ᵒ  &ᵐ⟨ α ⟩ᵒ P  ⊨  &ᵐ⟨ α ⟩ᵒ Q
  &ᵐᵒ-resp-□ᵒ×ᵒ R∧P⊢Q R∧Q⊢P (□Ra , -, -, -ᴵ, -, (S∧T⊢P , S∧P⊢T) , □Sa , BorTa) =
    -, -, -ᴵ, -,
    -- (R∧S)∧T ⊢ R∧(S∧T) ⊢ R∧P ⊢ Q
    (∧-assocʳ » ∧-monoʳ S∧T⊢P » R∧P⊢Q ,
    -- (R∧S)∧Q ⊢ (S∧R)∧Q ⊢ S∧(R∧Q) ⊢ S∧P ⊢ T
    ∧-monoˡ ∧-comm » ∧-assocʳ » ∧-monoʳ R∧Q⊢P » S∧P⊢T) ,
    binary □Ra □Sa , BorTa

  -- Make &ᵐᵒ out of Borᵐ

  &ᵐᵒ-make :  Borᵐ i α P  ⊨  &ᵐ⟨ α ⟩ᵒ P
  &ᵐᵒ-make Bora =  -, ⊤' , -ᴵ, -, (∧-elimʳ , ∧-elimʳ) , absurd , Bora

--------------------------------------------------------------------------------
-- %ᵐᵒ :  Interpret the open mutable borrow token

Oborᵐ :  ℕ →  Lft →  ℚ⁺ →  Prop∞ →  Propᵒ 1ᴸ
Oborᵐ i α p P =  ◎⟨ iᴮᵒʳ ⟩ oborᵐ i α p P

infix 8 %ᵐ⟨_⟩ᵒ_
%ᵐ⟨_⟩ᵒ_ :  Lft × ℚ⁺ →  Prop∞ →  Propᵒ 1ᴸ
%ᵐ⟨ α , p ⟩ᵒ P =  ∃ᵒ i , ∃ᵒ q , ∃ᵒ Q , ∃ᴵ BasicQ , ∃ᵒ R ,
  ⌜ p ≈ᴿ⁺ q  ×  Q ∗ P ⊢[ ∞ ] R ⌝ᵒ×
  ⸨ Q ⸩ᴮ {{BasicQ}}  ∗ᵒ  [ α ]ᴸ⟨ q /2⁺ ⟩ᵒ  ∗ᵒ  Oborᵐ i α q R

abstract

  -- Monoᵒ for %ᵐᵒ

  %ᵐᵒ-Mono :  Monoᵒ $ %ᵐ⟨ α , p ⟩ᵒ P
  %ᵐᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ Q → ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ →
    ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- Modify the fraction of %ᵐᵒ

  %ᵐᵒ-respᴿ :  p ≈ᴿ⁺ q  →   %ᵐ⟨ α , p ⟩ᵒ P  ⊨  %ᵐ⟨ α , q ⟩ᵒ P
  %ᵐᵒ-respᴿ {p} {q} p≈q (-, r , -, -ᴵ, -, (p≈r , R∗Q⊢S) , R∗αOborSa) =  -, -, -,
    -ᴵ, -, (≈ᴿ⁺-trans {q} {p} {r} (≈ᴿ⁺-sym {p} {q} p≈q) p≈r , R∗Q⊢S) , R∗αOborSa

  -- Monotonicity of %ᵐᵒ

  %ᵐᵒ-monoᴾ :  P  ⊢[ ∞ ]  Q  →   %ᵐ⟨ α , p ⟩ᵒ Q  ⊨  %ᵐ⟨ α , p ⟩ᵒ P
  %ᵐᵒ-monoᴾ P⊢Q (-, -, -, -ᴵ, -, (p≈q , R∗Q⊢S) , R∗αOborSa) =  -, -, -, -ᴵ, -,
    (p≈q , ∗-monoʳ P⊢Q » R∗Q⊢S) , R∗αOborSa

  -- Let %ᵐᵒ eat a basic proposition

  %ᵐᵒ-eatˡ :  {{_ : Basic Q}} →
    ⸨ Q ⸩ᴮ  ∗ᵒ  %ᵐ⟨ α , p ⟩ᵒ P  ⊨  %ᵐ⟨ α , p ⟩ᵒ (Q -∗ P)
  %ᵐᵒ-eatˡ =  ∗ᵒ⇒∗ᵒ' ›
    λ{ (-, -, b∙c⊑a , Qb , -, -, -, -ᴵ, -, (p≈q , R∗P⊢S) , R∗αOborSc) →
    -, -, -, -ᴵ, -, (p≈q ,
    -- (Q∗R)∗(Q-∗P) ⊢ (Q∗(Q-∗P))∗R ⊢ P∗R ⊢ R∗P ⊢ S
    ∗?-comm » ∗-monoˡ -∗-applyˡ » ∗-comm » R∗P⊢S) ,
    ∗ᵒ-assocˡ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Qb , R∗αOborSc) }

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

  -- Make &ᵐᵒ and ⟨†⟩ᵒ

  &ᵐᵒ-⟨†⟩ᵒ-make :
    ◎⟨ iᴮᵒʳ ⟩ (borᵐ i α P ∙ᴮᵒʳ lend i α P)  ⊨  &ᵐ⟨ α ⟩ᵒ P  ∗ᵒ  ⟨† α ⟩ᵒ P
  &ᵐᵒ-⟨†⟩ᵒ-make =  ◎⟨⟩-∙⇒∗ᵒ › ∗ᵒ-mono &ᵐᵒ-make ⟨†⟩ᵒ-make
