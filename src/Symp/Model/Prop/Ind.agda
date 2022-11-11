--------------------------------------------------------------------------------
-- Interpret the indirection modality and the precursors
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Symp.Model.Prop.Ind where

open import Base.Level using (1ᴸ)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Few using (⊤₀; absurd)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using (upd˙)
open import Base.Size using (∞)
open import Base.Option using (¿_; š_; ň)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_; _,-; -ᴵ,_; ∑-case)
open import Base.Nat using (ℕ; ṡ_; _≤_; _<_)
open import Symp.Lang.Expr using (Type; Expr∞; Val)
open import Symp.Lang.Ktxred using (Redex)
open import Symp.Logic.Prop using (HorKind; par; tot; SProp∞; ⊤'; _∗_; Basic)
open import Symp.Logic.Core using (_⊢[_]_; _»_; ∗-assocˡ; ∗-assocʳ; ∗-monoˡ;
  ∗-monoʳ; ?∗-comm; ∗-elimʳ)
open import Symp.Logic.Fupd using (_⊢[_][_]⇛_; _⊢[_][_]⇛ᴺ_; ⇛-≤; _ᵘ»_; _ᵘ»ᵘ_;
  ⇛-frameˡ; ⇛-frameʳ; ⇛ᴺ-frameˡ)
open import Symp.Logic.Hor using (_⊢[_][_]ᵃ⟨_⟩_; _⊢[_]⟨_⟩[_]_; _⊢[_]⟨_⟩ᴾ_;
  _⊢[_]⟨_⟩ᵀ[_]_; _⊢[_][_]⟨_⟩∞; hor-ᵀ⇒ᴾ; ihor⇒horᴾ; ahor-≤; horᵀ-≤; ihor-≤;
  _ᵘ»ᵃʰ_; _ᵘᴺ»ʰ_; _ᵘᴺ»ⁱʰ_; _ᵃʰ»ᵘ_; _ʰ»ᵘᴺ_; ahor-frameʳ; hor-frameʳ)
open import Symp.Model.ERA.Base using (ERA)
open import Symp.Model.ERA.Ind using (εᴵⁿᵈˣ; indˣ; indᵖ; indˣ-new; indˣ-use;
  indᵖ-new; indᵖ-use)
open import Symp.Model.ERA.Glob using (iᴵⁿᵈˣ; iᴵⁿᵈᵖ)
open import Symp.Model.Prop.Base using (SPropᵒ; Monoᵒ; _⊨_; ⊨_; ∃ᵒ-syntax;
  ∃ᴵ-syntax; ⌜_⌝ᵒ×_; _⨿ᵒ_; ⊤ᵒ₀; _∗ᵒ_; □ᵒ_; ⤇ᴱ⟨⟩; ◎⟨_⟩_; ∃ᵒ-Mono; ∃ᴵ-Mono;
  ⨿ᵒ-Mono; ∗ᵒ⇒∗ᵒ'; ∗ᵒ'⇒∗ᵒ; ∗ᵒ-Mono; ∗ᵒ-assocˡ; ?∗ᵒ-intro; ⤇ᴱ⟨⟩-mono; ⤇ᴱ⟨⟩-param;
  ◎-Mono; ◎⟨⟩-⌞⌟≡-□ᵒ; ↝-◎⟨⟩-⤇ᴱ⟨⟩; ε↝-◎⟨⟩-⤇ᴱ⟨⟩)
open import Symp.Model.Prop.Basic using (⸨_⸩ᴮ)

private variable
  i j n :  ℕ
  X :  Set₀
  T :  Type
  P P' Q Q' R :  SProp∞
  Q˙ Q'˙ :  X →  SProp∞
  Qˇ˙ :  ℕ →  ¿ SProp∞
  κ :  HorKind
  red :  Redex T
  e :  Expr∞ T

--------------------------------------------------------------------------------
-- Indˣ, Indᵖ, Ind :  Indirection base

Indˣ Indᵖ Ind :  SProp∞ →  SPropᵒ 1ᴸ
Indˣ P =  ∃ᵒ i , ◎⟨ iᴵⁿᵈˣ ⟩ indˣ i P
Indᵖ P =  ∃ᵒ i , ◎⟨ iᴵⁿᵈᵖ ⟩ indᵖ i P
Ind P =  Indˣ P ⨿ᵒ Indᵖ P

abstract

  -- Monoᵒ for Indˣ, Indᵖ, Ind

  Indˣ-Mono :  Monoᵒ $ Indˣ P
  Indˣ-Mono =  ∃ᵒ-Mono λ _ → ◎-Mono

  Indᵖ-Mono :  Monoᵒ $ Indᵖ P
  Indᵖ-Mono =  ∃ᵒ-Mono λ _ → ◎-Mono

  Ind-Mono :  Monoᵒ $ Ind P
  Ind-Mono =  ⨿ᵒ-Mono Indˣ-Mono Indᵖ-Mono

  -- Create Indˣ

  Indˣ-new' :  ⊨ (Qˇ˙ , n) ⤇ᴱ⟨ iᴵⁿᵈˣ ⟩ λ (_ : ⊤₀) → (upd˙ n (š P) Qˇ˙ , ṡ n) ,
                 Indˣ P
  Indˣ-new' =  ε↝-◎⟨⟩-⤇ᴱ⟨⟩ indˣ-new ▷ ⤇ᴱ⟨⟩-mono λ _ → -,_

  -- Use Indˣ

  Indˣ-use' :
    Indˣ P  ⊨ (Qˇ˙ , n) ⤇ᴱ⟨ iᴵⁿᵈˣ ⟩ λ ((i ,-) :  ∑ i , i < n  ×  Qˇ˙ i ≡ š P) →
      (upd˙ i ň Qˇ˙ , n) ,  ⊤ᵒ₀
  Indˣ-use' =  ∑-case λ i → ↝-◎⟨⟩-⤇ᴱ⟨⟩ {bⁱ˙ = λ _ → εᴵⁿᵈˣ} indˣ-use ›
    ⤇ᴱ⟨⟩-mono _ › ⤇ᴱ⟨⟩-param {f = i ,_}

  -- Create □ᵒ Indᵖ

  □ᵒIndᵖ-new' :  ⊨ (Qˇ˙ , n) ⤇ᴱ⟨ iᴵⁿᵈᵖ ⟩ λ (_ : ⊤₀) → (upd˙ n (š P) Qˇ˙ , ṡ n) ,
                   □ᵒ Indᵖ P
  □ᵒIndᵖ-new' =  ε↝-◎⟨⟩-⤇ᴱ⟨⟩ indᵖ-new ▷ ⤇ᴱ⟨⟩-mono λ _ → ◎⟨⟩-⌞⌟≡-□ᵒ refl › -,_

  -- Use Indᵖ

  Indᵖ-use' :
    Indᵖ P  ⊨ (Qˇ˙ , n) ⤇ᴱ⟨ iᴵⁿᵈᵖ ⟩ λ (_ :  ∑ i , i < n  ×  Qˇ˙ i ≡ š P) →
      (Qˇ˙ , n) ,  ⊤ᵒ₀
  Indᵖ-use' =  ∑-case λ i →
    ↝-◎⟨⟩-⤇ᴱ⟨⟩ indᵖ-use › ⤇ᴱ⟨⟩-mono _ › ⤇ᴱ⟨⟩-param {f = i ,_}

--------------------------------------------------------------------------------
-- ○ᵒ :  Interpret the indirection modality ○

infix 8 ○ᵒ_
○ᵒ_ :  SProp∞ →  SPropᵒ 1ᴸ
○ᵒ P =  ∃ᵒ Q , ∃ᴵ BasicQ , ∃ᵒ R ,
  ⌜ Q ∗ R ⊢[ ∞ ] P ⌝ᵒ×  ⸨ Q ⸩ᴮ {{BasicQ}}  ∗ᵒ  Ind R

abstract

  -- Monoᵒ for ○ᵒ

  ○ᵒ-Mono :  Monoᵒ $ ○ᵒ P
  ○ᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- Monotonicity of ○ᵒ

  ○ᵒ-mono :  P ⊢[ ∞ ] Q →  ○ᵒ P ⊨ ○ᵒ Q
  ○ᵒ-mono P⊢Q (-, -ᴵ, -, R∗S⊢P , R∗IndSa) =  -, -ᴵ, -, R∗S⊢P » P⊢Q , R∗IndSa

  -- Let ○ᵒ eat a proposition under ∗ᵒ

  ○ᵒ-eatˡ :  {{_ : Basic Q}} →  ⸨ Q ⸩ᴮ ∗ᵒ ○ᵒ P ⊨ ○ᵒ (Q ∗ P)
  ○ᵒ-eatˡ =  ∗ᵒ⇒∗ᵒ' › λ{ (-, -, b∙c⊑a , Qb , -, -ᴵ, -, R∗S⊢P , R∗IndSc) →
    -, -ᴵ, -, ∗-assocʳ » ∗-monoʳ R∗S⊢P ,
    ∗ᵒ-assocˡ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Qb , R∗IndSc) }

  -- Make ○ᵒ out of Ind

  Ind⇒○ᵒ :  Ind P ⊨ ○ᵒ P
  Ind⇒○ᵒ IndPa =  ⊤' , -ᴵ, -, ∗-elimʳ , ?∗ᵒ-intro absurd IndPa

--------------------------------------------------------------------------------
-- ⊸⇛ᵒ :  Interpret the fancy update precursor ⊸⇛

infixr 5 _⊸[_]⇛ˢ_
_⊸[_]⇛ˢ_ :  SProp∞ →  ℕ →  SProp∞ →  SPropᵒ 1ᴸ
P ⊸[ i ]⇛ˢ Q =  ∃ᵒ R , ∃ᴵ BasicR , ∃ᵒ S ,
  ⌜ P ∗ R ∗ S ⊢[ ∞ ][ i ]⇛ Q ⌝ᵒ×  ⸨ R ⸩ᴮ {{BasicR}}  ∗ᵒ  Ind S

abstract

  -- Monoᵒ for ⊸⇛ᵒ

  ⊸⇛ᵒ-Mono :  Monoᵒ $ P ⊸[ i ]⇛ˢ Q
  ⊸⇛ᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- Modify ⇛ proof

  ⊸⇛ᵒ-≤ :  i ≤ j  →   P ⊸[ i ]⇛ˢ Q  ⊨  P ⊸[ j ]⇛ˢ Q
  ⊸⇛ᵒ-≤ i≤j (-, -ᴵ, -, P∗R∗S⊢⇛Q , R∗IndSa) =
    -, -ᴵ, -, ⇛-≤ i≤j P∗R∗S⊢⇛Q , R∗IndSa

  ⊸⇛ᵒ-eatˡ⁻ˡᵘ :  {{_ : Basic R}} →
    R ∗ P' ⊢[ ∞ ][ i ]⇛ P →  ⸨ R ⸩ᴮ ∗ᵒ (P ⊸[ i ]⇛ˢ Q)  ⊨  P' ⊸[ i ]⇛ˢ Q
  ⊸⇛ᵒ-eatˡ⁻ˡᵘ R∗P'⊢⇛P =  ∗ᵒ⇒∗ᵒ' › λ{
    (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⇛Q , S∗IndTc) →  -, -ᴵ, -,
    -- P'∗(R∗S)∗T ⊢ P'∗R∗S∗T ⊢ R∗P'∗S∗T ⊢ (R∗P')∗S∗T ⊢⇛ P∗S∗T ⊢⇛ Q
    ∗-monoʳ ∗-assocʳ » ?∗-comm » ∗-assocˡ » ⇛-frameˡ R∗P'⊢⇛P ᵘ»ᵘ P∗S∗T⊢⇛Q ,
    ∗ᵒ-assocˡ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Rb , S∗IndTc) }

  ⊸⇛ᵒ-monoʳᵘ :  Q ⊢[ ∞ ][ i ]⇛ Q' →  P ⊸[ i ]⇛ˢ Q  ⊨  P ⊸[ i ]⇛ˢ Q'
  ⊸⇛ᵒ-monoʳᵘ Q⊢⇛Q' (-, -ᴵ, -, P∗R∗S⊢⇛Q , R∗IndSa) =
    -, -ᴵ, -, P∗R∗S⊢⇛Q ᵘ»ᵘ Q⊢⇛Q' , R∗IndSa

  ⊸⇛ᵒ-eatˡ⁻ʳ :  {{_ : Basic R}} →
    ⸨ R ⸩ᴮ ∗ᵒ (P ⊸[ i ]⇛ˢ Q)  ⊨  P ⊸[ i ]⇛ˢ R ∗ Q
  ⊸⇛ᵒ-eatˡ⁻ʳ =  ∗ᵒ⇒∗ᵒ' › λ{ (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⇛Q , S∗IndTc) →
    -, -ᴵ, -,
    -- P∗(R∗S)∗T ⊢ P∗R∗S∗T ⊢⇛ R∗P∗S∗T ⊢⇛ R∗Q
    ∗-monoʳ ∗-assocʳ » ?∗-comm » ⇛-frameʳ P∗S∗T⊢⇛Q ,
    ∗ᵒ-assocˡ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Rb , S∗IndTc) }

  ⊸⇛ᵒ-frameʳ :  P ⊸[ i ]⇛ˢ Q  ⊨  R ∗ P ⊸[ i ]⇛ˢ R ∗ Q
  ⊸⇛ᵒ-frameʳ (-, -ᴵ, -, P∗R∗S⊢⇛Q , R∗IndSa) =
    -, -ᴵ, -, ∗-assocʳ » ⇛-frameʳ P∗R∗S⊢⇛Q , R∗IndSa

  -- Make ⊸⇛ᵒ out of ○ᵒ

  ○ᵒ⇒⊸⇛ᵒ :  P ∗ R ⊢[ ∞ ][ i ]⇛ Q →  ○ᵒ R  ⊨  P ⊸[ i ]⇛ˢ Q
  ○ᵒ⇒⊸⇛ᵒ P∗R⊢⇛Q (-, -ᴵ, -, S∗T⊢R , S∗IndTa) =
    -, -ᴵ, -, ∗-monoʳ S∗T⊢R » P∗R⊢⇛Q , S∗IndTa

--------------------------------------------------------------------------------
-- ⊸ᵃ⟨ ⟩ᵒ :  Interpret the atomic Hoare triple precursor ⊸ᵃ⟨ ⟩

infixr 5 _⊸[_]ᵃ⟨_⟩ᵒ_
_⊸[_]ᵃ⟨_⟩ᵒ_ :  SProp∞ →  ℕ →  Redex T →  (Val T → SProp∞) →  SPropᵒ 1ᴸ
P ⊸[ i ]ᵃ⟨ red ⟩ᵒ Q˙ =  ∃ᵒ R , ∃ᴵ BasicR , ∃ᵒ S ,
  ⌜ P ∗ R ∗ S ⊢[ ∞ ][ i ]ᵃ⟨ red ⟩ Q˙ ⌝ᵒ×  ⸨ R ⸩ᴮ {{BasicR}}  ∗ᵒ  Ind S

abstract

  -- Monoᵒ for ⊸ᵃ⟨ ⟩ᵒ

  ⊸ᵃ⟨⟩ᵒ-Mono :  Monoᵒ $ P ⊸[ i ]ᵃ⟨ red ⟩ᵒ Q˙
  ⊸ᵃ⟨⟩ᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- Modify ᵃ⟨ ⟩ proof

  ⊸ᵃ⟨⟩ᵒ-≤ :  i ≤ j  →   P ⊸[ i ]ᵃ⟨ red ⟩ᵒ Q˙  ⊨  P ⊸[ j ]ᵃ⟨ red ⟩ᵒ Q˙
  ⊸ᵃ⟨⟩ᵒ-≤ i≤j (-, -ᴵ, -, P∗R∗S⊢⟨red⟩Q , R∗IndSa) =
    -, -ᴵ, -, ahor-≤ i≤j P∗R∗S⊢⟨red⟩Q , R∗IndSa

  ⊸ᵃ⟨⟩ᵒ-eatˡ⁻ˡᵘ :  {{_ : Basic R}} →  R ∗ P' ⊢[ ∞ ][ j ]⇛ P →
                   ⸨ R ⸩ᴮ ∗ᵒ (P ⊸[ i ]ᵃ⟨ red ⟩ᵒ Q˙)  ⊨  P' ⊸[ i ]ᵃ⟨ red ⟩ᵒ Q˙
  ⊸ᵃ⟨⟩ᵒ-eatˡ⁻ˡᵘ R∗P'⊢⇛P =  ∗ᵒ⇒∗ᵒ' › λ{
    (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⟨red⟩Q , S∗IndTc) →  -, -ᴵ, -,
    -- P'∗(R∗S)∗T ⊢ P'∗R∗S∗T ⊢ R∗P'∗S∗T ⊢ (R∗P')∗S∗T ⊢⇛ P∗S∗T ⊢ᵃ⟨red⟩ Q˙
    ∗-monoʳ ∗-assocʳ » ?∗-comm » ∗-assocˡ » ⇛-frameˡ R∗P'⊢⇛P ᵘ»ᵃʰ P∗S∗T⊢⟨red⟩Q ,
    ∗ᵒ-assocˡ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Rb , S∗IndTc) }

  ⊸ᵃ⟨⟩ᵒ-monoʳᵘ :  (∀ v →  Q˙ v ⊢[ ∞ ][ j ]⇛ Q'˙ v) →
                  P ⊸[ i ]ᵃ⟨ red ⟩ᵒ Q˙  ⊨  P ⊸[ i ]ᵃ⟨ red ⟩ᵒ Q'˙
  ⊸ᵃ⟨⟩ᵒ-monoʳᵘ Qv⊢⇛Q'v (-, -ᴵ, -, P∗R∗S⊢⟨red⟩Q , R∗IndSa) =
    -, -ᴵ, -, P∗R∗S⊢⟨red⟩Q ᵃʰ»ᵘ Qv⊢⇛Q'v , R∗IndSa

  ⊸ᵃ⟨⟩ᵒ-eatˡ⁻ʳ :  {{_ : Basic R}} →
    ⸨ R ⸩ᴮ ∗ᵒ (P ⊸[ i ]ᵃ⟨ red ⟩ᵒ Q˙)  ⊨  P ⊸[ i ]ᵃ⟨ red ⟩ᵒ λ v → R ∗ Q˙ v
  ⊸ᵃ⟨⟩ᵒ-eatˡ⁻ʳ =  ∗ᵒ⇒∗ᵒ' › λ{
    (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⟨red⟩Q , S∗IndTc) →  -, -ᴵ, -,
    -- P∗(R∗S)∗T ⊢ P∗R∗S∗T ⊢ R∗P∗S∗T ⊢ᵃ⟨red⟩ R∗Q
    ∗-monoʳ ∗-assocʳ » ?∗-comm » ahor-frameʳ P∗S∗T⊢⟨red⟩Q ,
    ∗ᵒ-assocˡ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Rb , S∗IndTc) }

  ⊸ᵃ⟨⟩ᵒ-frameʳ :  P ⊸[ i ]ᵃ⟨ red ⟩ᵒ Q˙  ⊨  R ∗ P ⊸[ i ]ᵃ⟨ red ⟩ᵒ λ v → R ∗ Q˙ v
  ⊸ᵃ⟨⟩ᵒ-frameʳ (-, -ᴵ, -, P∗R∗S⊢⟨red⟩Q , R∗IndSa) =
    -, -ᴵ, -, ∗-assocʳ » ahor-frameʳ P∗R∗S⊢⟨red⟩Q , R∗IndSa

  -- Make ⊸ᵃ⟨ ⟩ᵒ out of ○ᵒ

  ○ᵒ⇒⊸ᵃ⟨⟩ᵒ :  P ∗ R ⊢[ ∞ ][ i ]ᵃ⟨ red ⟩ Q˙ →  ○ᵒ R  ⊨  P ⊸[ i ]ᵃ⟨ red ⟩ᵒ Q˙
  ○ᵒ⇒⊸ᵃ⟨⟩ᵒ P∗R⊢⟨red⟩Q (-, -ᴵ, -, S∗T⊢R , S∗IndTa) =
    -, -ᴵ, -, ∗-monoʳ S∗T⊢R » P∗R⊢⟨red⟩Q , S∗IndTa

--------------------------------------------------------------------------------
-- ⊸⟨ ⟩[ ]ᵒ :  Interpret the common Hoare triple precursor ⊸⟨ ⟩

infixr 5 _⊸⟨_⟩[_]ᵒ_ _⊸⟨_⟩ᴾᵒ_ _⊸⟨_⟩ᵀ[_]ᵒ_

_⊸⟨_⟩[_]ᵒ_ :  SProp∞ →  Expr∞ T →  HorKind →  (Val T → SProp∞) →  SPropᵒ 1ᴸ
P ⊸⟨ e ⟩[ κ ]ᵒ Q˙ =  ∃ᵒ R , ∃ᴵ BasicR , ∃ᵒ S ,
  ⌜ P ∗ R ∗ S ⊢[ ∞ ]⟨ e ⟩[ κ ] Q˙ ⌝ᵒ×  ⸨ R ⸩ᴮ {{BasicR}}  ∗ᵒ  Ind S

_⊸⟨_⟩ᴾᵒ_ :  SProp∞ →  Expr∞ T →  (Val T → SProp∞) →  SPropᵒ 1ᴸ
P ⊸⟨ e ⟩ᴾᵒ Q˙ =  P ⊸⟨ e ⟩[ par ]ᵒ Q˙

_⊸⟨_⟩ᵀ[_]ᵒ_ :  SProp∞ →  Expr∞ T →  ℕ →  (Val T → SProp∞) →  SPropᵒ 1ᴸ
P ⊸⟨ e ⟩ᵀ[ i ]ᵒ Q˙ =  P ⊸⟨ e ⟩[ tot i ]ᵒ Q˙

abstract

  -- Monoᵒ for ⊸⟨ ⟩ᵒ

  ⊸⟨⟩ᵒ-Mono :  Monoᵒ $ P ⊸⟨ e ⟩[ κ ]ᵒ Q˙
  ⊸⟨⟩ᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- Modify ⟨ ⟩ proof

  ⊸⟨⟩ᵀᵒ⇒⊸⟨⟩ᴾᵒ :  P ⊸⟨ e ⟩ᵀ[ i ]ᵒ Q˙  ⊨  P ⊸⟨ e ⟩ᴾᵒ Q˙
  ⊸⟨⟩ᵀᵒ⇒⊸⟨⟩ᴾᵒ (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, hor-ᵀ⇒ᴾ P∗R∗S⊢⟨e⟩Q , R∗IndSa

  ⊸⟨⟩ᵀᵒ-≤ :  i ≤ j  →   P ⊸⟨ e ⟩ᵀ[ i ]ᵒ Q˙  ⊨  P ⊸⟨ e ⟩ᵀ[ j ]ᵒ Q˙
  ⊸⟨⟩ᵀᵒ-≤ i≤j (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, horᵀ-≤ i≤j P∗R∗S⊢⟨e⟩Q , R∗IndSa

  ⊸⟨⟩ᵒ-eatˡ⁻ˡᵘᴺ :  {{_ : Basic R}} →  R ∗ P' ⊢[ ∞ ][ i ]⇛ᴺ P →
                   ⸨ R ⸩ᴮ ∗ᵒ (P ⊸⟨ e ⟩[ κ ]ᵒ Q˙)  ⊨  P' ⊸⟨ e ⟩[ κ ]ᵒ Q˙
  ⊸⟨⟩ᵒ-eatˡ⁻ˡᵘᴺ R∗P'⊢⇛[⊤]P =  ∗ᵒ⇒∗ᵒ' › λ{
    (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⟨e⟩Q , S∗IndTc) →  -, -ᴵ, -,
    -- P'∗(R∗S)∗T ⊢ P'∗R∗S∗T ⊢ R∗P'∗S∗T ⊢ (R∗P')∗S∗T ⊢⇛ᴺ P∗S∗T ⊢⟨e⟩ Q˙
    ∗-monoʳ ∗-assocʳ » ?∗-comm » ∗-assocˡ »
      ⇛ᴺ-frameˡ R∗P'⊢⇛[⊤]P ᵘᴺ»ʰ P∗S∗T⊢⟨e⟩Q ,
    ∗ᵒ-assocˡ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Rb , S∗IndTc) }

  ⊸⟨⟩ᵒ-monoʳᵘᴺ :  (∀ v →  Q˙ v ⊢[ ∞ ][ i ]⇛ᴺ Q'˙ v) →
                  P ⊸⟨ e ⟩[ κ ]ᵒ Q˙  ⊨  P ⊸⟨ e ⟩[ κ ]ᵒ Q'˙
  ⊸⟨⟩ᵒ-monoʳᵘᴺ Qv⊢⇛Q'v (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, P∗R∗S⊢⟨e⟩Q ʰ»ᵘᴺ Qv⊢⇛Q'v , R∗IndSa

  ⊸⟨⟩ᵒ-eatˡ⁻ʳ :  {{_ : Basic R}} →
    ⸨ R ⸩ᴮ ∗ᵒ (P ⊸⟨ e ⟩[ κ ]ᵒ Q˙)  ⊨  P ⊸⟨ e ⟩[ κ ]ᵒ λ v → R ∗ Q˙ v
  ⊸⟨⟩ᵒ-eatˡ⁻ʳ =  ∗ᵒ⇒∗ᵒ' › λ{
    (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⟨e⟩Q , S∗IndTc) →  -, -ᴵ, -,
    -- P∗(R∗S)∗T ⊢ P∗R∗S∗T ⊢ R∗P∗S∗T ⊢⟨e⟩ R∗Q
    ∗-monoʳ ∗-assocʳ » ?∗-comm » hor-frameʳ P∗S∗T⊢⟨e⟩Q ,
    ∗ᵒ-assocˡ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Rb , S∗IndTc) }

  ⊸⟨⟩ᵒ-frameʳ :  P ⊸⟨ e ⟩[ κ ]ᵒ Q˙  ⊨  R ∗ P ⊸⟨ e ⟩[ κ ]ᵒ λ v → R ∗ Q˙ v
  ⊸⟨⟩ᵒ-frameʳ (-, -ᴵ, -, P∗R∗S⊢⟨e⟩Q , R∗IndSa) =
    -, -ᴵ, -, ∗-assocʳ » hor-frameʳ P∗R∗S⊢⟨e⟩Q , R∗IndSa

  -- Make ⊸⟨ ⟩ᵒ out of ○ᵒ

  ○ᵒ⇒⊸⟨⟩ᵒ :  P ∗ R ⊢[ ∞ ]⟨ e ⟩[ κ ] Q˙ →  ○ᵒ R  ⊨  P ⊸⟨ e ⟩[ κ ]ᵒ Q˙
  ○ᵒ⇒⊸⟨⟩ᵒ P∗R⊢⟨e⟩Q (-, -ᴵ, -, S∗T⊢R , S∗IndTa) =
    -, -ᴵ, -, ∗-monoʳ S∗T⊢R » P∗R⊢⟨e⟩Q , S∗IndTa

--------------------------------------------------------------------------------
-- ⊸⟨ ⟩∞ᵒ :  Interpret the infinite Hoare triple precursor ⊸ᵃ⟨ ⟩

infixr 5 _⊸[_]⟨_⟩∞ᵒ
_⊸[_]⟨_⟩∞ᵒ :  SProp∞ →  ℕ →  Expr∞ T →  SPropᵒ 1ᴸ
P ⊸[ i ]⟨ e ⟩∞ᵒ =  ∃ᵒ Q , ∃ᴵ BasicQ , ∃ᵒ R ,
  ⌜ P ∗ Q ∗ R ⊢[ ∞ ][ i ]⟨ e ⟩∞ ⌝ᵒ×  ⸨ Q ⸩ᴮ {{BasicQ}}  ∗ᵒ  Ind R

abstract

  -- Monoᵒ for ⊸⟨ ⟩∞ᵒ

  ⊸⟨⟩∞ᵒ-Mono :  Monoᵒ $ P ⊸[ i ]⟨ e ⟩∞ᵒ
  ⊸⟨⟩∞ᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᴵ-Mono $ ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ∗ᵒ-Mono

  -- Modify ⟨ ⟩∞ proof

  ⊸⟨⟩∞ᵒ⇒⊸⟨⟩ᴾᵒ :  P ⊸[ i ]⟨ e ⟩∞ᵒ  ⊨  P ⊸⟨ e ⟩ᴾᵒ Q˙
  ⊸⟨⟩∞ᵒ⇒⊸⟨⟩ᴾᵒ (-, -ᴵ, -, P∗R∗S⊢⟨e⟩∞ , R∗IndSa) =
    -, -ᴵ, -, ihor⇒horᴾ P∗R∗S⊢⟨e⟩∞ , R∗IndSa

  ⊸⟨⟩∞ᵒ-≤ :  i ≤ j  →   P ⊸[ i ]⟨ e ⟩∞ᵒ  ⊨  P ⊸[ j ]⟨ e ⟩∞ᵒ
  ⊸⟨⟩∞ᵒ-≤ i≤j (-, -ᴵ, -, P∗Q∗R⊢⟨e⟩∞ , Q∗IndRa) =
    -, -ᴵ, -, ihor-≤ i≤j P∗Q∗R⊢⟨e⟩∞ , Q∗IndRa

  ⊸⟨⟩∞ᵒ-eatˡ⁻ᵘᴺ :  {{_ : Basic R}} →  R ∗ Q ⊢[ ∞ ][ i ]⇛ᴺ P →
                   ⸨ R ⸩ᴮ ∗ᵒ (P ⊸[ j ]⟨ e ⟩∞ᵒ)  ⊨  Q ⊸[ j ]⟨ e ⟩∞ᵒ
  ⊸⟨⟩∞ᵒ-eatˡ⁻ᵘᴺ R∗Q⊢⇛P =  ∗ᵒ⇒∗ᵒ' › λ{
    (-, -, b∙c⊑a , Rb , -, -ᴵ, -, P∗S∗T⊢⟨e⟩Q , S∗IndTc) →  -, -ᴵ, -,
    -- Q∗(R∗S)∗T ⊢ Q∗R∗S∗T ⊢ R∗Q∗S∗T ⊢ (R∗Q)∗S∗T ⊢⇛ P∗S∗T ⊢⟨e⟩∞
    ∗-monoʳ ∗-assocʳ » ?∗-comm » ∗-assocˡ » ⇛ᴺ-frameˡ R∗Q⊢⇛P ᵘᴺ»ⁱʰ P∗S∗T⊢⟨e⟩Q ,
    ∗ᵒ-assocˡ $ ∗ᵒ'⇒∗ᵒ (-, -, b∙c⊑a , Rb , S∗IndTc) }

  -- Make ⊸⟨ ⟩∞ᵒ out of ○ᵒ

  ○ᵒ⇒⊸⟨⟩∞ᵒ :  P ∗ Q ⊢[ ∞ ][ i ]⟨ e ⟩∞ →  ○ᵒ Q  ⊨  P ⊸[ i ]⟨ e ⟩∞ᵒ
  ○ᵒ⇒⊸⟨⟩∞ᵒ P∗Q⊢⟨e⟩∞ (-, -ᴵ, -, R∗S⊢Q , R∗IndSa) =
    -, -ᴵ, -, ∗-monoʳ R∗S⊢Q » P∗Q⊢⟨e⟩∞ , R∗IndSa
