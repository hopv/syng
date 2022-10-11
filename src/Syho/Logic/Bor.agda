--------------------------------------------------------------------------------
-- Borrow
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Bor where

open import Base.Func using (_$_)
open import Base.Size using (Size; !; ¡_; _$ᵀʰ_)
open import Base.Prod using (_,_)
open import Base.Nat using (ℕ)
open import Base.RatPos using (ℚ⁺)
open import Syho.Logic.Prop using (Lft; Prop∞; Prop˂∞; _∧_; _∗_; _-∗_; [_]ᴸ⟨_⟩;
  ⟨†_⟩_; &ˢ⟨_⟩_; %ˢ⟨_⟩_; Basic)
open import Syho.Logic.Core using (_⊢[_]_; _⊢[<_]_; Pers; Pers-⇒□; ⇒<; _»_;
  ∧-monoˡ; ∧-elimʳ; ⊤∧-intro; ∗-comm; ∗-assocˡ; ∗-assocʳ; ?∗-comm; ∗⇒∧; ∗∃-elim;
  Persˡ-∧⇒∗)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_; _ᵘ»ᵘ_; ⇛-frameˡ; ⇛-frameʳ)

-- Import and re-export
open import Syho.Logic.Judg public using (&ˢ-⇒□; ⟨†⟩-mono; ⟨†⟩-eatˡ; &ˢ-resp-□∧;
  %ˢ-mono; %ˢ-eatˡ; ⟨†⟩-back; &ˢ-new; &ˢ-open; %ˢ-close)

private variable
  ι :  Size
  i :  ℕ
  α :  Lft
  Q R :  Prop∞
  P˂ :  Prop˂∞
  P˂˙ Q˂˙ :  ℚ⁺ → Prop˂∞
  p :  ℚ⁺

abstract

  -->  ⟨†⟩-mono :  P˂ .!  ⊢[< ι ]  Q˂ .!  →   ⟨† α ⟩ P˂  ⊢[ ι ]  ⟨† α ⟩ Q˂

  -->  %ˢ-mono :  P˂ .!  ⊢[< ι ]  Q˂ .!  →
  -->             %ˢ⟨ α , p ⟩ Q˂  ⊢[ ι ]  %ˢ⟨ α , p ⟩ P˂

  -->  ⟨†⟩-back :  †ᴸ α  ∗  ⟨† α ⟩ P˂  ⊢[ ι ][ i ]⇛  P˂ .!

  -->  &ˢ-new :  P˂˙ 1ᴿ⁺ .!  ⊢[ ι ][ i ]⇛  &ˢ⟨ α ⟩ P˂˙  ∗  ⟨† α ⟩ P˂˙ 1ᴿ⁺

  -- The shared borrow token is persistent

  -->  &ˢ-⇒□ :  &ˢ⟨ α ⟩ P˂˙  ⊢[ ι ]  □ &ˢ⟨ α ⟩ P˂˙

  &ˢ-Pers :  Pers $ &ˢ⟨ α ⟩ P˂˙
  &ˢ-Pers .Pers-⇒□ =  &ˢ-⇒□

  -- Let a lending token eat a basic proposition

  -->  ⟨†⟩-eatˡ :  {{Basic Q}}  →
  -->    Q  ∗  ⟨† α ⟩ P˂  ⊢[ ι ]  ⟨† α ⟩ ¡ (Q ∗ P˂ .!)

  ⟨†⟩-eatʳ :  {{Basic Q}}  →   ⟨† α ⟩ P˂  ∗  Q  ⊢[ ι ]  ⟨† α ⟩ ¡ (P˂ .! ∗ Q)
  ⟨†⟩-eatʳ =  ∗-comm » ⟨†⟩-eatˡ » ⟨†⟩-mono $ ⇒< ∗-comm

  -- Modify a shared borrow token

  -->  &ˢ-resp-□∧ :  {{Basic R}}  →
  -->    (∀{p} →  R  ∧  P˂˙ p .!  ⊢[< ι ]  Q˂˙ p .!)  →
  -->    (∀{p} →  R  ∧  Q˂˙ p .!  ⊢[< ι ]  P˂˙ p .!)  →
  -->    □ R  ∧  &ˢ⟨ α ⟩ P˂˙  ⊢[ ι ]  &ˢ⟨ α ⟩ Q˂˙

  &ˢ-resp-∧ :  {{Pers R}}  →   {{Basic R}}  →
    (∀{p} →  R  ∧  P˂˙ p .!  ⊢[< ι ]  Q˂˙ p .!)  →
    (∀{p} →  R  ∧  Q˂˙ p .!  ⊢[< ι ]  P˂˙ p .!)  →
    R  ∧  &ˢ⟨ α ⟩ P˂˙  ⊢[ ι ]  &ˢ⟨ α ⟩ Q˂˙
  &ˢ-resp-∧ R∧Pp⊢Qp R∧Qp⊢Pp =  ∧-monoˡ Pers-⇒□ » &ˢ-resp-□∧ R∧Pp⊢Qp R∧Qp⊢Pp

  &ˢ-resp-∗ :  {{Pers R}}  →   {{Basic R}}  →
    (∀{p} →  R  ∗  P˂˙ p .!  ⊢[< ι ]  Q˂˙ p .!)  →
    (∀{p} →  R  ∗  Q˂˙ p .!  ⊢[< ι ]  P˂˙ p .!)  →
    R  ∗  &ˢ⟨ α ⟩ P˂˙  ⊢[ ι ]  &ˢ⟨ α ⟩ Q˂˙
  &ˢ-resp-∗ R∗Pp⊢Qp R∗Qp⊢Pp =  ∗⇒∧ »
    &ˢ-resp-∧ ((Persˡ-∧⇒∗ »_) $ᵀʰ R∗Pp⊢Qp) ((Persˡ-∧⇒∗ »_) $ᵀʰ R∗Qp⊢Pp)

  &ˢ-resp :  (∀{p} →  P˂˙ p .!  ⊢[< ι ]  Q˂˙ p .!)  →
             (∀{p} →  Q˂˙ p .!  ⊢[< ι ]  P˂˙ p .!)  →
             &ˢ⟨ α ⟩ P˂˙  ⊢[ ι ]  &ˢ⟨ α ⟩ Q˂˙
  &ˢ-resp Pp⊢Qp Qp⊢Pp =  ⊤∧-intro »
    &ˢ-resp-∧ ((∧-elimʳ »_) $ᵀʰ Pp⊢Qp) ((∧-elimʳ »_) $ᵀʰ Qp⊢Pp)

  -- Let an open shared borrow token eat a basic proposition

  -->  %ˢ-eatˡ :  {{Basic Q}}  →
  -->    Q  ∗  %ˢ⟨ α , p ⟩ P˂  ⊢[ ι ]  %ˢ⟨ α , p ⟩ ¡ (Q -∗ P˂ .!)

  %ˢ-eatʳ :  {{Basic Q}}  →
    %ˢ⟨ α , p ⟩ P˂  ∗  Q  ⊢[ ι ]  %ˢ⟨ α , p ⟩ ¡ (Q -∗ P˂ .!)
  %ˢ-eatʳ =  ∗-comm » %ˢ-eatˡ

  -- Use a shared borrow token

  -->  &ˢ-open :  &ˢ⟨ α ⟩ P˂˙  ∗  [ α ]ᴸ⟨ p ⟩  ⊢[ ι ][ i ]⇛
  -->               ∃ q ,  P˂˙ q .!  ∗  %ˢ⟨ α , p ⟩ P˂˙ q

  -->  %ˢ-close :  P˂˙ q .!  ∗  %ˢ⟨ α , p ⟩ P˂˙ q  ⊢[ ι ][ i ]⇛  [ α ]ᴸ⟨ p ⟩

  &ˢ-use :  (∀{q} →  Q  ∗  P˂˙ q .!  ⊢[ ι ][ i ]⇛  R  ∗  P˂˙ q .!)  →
    &ˢ⟨ α ⟩ P˂˙  ∗  Q  ∗  [ α ]ᴸ⟨ p ⟩  ⊢[ ι ][ i ]⇛  R  ∗  [ α ]ᴸ⟨ p ⟩
  &ˢ-use {P˂˙ = P˂˙} Q∗Pq⊢⇛R∗Pq =  ?∗-comm » ⇛-frameˡ &ˢ-open ᵘ»ᵘ ∗∃-elim λ _ →
    ∗-assocʳ » ⇛-frameʳ Q∗Pq⊢⇛R∗Pq ᵘ»ᵘ ∗-assocˡ »
    ⇛-frameˡ $ %ˢ-close {P˂˙ = P˂˙}
