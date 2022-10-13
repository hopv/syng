--------------------------------------------------------------------------------
-- Proof rules on the borrow
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Bor where

open import Base.Func using (_$_)
open import Base.Size using (𝕊; !; ¡_; _$ᵀʰ_)
open import Base.Eq using (_≡_; refl)
open import Base.Prod using (_,_; -,_)
open import Base.Sum using (ĩ₁_)
open import Base.Nat using (ℕ)
open import Base.Ratp using (ℚ⁺)
open import Syho.Lang.Expr using (Addr; Type; V⇒E)
open import Syho.Lang.Ktxred using (🞰ᴿ_; Ktx; _ᴷ◁_)
open import Syho.Logic.Prop using (Lft; WpKind; Prop∞; Prop˂∞; ¡ᴾ_; _∧_; ⌜_⌝∧_;
  _∗_; _-∗_; _↦⟨_⟩_; [_]ᴸ⟨_⟩; ⟨†_⟩_; &ˢ⟨_⟩_; %ˢ⟨_⟩_; _↦ˢ⟨_⟩_; Basic)
open import Syho.Logic.Core using (_⊢[_]_; _⊢[<_]_; Pers; Pers-⇒□; ⇒<; _»_;
  ∃-elim; ∃-intro; ∧-monoˡ; ∧-elimʳ; ⊤∧-intro; ∗-comm; ∗-assocˡ; ∗-assocʳ;
  ?∗-comm; ∗?-comm; ∗⇒∧; ∃∗-elim; ∗∃-elim; Persˡ-∧⇒∗)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_; _ᵘ»ᵘ_; _ᵘ»_; ⇛-frameˡ; ⇛-frameʳ)
open import Syho.Logic.Hor using (_⊢[_][_]ᵃ⟨_⟩_; _⊢[<ᴾ_]⟨_⟩[_]_; _⊢[_]⁺⟨_⟩[_]_;
  _ᵘ»ᵃʰ_; _ᵃʰ»ᵘ_; ahor-frameʳ; ahor-hor; hor<ᴾ-map)
open import Syho.Logic.Mem using (ahor-🞰)

-- Import and re-export
open import Syho.Logic.Judg public using (&ˢ-⇒□; ⟨†⟩-mono; ⟨†⟩-eatˡ; &ˢ-resp-□∧;
  %ˢ-mono; %ˢ-eatˡ; ⟨†⟩-back; &ˢ-new; &ˢ-open; %ˢ-close)

private variable
  ι :  𝕊
  i :  ℕ
  α :  Lft
  X :  Set₀
  P Q R :  Prop∞
  P˂ :  Prop˂∞
  Q˙ :  X → Prop∞
  P˂˙ Q˂˙ :  X → Prop˂∞
  p :  ℚ⁺
  θ :  Addr
  T U :  Type
  v :  X
  K :  Ktx T U
  κ :  WpKind

abstract

  ------------------------------------------------------------------------------
  -- On the borrow

  -->  ⟨†⟩-mono :  P˂ .!  ⊢[< ι ]  Q˂ .!  →   ⟨† α ⟩ P˂  ⊢[ ι ]  ⟨† α ⟩ Q˂

  -->  %ˢ-mono :  P˂ .!  ⊢[< ι ]  Q˂ .!  →
  -->             %ˢ⟨ α , p ⟩ Q˂  ⊢[ ι ]  %ˢ⟨ α , p ⟩ P˂

  -->  ⟨†⟩-back :  †ᴸ α  ∗  ⟨† α ⟩ P˂  ⊢[ ι ][ i ]⇛  P˂ .!

  -->  &ˢ-new :  P˂˙ 1ᴿ⁺ .!  ⊢[ ι ][ i ]⇛  &ˢ⟨ α ⟩ P˂˙  ∗  ⟨† α ⟩ P˂˙ 1ᴿ⁺

  -- The shared borrow token is persistent

  instance

    -->  &ˢ-⇒□ :  &ˢ⟨ α ⟩ P˂˙  ⊢[ ι ]  □ &ˢ⟨ α ⟩ P˂˙

    &ˢ-Pers :  Pers $ &ˢ⟨ α ⟩ P˂˙
    &ˢ-Pers .Pers-⇒□ =  &ˢ-⇒□

  -- Let a lending token eat a basic proposition

  -->  ⟨†⟩-eatˡ :  {{Basic Q}}  →
  -->    Q  ∗  ⟨† α ⟩ P˂  ⊢[ ι ]  ⟨† α ⟩ ¡ᴾ (Q ∗ P˂ .!)

  ⟨†⟩-eatʳ :  {{Basic Q}}  →   ⟨† α ⟩ P˂  ∗  Q  ⊢[ ι ]  ⟨† α ⟩ ¡ᴾ (P˂ .! ∗ Q)
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
  -->    Q  ∗  %ˢ⟨ α , p ⟩ P˂  ⊢[ ι ]  %ˢ⟨ α , p ⟩ ¡ᴾ (Q -∗ P˂ .!)

  %ˢ-eatʳ :  {{Basic Q}}  →
    %ˢ⟨ α , p ⟩ P˂  ∗  Q  ⊢[ ι ]  %ˢ⟨ α , p ⟩ ¡ᴾ (Q -∗ P˂ .!)
  %ˢ-eatʳ =  ∗-comm » %ˢ-eatˡ

  -- Use a shared borrow token

  -->  &ˢ-open :  &ˢ⟨ α ⟩ P˂˙  ∗  [ α ]ᴸ⟨ p ⟩  ⊢[ ι ][ i ]⇛
  -->               ∃ q ,  P˂˙ q .!  ∗  %ˢ⟨ α , p ⟩ P˂˙ q

  -->  %ˢ-close :  P˂˙ q .!  ∗  %ˢ⟨ α , p ⟩ P˂˙ q  ⊢[ ι ][ i ]⇛  [ α ]ᴸ⟨ p ⟩

  &ˢ-use :  (∀{q} →  P˂˙ q .!  ∗  Q  ⊢[ ι ][ i ]⇛  P˂˙ q .!  ∗  R)  →
    &ˢ⟨ α ⟩ P˂˙  ∗  [ α ]ᴸ⟨ p ⟩  ∗  Q  ⊢[ ι ][ i ]⇛  [ α ]ᴸ⟨ p ⟩  ∗  R
  &ˢ-use {P˂˙ = P˂˙} Pq∗Q⊢⇛Pq∗R =  ∗-assocʳ » ⇛-frameʳ &ˢ-open ᵘ»ᵘ ∃∗-elim λ _ →
    ∗?-comm » ⇛-frameʳ Pq∗Q⊢⇛Pq∗R ᵘ»ᵘ ∗-assocˡ » ?∗-comm »
    ⇛-frameˡ (%ˢ-close {P˂˙ = P˂˙}) ᵘ» ∗-comm

  ------------------------------------------------------------------------------
  -- On the shared-borrowed points-to token

  ahor-↦ˢ-🞰 :  θ ↦ˢ⟨ α ⟩ (T , v)  ∗  [ α ]ᴸ⟨ p ⟩
                 ⊢[ ι ][ i ]ᵃ⟨ 🞰ᴿ_ {T} θ ⟩ λ u →  ⌜ u ≡ v ⌝∧  [ α ]ᴸ⟨ p ⟩
  ahor-↦ˢ-🞰 =  &ˢ-open {i = 0} ᵘ»ᵃʰ ∃-elim λ _ → ahor-frameʳ ahor-🞰 ᵃʰ»ᵘ λ _ →
    ∃∗-elim λ u≡v → %ˢ-close {P˂˙ = λ q → ¡ᴾ _ ↦⟨ q ⟩ _} {i = 0} ᵘ» ∃-intro u≡v

  hor-↦ˢ-🞰 :  [ α ]ᴸ⟨ p ⟩  ∗  P  ⊢[<ᴾ ι ]⟨ K ᴷ◁ V⇒E v ⟩[ κ ]  Q˙  →
              θ ↦ˢ⟨ α ⟩ (T , v)  ∗  [ α ]ᴸ⟨ p ⟩  ∗  P
                ⊢[ ι ]⁺⟨ ĩ₁ (-, K , 🞰ᴿ_ {T} θ) ⟩[ κ ]  Q˙
  hor-↦ˢ-🞰 [α]∗P⊢⟨Kv⟩Q =  ∗-assocʳ »
    ahor-hor (ahor-frameʳ $ ahor-↦ˢ-🞰 {i = 0}) λ v →
    hor<ᴾ-map (λ big → ∃∗-elim λ{ refl → big }) [α]∗P⊢⟨Kv⟩Q
