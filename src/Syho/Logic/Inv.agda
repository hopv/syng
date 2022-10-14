--------------------------------------------------------------------------------
-- Proof rules on the impredicative invariant
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Inv where

open import Base.Func using (_$_)
open import Base.Eq using (_≡_; refl; ◠˙_)
open import Base.Size using (𝕊; !; ¡_; _$ᵀʰ_)
open import Base.Prod using (_,_; -,_)
open import Base.Sum using (ĩ₁_)
open import Base.Nat using (ℕ)
open import Syho.Lang.Expr using (Addr; Type; V⇒E)
open import Syho.Lang.Ktxred using (Redex; 🞰ᴿ_; Ktx; _ᴷ◁_)
open import Syho.Logic.Prop using (WpKind; Name; Prop∞; Prop˂∞; ¡ᴾ_; _∧_; ⌜_⌝∧_;
  _∗_; _-∗_; [^_]ᴺ; &ⁱ⟨_⟩_; %ⁱ⟨_⟩_; static; _↦ⁱ_; Basic; ^ᶻᴺ-✔)
open import Syho.Logic.Core using (_⊢[_]_; _⊢[<_]_; Pers; Pers-⇒□; _»_; ∃-elim;
  ∃-intro; ∧-monoˡ; ∧-elimʳ; ⊤∧-intro; ∗-monoʳ; ∗-comm; ∗-assocˡ; ∗-assocʳ;
  ?∗-comm; ∗?-comm; ∗⇒∧; ∃∗-elim; -∗-applyˡ; -∗-const; Persˡ-∧⇒∗)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_; _ᵘ»ᵘ_; _ᵘ»_; ⇛-frameˡ; ⇛-frameʳ)
open import Syho.Logic.Hor using (_⊢[_][_]ᵃ⟨_⟩_; _⊢[_]⁺⟨_⟩[_]_; _⊢[<ᴾ_]⟨_⟩[_]_;
  _ᵘ»ᵃʰ_; _ᵃʰ»ᵘ_; _ᵃʰ»_; ahor-frameʳ; ahor✔-hor; hor<ᴾ-map)
open import Syho.Logic.Mem using (ahor-🞰)

-- Import and re-export
open import Syho.Logic.Judg public using (&ⁱ-⇒□; &ⁱ-resp-□∧; %ⁱ-mono; %ⁱ-eatˡ;
  &ⁱ-new-rec; &ⁱ-open; %ⁱ-close)

private variable
  ι :  𝕊
  P Q R :  Prop∞
  P˂ Q˂ :  Prop˂∞
  nm :  Name
  i :  ℕ
  T U :  Type
  red :  Redex T
  X :  Set₀
  Q˙ R˙ :  X →  Prop∞
  θ :  Addr
  v :  X
  κ :  WpKind
  K :  Ktx T U

abstract

  ------------------------------------------------------------------------------
  -- On the invariant and open invariant tokens

  -->  %ⁱ-mono :  P˂ .!  ⊢[< ι ]  Q˂ .!  →   %ⁱ⟨ nm ⟩ Q˂  ⊢[ ι ]  %ⁱ⟨ nm ⟩ P˂

  instance

    -- An invariant token is persistent

    -->  &ⁱ-⇒□ :  &ⁱ⟨ nm ⟩ P˂  ⊢[ ι ]  □ &ⁱ⟨ nm ⟩ P˂

    &ⁱ-Pers :  Pers $ &ⁱ⟨ nm ⟩ P˂
    &ⁱ-Pers .Pers-⇒□ =  &ⁱ-⇒□

  -- Modify an invariant token

  -->  &ⁱ-resp-□∧ :  {{Basic R}}  →
  -->    R  ∧  P˂ .!  ⊢[< ι ]  Q˂ .!  →   R  ∧  Q˂ .!  ⊢[< ι ]  P˂ .!  →
  -->    □ R  ∧  &ⁱ⟨ nm ⟩ P˂  ⊢[ ι ]  &ⁱ⟨ nm ⟩ Q˂

  &ⁱ-resp-∧ :  {{Pers R}}  →   {{Basic R}}  →
    R  ∧  P˂ .!  ⊢[< ι ]  Q˂ .!  →   R  ∧  Q˂ .!  ⊢[< ι ]  P˂ .!  →
    R  ∧  &ⁱ⟨ nm ⟩ P˂  ⊢[ ι ]  &ⁱ⟨ nm ⟩ Q˂
  &ⁱ-resp-∧ R∧P⊢Q R∧Q⊢P =  ∧-monoˡ Pers-⇒□ » &ⁱ-resp-□∧ R∧P⊢Q R∧Q⊢P

  &ⁱ-resp-∗ :  {{Pers R}}  →   {{Basic R}}  →
    R  ∗  P˂ .!  ⊢[< ι ]  Q˂ .!  →   R  ∗  Q˂ .!  ⊢[< ι ]  P˂ .!  →
    R  ∗  &ⁱ⟨ nm ⟩ P˂  ⊢[ ι ]  &ⁱ⟨ nm ⟩ Q˂
  &ⁱ-resp-∗ R∗P⊢Q R∗Q⊢P =  ∗⇒∧ »
    &ⁱ-resp-∧ ((Persˡ-∧⇒∗ »_) $ᵀʰ R∗P⊢Q) ((Persˡ-∧⇒∗ »_) $ᵀʰ R∗Q⊢P)

  &ⁱ-resp :  P˂ .!  ⊢[< ι ]  Q˂ .!  →   Q˂ .!  ⊢[< ι ]  P˂ .!  →
             &ⁱ⟨ nm ⟩ P˂  ⊢[ ι ]  &ⁱ⟨ nm ⟩ Q˂
  &ⁱ-resp P⊢Q Q⊢P =  ⊤∧-intro »
    &ⁱ-resp-∧ ((∧-elimʳ »_) $ᵀʰ P⊢Q) ((∧-elimʳ »_) $ᵀʰ Q⊢P)

  -- Let an open invariant token eat a basic proposition

  -->  %ⁱ-eatˡ :  {{Basic Q}}  →
  -->    Q  ∗  %ⁱ⟨ nm ⟩ P˂  ⊢[ ι ]  %ⁱ⟨ nm ⟩ ¡ᴾ (Q -∗ P˂ .!)

  %ⁱ-eatʳ :  {{Basic Q}} →  %ⁱ⟨ nm ⟩ P˂  ∗  Q  ⊢[ ι ]  %ⁱ⟨ nm ⟩ ¡ᴾ (Q -∗ P˂ .!)
  %ⁱ-eatʳ =  ∗-comm » %ⁱ-eatˡ

  -- Create &ⁱ⟨ nm ⟩ P˂ by storing P˂

  -->  &ⁱ-new-rec :  &ⁱ⟨ nm ⟩ P˂ -∗ P˂ .!  ⊢[ ι ][ i ]⇛  &ⁱ⟨ nm ⟩ P˂

  &ⁱ-new :  P˂ .!  ⊢[ ι ][ i ]⇛  &ⁱ⟨ nm ⟩ P˂
  &ⁱ-new =  -∗-const » &ⁱ-new-rec

  -- Use an invariant token

  -->  &ⁱ-open :  &ⁱ⟨ nm ⟩ P˂  ∗  [^ nm ]ᴺ  ⊢[ ι ][ i ]⇛  P˂ .!  ∗  %ⁱ⟨ nm ⟩ P˂

  -->  %ⁱ-close :  P˂ .!  ∗  %ⁱ⟨ nm ⟩ P˂  ⊢[ ι ][ i ]⇛  [^ nm ]ᴺ

  &ⁱ-use :  P˂ .!  ∗  Q  ⊢[ ι ][ i ]⇛  P˂ .!  ∗  R  →
            &ⁱ⟨ nm ⟩ P˂  ∗  [^ nm ]ᴺ  ∗  Q  ⊢[ ι ][ i ]⇛  [^ nm ]ᴺ  ∗  R
  &ⁱ-use P∗Q⊢⇛P∗R =  ∗-assocʳ » ⇛-frameʳ &ⁱ-open ᵘ»ᵘ ∗?-comm »
    ⇛-frameʳ P∗Q⊢⇛P∗R ᵘ»ᵘ ∗-assocˡ » ?∗-comm »
    ⇛-frameˡ %ⁱ-close ᵘ» ∗-comm

  ahor-&ⁱ-use :  P˂ .!  ∗  Q  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ (λ v →  P˂ .!  ∗  R˙ v)  →
    &ⁱ⟨ nm ⟩ P˂  ∗  [^ nm ]ᴺ  ∗  Q  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ λ v →  [^ nm ]ᴺ  ∗  R˙ v
  ahor-&ⁱ-use P∗Q⊢⟨red⟩P∗Rv =  ∗-assocʳ » ⇛-frameʳ {i = 0} &ⁱ-open ᵘ»ᵃʰ
    ∗?-comm » ahor-frameʳ P∗Q⊢⟨red⟩P∗Rv ᵃʰ»ᵘ λ _ → ∗-assocˡ » ?∗-comm »
    ⇛-frameˡ {i = 0} %ⁱ-close ᵘ» ∗-comm

  ------------------------------------------------------------------------------
  -- Static reference

  -- Hoare triple rules for ↦ⁱ

  ahor-↦ⁱ-🞰 :  θ ↦ⁱ (T , v)  ∗  [^ static ]ᴺ  ⊢[ ι ][ i ]ᵃ⟨ 🞰ᴿ_ {T} θ ⟩ λ u →
                 ⌜ u ≡ v ⌝∧  [^ static ]ᴺ
  ahor-↦ⁱ-🞰 =  &ⁱ-open {i = 0} ᵘ»ᵃʰ ahor-frameʳ ahor-🞰 ᵃʰ»ᵘ λ _ →
    ∃∗-elim λ u≡v → %ⁱ-close {P˂ = ¡ᴾ _} {i = 0} ᵘ» ∃-intro u≡v

  hor-↦ⁱ-🞰 :  P  ⊢[<ᴾ ι ]⟨ K ᴷ◁ V⇒E v ⟩[ κ ]  Q˙  →
              θ ↦ⁱ (T , v)  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , 🞰ᴿ_ {T} θ) ⟩[ κ ]  Q˙
  hor-↦ⁱ-🞰 P⊢⟨Kv⟩Q =  ahor✔-hor {i = 0} ^ᶻᴺ-✔
    (?∗-comm » ∗-assocʳ » ahor-frameʳ ahor-↦ⁱ-🞰 ᵃʰ» λ _ → ∃∗-elim λ u≡v →
      ∗-monoʳ $ ∃-intro u≡v)
    λ v → hor<ᴾ-map (λ big → ∃-elim λ{ refl → big }) P⊢⟨Kv⟩Q
