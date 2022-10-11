--------------------------------------------------------------------------------
-- Proof rules on the impredicative invariant
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Inv where

open import Base.Func using (_$_)
open import Base.Eq using (◠˙_)
open import Base.Size using (Size; !; ¡_; _$ᵀʰ_)
open import Base.Zoi using (Zoi; _⊆ᶻ_; _∖ᶻ_; ⊆ᶻ⇒∖-⊎ˡ)
open import Base.Prod using (_,_)
open import Base.Nat using (ℕ)
open import Syho.Lang.Expr using (Type)
open import Syho.Lang.Ktxred using (Redex)
open import Syho.Logic.Prop using (Name; Prop∞; Prop˂∞; ¡ᴾ_; _∧_; _∗_; _-∗_;
  [_]ᴺ; [^_]ᴺ; &ⁱ⟨_⟩_; %ⁱ⟨_⟩_; Basic)
open import Syho.Logic.Core using (_⊢[_]_; _⊢[<_]_; Pers; Pers-⇒□; _»_; ∧-monoˡ;
  ∧-elimʳ; ⊤∧-intro; ∗-monoʳ; ∗-comm; ∗-assocˡ; ∗-assocʳ; ?∗-comm; ∗?-comm; ∗⇒∧;
  -∗-intro; -∗-applyˡ; -∗-const; Persˡ-∧⇒∗)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_; _ᵘ»ᵘ_; _ᵘ»_; ⇛-frameˡ; ⇛-frameʳ)
open import Syho.Logic.Hor using (_⊢[_][_]ᵃ⟨_⟩_; _ᵘ»ᵃʰ_; _ᵃʰ»ᵘ_; ahor-frameʳ)

-- Import and re-export
open import Syho.Logic.Judg public using ([]ᴺ-resp; []ᴺ-merge; []ᴺ-split; []ᴺ-✔;
  &ⁱ-⇒□; &ⁱ-resp-□∧; %ⁱ-mono; %ⁱ-eatˡ; &ⁱ-new-rec; &ⁱ-open; %ⁱ-close)

private variable
  ι :  Size
  P Q R :  Prop∞
  P˂ Q˂ :  Prop˂∞
  Nm Nm' :  Name → Zoi
  nm :  Name
  i :  ℕ
  T :  Type
  red :  Redex T
  X :  Set₀
  R˙ :  X →  Prop∞

abstract

  ------------------------------------------------------------------------------
  -- On the name set token

  -->  []ᴺ-resp :  Nm ≡˙ Nm' →  [ Nm ]ᴺ ⊢[ ι ] [ Nm' ]ᴺ

  -->  []ᴺ-merge :  [ Nm ]ᴺ  ∗  [ Nm' ]ᴺ  ⊢[ ι ]  [ Nm ⊎ᶻ Nm' ]ᴺ

  -->  []ᴺ-split :  [ Nm ⊎ᶻ Nm' ]ᴺ  ⊢[ ι ]  [ Nm ]ᴺ  ∗  [ Nm' ]ᴺ

  -->  []ᴺ-✔ :  [ Nm ]ᴺ  ⊢[ ι ]  ⌜ ✔ᶻ Nm ⌝

  -- Take out a name set token of a subset

  []ᴺ-⊆-split :  Nm' ⊆ᶻ Nm  →   [ Nm ]ᴺ  ⊢[ ι ]  [ Nm' ]ᴺ  ∗  [ Nm ∖ᶻ Nm' ]ᴺ
  []ᴺ-⊆-split Nm'⊆Nm =  []ᴺ-resp (◠˙ ⊆ᶻ⇒∖-⊎ˡ Nm'⊆Nm) » []ᴺ-split

  []ᴺ-⊆-merge :  Nm' ⊆ᶻ Nm  →   [ Nm' ]ᴺ  ∗  [ Nm ∖ᶻ Nm' ]ᴺ  ⊢[ ι ]  [ Nm ]ᴺ
  []ᴺ-⊆-merge Nm'⊆Nm =  []ᴺ-merge » []ᴺ-resp (⊆ᶻ⇒∖-⊎ˡ Nm'⊆Nm)

  []ᴺ-⊆--∗ :  Nm' ⊆ᶻ Nm  →   [ Nm ]ᴺ  ⊢[ ι ]  [ Nm' ]ᴺ  ∗  ([ Nm' ]ᴺ -∗ [ Nm ]ᴺ)
  []ᴺ-⊆--∗ Nm'⊆Nm =
    []ᴺ-⊆-split Nm'⊆Nm » ∗-monoʳ $ -∗-intro $ []ᴺ-⊆-merge Nm'⊆Nm

  -- Use only a part of a name set token for super update

  ⇛-[]ᴺ-⊆ :  Nm' ⊆ᶻ Nm  →   P  ∗  [ Nm' ]ᴺ  ⊢[ ι ][ i ]⇛  Q  ∗  [ Nm' ]ᴺ  →
             P  ∗  [ Nm ]ᴺ  ⊢[ ι ][ i ]⇛  Q  ∗  [ Nm ]ᴺ
  ⇛-[]ᴺ-⊆ Nm'⊆Nm P⊢⇛[Nm']Q =  ∗-monoʳ ([]ᴺ-⊆--∗ Nm'⊆Nm) » ∗-assocʳ »
    ⇛-frameʳ P⊢⇛[Nm']Q ᵘ» ∗-assocˡ » ∗-monoʳ -∗-applyˡ

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
