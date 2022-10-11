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
open import Syho.Logic.Prop using (Name; Prop∞; Prop˂∞; _∧_; _∗_; _-∗_; [_]ᴺ;
  [^_]ᴺ; Inv; OInv; Basic)
open import Syho.Logic.Core using (_⊢[_]_; _⊢[<_]_; Pers; Pers-⇒□; _»_; ∧-monoˡ;
  ∧-elimʳ; ⊤∧-intro; ∗-monoʳ; ∗-comm; ∗-assocˡ; ∗-assocʳ; ?∗-comm; ∗⇒∧;
  -∗-intro; -∗-applyˡ; -∗-const; Persˡ-∧⇒∗)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_; _ᵘ»ᵘ_; _ᵘ»_; ⇛-frameˡ; ⇛-frameʳ)
open import Syho.Logic.Hor using (_⊢[_][_]ᵃ⟨_⟩_; _ᵘ»ᵃʰ_; _ᵃʰ»ᵘ_; ahor-frameʳ)

-- Import and re-export
open import Syho.Logic.Judg public using ([]ᴺ-resp; []ᴺ-merge; []ᴺ-split; []ᴺ-✔;
  Inv-⇒□; Inv-resp-□∧; OInv-mono; OInv-eatˡ; Inv-alloc-rec; Inv-open;
  OInv-close)

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

  -->  OInv-mono :  P˂ .!  ⊢[< ι ]  Q˂ .!  →   OInv nm Q˂  ⊢[ ι ]  OInv nm P˂

  instance

    -- An invariant token is persistent

    -->  Inv-⇒□ :  Inv nm P˂  ⊢[ ι ]  □ Inv nm P˂

    Inv-Pers :  Pers $ Inv nm P˂
    Inv-Pers .Pers-⇒□ =  Inv-⇒□

  -- Change the proposition of an invariant token

  -->  Inv-resp-□∧ :  {{Basic R}}  →
  -->    R  ∧  P˂ .!  ⊢[< ι ]  Q˂ .!  →   R  ∧  Q˂ .!  ⊢[< ι ]  P˂ .!  →
  -->    □ R  ∧  Inv nm P˂  ⊢[ ι ]  Inv nm Q˂

  Inv-resp-∧ :  {{Pers R}}  →   {{Basic R}}  →
    R  ∧  P˂ .!  ⊢[< ι ]  Q˂ .!  →   R  ∧  Q˂ .!  ⊢[< ι ]  P˂ .!  →
    R  ∧  Inv nm P˂  ⊢[ ι ]  Inv nm Q˂
  Inv-resp-∧ R∧P⊢Q R∧Q⊢P =  ∧-monoˡ Pers-⇒□ » Inv-resp-□∧ R∧P⊢Q R∧Q⊢P

  Inv-resp-∗ :  {{Pers R}}  →   {{Basic R}}  →
    R  ∗  P˂ .!  ⊢[< ι ]  Q˂ .!  →   R  ∗  Q˂ .!  ⊢[< ι ]  P˂ .!  →
    R  ∗  Inv nm P˂  ⊢[ ι ]  Inv nm Q˂
  Inv-resp-∗ R∗P⊢Q R∗Q⊢P =  ∗⇒∧ »
    Inv-resp-∧ ((Persˡ-∧⇒∗ »_) $ᵀʰ R∗P⊢Q) ((Persˡ-∧⇒∗ »_) $ᵀʰ R∗Q⊢P)

  Inv-resp :  P˂ .!  ⊢[< ι ]  Q˂ .!  →   Q˂ .!  ⊢[< ι ]  P˂ .!  →
              Inv nm P˂  ⊢[ ι ]  Inv nm Q˂
  Inv-resp P⊢Q Q⊢P =  ⊤∧-intro »
    Inv-resp-∧ ((∧-elimʳ »_) $ᵀʰ P⊢Q) ((∧-elimʳ »_) $ᵀʰ Q⊢P)

  -- Let an open invariant token eat a basic proposition

  -->  OInv-eatˡ :  {{Basic Q}} →
  -->    Q  ∗  OInv nm P˂  ⊢[ ι ]  OInv nm (¡ (Q -∗ P˂ .!))

  OInv-eatʳ :  {{Basic Q}} →  OInv nm P˂  ∗  Q  ⊢[ ι ]  OInv nm (¡ (Q -∗ P˂ .!))
  OInv-eatʳ =   ∗-comm » OInv-eatˡ

  -- Get Inv nm P˂ by storing P˂

  -->  Inv-alloc-rec :  Inv nm P˂ -∗ P˂ .!  ⊢[ ι ][ i ]⇛  Inv nm P˂

  Inv-alloc :  P˂ .!  ⊢[ ι ][ i ]⇛  Inv nm P˂
  Inv-alloc =  -∗-const » Inv-alloc-rec

  -- Use an invariant token

  -->  Inv-open :  Inv nm P˂  ∗  [^ nm ]ᴺ  ⊢[ ι ][ i ]⇛  P˂ .!  ∗  OInv nm P˂

  -->  OInv-close :  P˂ .!  ∗  OInv nm P˂  ⊢[ ι ][ i ]⇛  [^ nm ]ᴺ

  Inv-use :  Q  ∗  P˂ .!  ⊢[ ι ][ i ]⇛  R  ∗  P˂ .!  →
             Inv nm P˂  ∗  Q  ∗  [^ nm ]ᴺ  ⊢[ ι ][ i ]⇛  R  ∗  [^ nm ]ᴺ
  Inv-use Q∗P⊢⇛R∗P =  ?∗-comm » ⇛-frameˡ Inv-open ᵘ»ᵘ ∗-assocʳ »
    ⇛-frameʳ Q∗P⊢⇛R∗P ᵘ»ᵘ ∗-assocˡ » ⇛-frameˡ OInv-close

  ahor-Inv-use :  Q  ∗  P˂ .!  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ (λ v →  R˙ v  ∗  P˂ .!)  →
    Inv nm P˂  ∗  Q  ∗  [^ nm ]ᴺ  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ λ v →  R˙ v  ∗  [^ nm ]ᴺ
  ahor-Inv-use Q∗P⊢⟨red⟩Rv∗P =  ?∗-comm » ⇛-frameˡ {i = 0} Inv-open ᵘ»ᵃʰ
    ∗-assocʳ » ahor-frameʳ Q∗P⊢⟨red⟩Rv∗P ᵃʰ»ᵘ λ _ → ∗-assocˡ »
    ⇛-frameˡ {i = 0} OInv-close
