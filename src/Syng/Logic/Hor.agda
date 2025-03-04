--------------------------------------------------------------------------------
-- Proof rules on the Hoare triples
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syng.Logic.Hor where

open import Base.Func using (_$_; _∘_; id)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using (Inh)
open import Base.Size using (𝕊; !; _$ᵀʰ_)
open import Base.Bool using (𝔹; tt; ff)
open import Base.Zoi using (Zoi; ✔ᶻ_)
open import Base.Prod using (_,_; -,_)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Base.Nat using (ℕ; _<ᵈ_; ≤ᵈ-refl; ≤ᵈṡ; _≤_; _<_; ≤⇒<≡; ≤⇒≤ᵈ)
open import Base.Sety using (Setʸ; ⸨_⸩ʸ)
open import Syng.Lang.Expr using (Type; ◸ʸ_; _ʸ↷_; Expr∞; Expr˂∞; ∇_; _⁏_; let˙;
  V⇒E)
open import Syng.Lang.Ktxred using (Redex; ndᴿ; [_]ᴿ⟨_⟩; Ktx; •ᴷ; _◁ᴷʳ_; _⁏ᴷ_;
  _ᴷ◁_; Val/Ktxred)
open import Syng.Lang.Reduce using (_⇒ᴾ_; _⇒ᴾ○_; _⇒ᴾ●_; redᴾ)
open import Syng.Logic.Prop using (HorKind; par; tot; Name; SProp∞; ⌜_⌝; _∗_;
  [_]ᴺ; [⊤]ᴺ)
open import Syng.Logic.Core using (_⊢[_]_; ⇒<; _»_; ⌜⌝-intro; ∗-monoˡ; ∗-comm;
  ∗?-comm; -∗-applyˡ)
open import Syng.Logic.Fupd using (_⊢[_][_]⇛_; _⊢[_][_]⇛ᴺ_; ⇒⇛; ⇛⇒⇛ᴺ)
open import Syng.Logic.Names using ([]ᴺ-⊆--∗)

-- Import and re-export
open import Syng.Logic.Judg public using ([_]ᵃ⟨_⟩_; ⁺⟨_⟩[_]_; _⊢[_][_]ᵃ⟨_⟩_;
  _⊢[<_][_]ᵃ⟨_⟩_; _⊢[_]⁺⟨_⟩[_]_; _⊢[_]⁺⟨_/_⟩[_]_; _⊢[_]⁺⟨_⟩ᴾ_; _⊢[_]⁺⟨_⟩ᵀ[_]_;
  _⊢[<_]⁺⟨_⟩ᵀ[_]_; _⊢[_]⟨_⟩[_]_; _⊢[<_]⟨_⟩[_]_; _⊢[_]⟨_⟩ᴾ_; _⊢[<_]⟨_⟩ᴾ_;
  _⊢[_]⟨_⟩ᵀ[_]_; _⊢[<_]⟨_⟩ᵀ[_]_; _⊢[<ᴾ_]⟨_⟩[_]_; _⊢[_][_]⁺⟨_⟩∞; _⊢[<_][_]⁺⟨_⟩∞;
  _⊢[_][_]⟨_⟩∞; _⊢[<_][_]⟨_⟩∞; hor-ᵀ⇒ᴾ; ihor⇒horᴾ; ahor-ṡ; horᵀ-ṡ; ihor-ṡ;
  _ᵘ»ᵃʰ_; _ᵘᴺ»ʰ_; _ᵘᴺ»ⁱʰ_; _ᵃʰ»ᵘ_; _ʰ»ᵘᴺ_; ahor-frameʳ; hor-frameʳ; ahorᴺ-hor;
  ahorᴺ-ihor; hor-bind; ihor-bind; hor-ihor-bind; hor-valᵘᴺ; ahor-nd; hor-[];
  ihor-[]○; ihor-[]●; hor-fork; ihor-fork)

private variable
  ι :  𝕊
  b :  𝔹
  i j :  ℕ
  X :  Set₀
  Xʸ :  Setʸ
  T U :  Type
  κ :  HorKind
  Nm :  Name → Zoi
  P P' Q R :  SProp∞
  Q˙ Q'˙ R˙ :  X → SProp∞
  red :  Redex T
  vk :  Val/Ktxred T
  K :  Ktx T U
  e e' e₀ :  Expr∞ T
  e'˂ :  Expr˂∞ T
  e˂˙ :  X → Expr˂∞ T
  v :  X

infixr -1 _ᵘ»ʰ_ _ᵃʰ»_ _ʰ»ᵘ_ _ʰ»_

abstract

  ------------------------------------------------------------------------------
  -- Proof rules on the Hoare triples

  -->  hor-ᵀ⇒ᴾ :  P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ  Q˙  →   P  ⊢[ ι ]⁺⟨ vk ⟩ᴾ  Q˙

  -->  ihor⇒horᴾ :  P  ⊢[ ι ][ i ]⁺⟨ vk ⟩∞  →   P  ⊢[ ι ]⁺⟨ vk ⟩ᴾ  Q˙

  -->  hor-fork :  P  ⊢[<ᴾ ι ]⟨ e ⟩[ κ ] (λ _ →  ⊤')  →
  -->              Q  ⊢[<ᴾ ι ]⟨ K ᴷ◁ ∇ _ ⟩[ κ ]  R˙  →
  -->              P  ∗  Q  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , forkᴿ e) ⟩[ κ ]  R˙

  -->  ihor-fork :  P  ⊢[ ι ]⟨ e ⟩ᵀ[ j ] (λ _ →  ⊤')  →
  -->               Q  ⊢[ ι ][ i ]⟨ K ᴷ◁ ∇ _ ⟩∞  →
  -->               P  ∗  Q  ⊢[ ι ][ i ]⁺⟨ ĩ₁ (-, K , forkᴿ e) ⟩∞

  -- Level increase on the atomic / total Hoare triple

  -->  ahor-ṡ :  P  ⊢[< ι ][ i ]ᵃ⟨ red ⟩  Q˙  →   P  ⊢[ ι ][ ṡ i ]ᵃ⟨ red ⟩  Q˙

  ahor-<ᵈ :  i <ᵈ j  →   P  ⊢[< ι ][ i ]ᵃ⟨ red ⟩  Q˙  →
             P  ⊢[ ι ][ j ]ᵃ⟨ red ⟩  Q˙
  ahor-<ᵈ ≤ᵈ-refl =  ahor-ṡ
  ahor-<ᵈ (≤ᵈṡ i<j') =  ahor-ṡ ∘ ⇒< ∘ ahor-<ᵈ i<j'

  ahor-< :  i < j  →   P  ⊢[< ι ][ i ]ᵃ⟨ red ⟩  Q˙  →
            P  ⊢[ ι ][ j ]ᵃ⟨ red ⟩  Q˙
  ahor-< =  ahor-<ᵈ ∘ ≤⇒≤ᵈ

  ahor-≤ :  i ≤ j  →   P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩  Q˙  →
            P  ⊢[ ι ][ j ]ᵃ⟨ red ⟩  Q˙
  ahor-≤ i≤j  with ≤⇒<≡ i≤j
  … | ĩ₀ i<j =  ahor-< i<j ∘ ⇒<
  … | ĩ₁ refl =  id

  -->  horᵀ-ṡ :  P  ⊢[< ι ]⁺⟨ vk ⟩ᵀ[ i ]  Q˙  →   P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ ṡ i ]  Q˙

  horᵀ-<ᵈ :  i <ᵈ j  →   P  ⊢[< ι ]⁺⟨ vk ⟩ᵀ[ i ]  Q˙  →
             P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ j ]  Q˙
  horᵀ-<ᵈ ≤ᵈ-refl =  horᵀ-ṡ
  horᵀ-<ᵈ (≤ᵈṡ i<j') =  horᵀ-ṡ ∘ ⇒< ∘ horᵀ-<ᵈ i<j'

  horᵀ-< :  i < j  →   P  ⊢[< ι ]⁺⟨ vk ⟩ᵀ[ i ]  Q˙  →
            P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ j ]  Q˙
  horᵀ-< =  horᵀ-<ᵈ ∘ ≤⇒≤ᵈ

  horᵀ-≤ :  i ≤ j  →   P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ i ]  Q˙  →
            P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ j ]  Q˙
  horᵀ-≤ i≤j  with ≤⇒<≡ i≤j
  … | ĩ₀ i<j =  horᵀ-< i<j ∘ ⇒<
  … | ĩ₁ refl =  id

  -->  ihor-ṡ :  P  ⊢[< ι ][ i ]⁺⟨ vk ⟩∞  →   P  ⊢[ ι ][ ṡ i ]⁺⟨ vk ⟩∞

  ihor-<ᵈ :  i <ᵈ j  →   P  ⊢[< ι ][ i ]⁺⟨ vk ⟩∞  →   P  ⊢[ ι ][ j ]⁺⟨ vk ⟩∞
  ihor-<ᵈ ≤ᵈ-refl =  ihor-ṡ
  ihor-<ᵈ (≤ᵈṡ i<j') =  ihor-ṡ ∘ ⇒< ∘ ihor-<ᵈ i<j'

  ihor-< :  i < j  →   P  ⊢[< ι ][ i ]⁺⟨ vk ⟩∞  →   P  ⊢[ ι ][ j ]⁺⟨ vk ⟩∞
  ihor-< =  ihor-<ᵈ ∘ ≤⇒≤ᵈ

  ihor-≤ :  i ≤ j  →   P  ⊢[ ι ][ i ]⁺⟨ vk ⟩∞  →   P  ⊢[ ι ][ j ]⁺⟨ vk ⟩∞
  ihor-≤ i≤j  with ≤⇒<≡ i≤j
  … | ĩ₀ i<j =  ihor-< i<j ∘ ⇒<
  … | ĩ₁ refl =  id

  -- Compose

  -->  _ᵘ»ᵃʰ_ :  P  ⊢[ ι ][ j ]⇛  Q  →   Q  ⊢[ ι ][ i ]ᵃ⟨ red ⟩  R˙  →
  -->            P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩  R˙

  -->  _ᵘᴺ»ʰ_ :  P  ⊢[ ι ][ i ]⇛ᴺ  Q  →   Q  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  R˙  →
  -->            P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  R˙

  _ᵘ»ʰ_ :  P  ⊢[ ι ][ i ]⇛  Q  →   Q  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  R˙  →
           P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  R˙
  _ᵘ»ʰ_ =  _ᵘᴺ»ʰ_ ∘ ⇛⇒⇛ᴺ

  -->  _ᵘᴺ»ⁱʰ_ :  P  ⊢[ ι ][ i ]⇛ᴺ  Q  →   Q  ⊢[ ι ][ j ]⁺⟨ vk ⟩∞  →
  -->             P  ⊢[ ι ][ j ]⁺⟨ vk ⟩∞

  _ᵘ»ⁱʰ_ :  P  ⊢[ ι ][ i ]⇛  Q  →   Q  ⊢[ ι ][ j ]⁺⟨ vk ⟩∞  →
            P  ⊢[ ι ][ j ]⁺⟨ vk ⟩∞
  _ᵘ»ⁱʰ_ =  _ᵘᴺ»ⁱʰ_ ∘ ⇛⇒⇛ᴺ

  -->  _ᵃʰ»ᵘ_ :  P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩  Q˙  →
  -->            (∀ v →  Q˙ v  ⊢[ ι ][ j ]⇛  R˙ v)  →
  -->            P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩  R˙

  _ᵃʰ»_ :  P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩  Q˙  →   (∀ v →  Q˙ v  ⊢[ ι ]  R˙ v)  →
           P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩  R˙
  P⊢⟨red⟩Q ᵃʰ» ∀vQ⊢R =  P⊢⟨red⟩Q ᵃʰ»ᵘ λ _ → ⇒⇛ {i = 0} $ ∀vQ⊢R _

  -->  _ʰ»ᵘᴺ_ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  Q˙  →
  -->            (∀ v →  Q˙ v  ⊢[ ι ][ j ]⇛ᴺ  R˙ v)  →
  -->            P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  R˙

  _ʰ»ᵘ_ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  Q˙  →   (∀ v →  Q˙ v  ⊢[ ι ][ j ]⇛  R˙ v)  →
           P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  R˙
  _ʰ»ᵘ_ P⊢⟨vk⟩Q =  (P⊢⟨vk⟩Q ʰ»ᵘᴺ_) ∘ (⇛⇒⇛ᴺ ∘_)

  _ʰ»_ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  Q˙  →   (∀ v →  Q˙ v  ⊢[ ι ]  R˙ v)  →
          P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  R˙
  P⊢⟨vk⟩Q ʰ» ∀vQ⊢R =  P⊢⟨vk⟩Q ʰ»ᵘ λ _ → ⇒⇛ {i = 0} $ ∀vQ⊢R _

  hor-⇛ᴺ :  P'  ⊢[ ι ][ i ]⇛ᴺ  P  →   P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  Q˙  →
            (∀ v →  Q˙ v  ⊢[ ι ][ j ]⇛ᴺ  Q'˙ v)  →   P'  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  Q'˙
  hor-⇛ᴺ P'⊢⇛P P⊢⟨vk⟩Q Qv⊢⇛Q'v =  P'⊢⇛P ᵘᴺ»ʰ P⊢⟨vk⟩Q ʰ»ᵘᴺ Qv⊢⇛Q'v

  -- Frame

  -->  ahor-frameʳ :  P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩  Q˙  →
  -->                 R  ∗  P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ λ v →  R  ∗  Q˙ v

  ahor-frameˡ :  P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩  Q˙  →
                 P  ∗  R  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ λ v →  Q˙ v  ∗  R
  ahor-frameˡ P⊢⟨red⟩Q =  ∗-comm » ahor-frameʳ P⊢⟨red⟩Q ᵃʰ» λ _ → ∗-comm

  -->  hor-frameʳ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  Q˙  →
  -->                R  ∗  P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ] λ v →  R  ∗  Q˙ v

  hor-frameˡ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  Q˙  →
                P  ∗  R  ⊢[ ι ]⁺⟨ vk ⟩[ κ ] λ v →  Q˙ v  ∗  R
  hor-frameˡ P⊢⟨vk⟩Q =  ∗-comm » hor-frameʳ P⊢⟨vk⟩Q ʰ» λ _ → ∗-comm

  -- Turn an atomic Hoare triple with a valid name set token into one with the
  -- universal name set token

  ahor-✔⇒ᴺ :  ✔ᶻ Nm  →
    [ Nm ]ᴺ ∗ P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ (λ v →  [ Nm ]ᴺ ∗ Q˙ v)  →
    [⊤]ᴺ ∗ P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ (λ v →  [⊤]ᴺ ∗ Q˙ v)
  ahor-✔⇒ᴺ ✔Nm P⊢⟨red⟩[Nm]Q =  ∗-monoˡ ([]ᴺ-⊆--∗ ✔Nm) » ∗?-comm »
    ahor-frameˡ P⊢⟨red⟩[Nm]Q ᵃʰ» λ _ → ∗?-comm » ∗-monoˡ -∗-applyˡ

  -- Compose an atomic Hoare triple and a common Hoare triple for the context

  -->  ahorᴺ-hor :  [⊤]ᴺ ∗ P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ (λ v →  [⊤]ᴺ ∗ Q˙ v)  →
  -->               (∀ v →  Q˙ v  ⊢[<ᴾ ι ]⟨ K ᴷ◁ V⇒E v ⟩[ κ ]  R˙)  →
  -->               P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , red) ⟩[ κ ]  R˙

  ahor✔-hor :  ✔ᶻ Nm  →
    [ Nm ]ᴺ ∗ P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ (λ v →  [ Nm ]ᴺ ∗ Q˙ v)  →
    (∀ v →  Q˙ v  ⊢[<ᴾ ι ]⟨ K ᴷ◁ V⇒E v ⟩[ κ ]  R˙)  →
    P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , red) ⟩[ κ ]  R˙
  ahor✔-hor ✔Nm P⊢⟨red⟩[Nm]Q =  ahorᴺ-hor $ ahor-✔⇒ᴺ ✔Nm P⊢⟨red⟩[Nm]Q

  ahor-hor :  P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ (λ v →  Q˙ v)  →
              (∀ v →  Q˙ v  ⊢[<ᴾ ι ]⟨ K ᴷ◁ V⇒E v ⟩[ κ ]  R˙)  →
              P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , red) ⟩[ κ ]  R˙
  ahor-hor P⊢⟨red⟩Qv =  ahorᴺ-hor $ ahor-frameʳ P⊢⟨red⟩Qv

  -->  ahorᴺ-ihor :  [⊤]ᴺ ∗ P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ (λ v →  [⊤]ᴺ ∗ Q˙ v)  →
  -->                (∀ v →  Q˙ v  ⊢[ ι ][ j ]⟨ K ᴷ◁ V⇒E v ⟩∞)  →
  -->                P  ⊢[ ι ][ j ]⁺⟨ ĩ₁ (-, K , red) ⟩∞

  ahor✔-ihor :  ✔ᶻ Nm  →
    [ Nm ]ᴺ ∗ P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ (λ v →  [ Nm ]ᴺ ∗ Q˙ v)  →
    (∀ v →  Q˙ v  ⊢[ ι ][ j ]⟨ K ᴷ◁ V⇒E v ⟩∞)  →
    P  ⊢[ ι ][ j ]⁺⟨ ĩ₁ (-, K , red) ⟩∞
  ahor✔-ihor ✔Nm P⊢⟨red⟩[Nm]Q =  ahorᴺ-ihor $ ahor-✔⇒ᴺ ✔Nm P⊢⟨red⟩[Nm]Q

  ahor-ihor :  P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ (λ v →  Q˙ v)  →
               (∀ v →  Q˙ v  ⊢[ ι ][ j ]⟨ K ᴷ◁ V⇒E v ⟩∞)  →
               P  ⊢[ ι ][ j ]⁺⟨ ĩ₁ (-, K , red) ⟩∞
  ahor-ihor P⊢⟨red⟩Qv =  ahorᴺ-ihor $ ahor-frameʳ P⊢⟨red⟩Qv

  -- Value

  -->  hor-valᵘᴺ :  P  ⊢[ ι ][ i ]⇛  Q˙ v  →   P  ⊢[ ι ]⁺⟨ T / ĩ₀ v ⟩[ κ ]  Q˙

  hor-valᵘ :  P  ⊢[ ι ][ i ]⇛  Q˙ v  →   P  ⊢[ ι ]⁺⟨ T / ĩ₀ v ⟩[ κ ]  Q˙
  hor-valᵘ =  hor-valᵘᴺ ∘ ⇛⇒⇛ᴺ

  hor-val :  P  ⊢[ ι ]  Q˙ v  →   P  ⊢[ ι ]⁺⟨ T / ĩ₀ v ⟩[ κ ]  Q˙
  hor-val P⊢Q =  hor-valᵘ $ ⇒⇛ {i = 0} P⊢Q

  hor-val≡ :  P  ⊢[ ι ]⁺⟨ T / ĩ₀ v ⟩[ κ ] λ u →  ⌜ u ≡ v ⌝
  hor-val≡ =  hor-val $ ⌜⌝-intro refl

  -- Non-deterministic value

  -->  ahor-nd :  {{ Inh ⸨ Xʸ ⸩ʸ }} →  P  ⊢[ ι ][ i ]ᵃ⟨ ndᴿ {Xʸ} ⟩ λ _ →  P

  hor-nd :  {{ Inh ⸨ Xʸ ⸩ʸ }} →  (∀ x →  P ⊢[<ᴾ ι ]⟨ K ᴷ◁ ∇ x ⟩[ κ ] Q˙)  →
            P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , ndᴿ {Xʸ}) ⟩[ κ ]  Q˙
  hor-nd {{InhX}} P⊢⟨Kx⟩Q =  ahor-hor (ahor-nd {i = 0} {{InhX}}) λ _ → P⊢⟨Kx⟩Q _

  -- Pure reduction

  -->  hor-[] :  P  ⊢[<ᴾ ι ]⟨ K ᴷ◁ e ⟩[ κ ]  Q˙  →
  -->            P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , [ e ]ᴿ⟨ b ⟩) ⟩[ κ ]  Q˙

  hor-⇒ᴾ :  e ⇒ᴾ e'  →   P  ⊢[<ᴾ ι ]⟨ e' ⟩[ κ ]  Q˙  →
            P  ⊢[ ι ]⟨ e ⟩[ κ ]  Q˙
  hor-⇒ᴾ (-, redᴾ e⇒K[e₀])  rewrite e⇒K[e₀] =  hor-[]

  -->  ihor-[]○ :  P  ⊢[ ι ][ i ]⟨ K ᴷ◁ e ⟩∞  →
  -->              P  ⊢[ ι ][ i ]⁺⟨ ĩ₁ (-, K , [ e ]ᴿ○) ⟩∞

  -->  ihor-[]● :  P  ⊢[< ι ][ i ]⟨ K ᴷ◁ e ⟩∞  →
  -->              P  ⊢[ ι ][ i ]⁺⟨ ĩ₁ (-, K , [ e ]ᴿ●) ⟩∞

  ihor-[] :  P  ⊢[ ι ][ i ]⟨ K ᴷ◁ e ⟩∞  →
             P  ⊢[ ι ][ i ]⁺⟨ ĩ₁ (-, K , [ e ]ᴿ⟨ b ⟩) ⟩∞
  ihor-[] {b = ff} =  ihor-[]○
  ihor-[] {b = tt} =  ihor-[]● ∘ ⇒<

  ihor-⇒ᴾ○ :  e ⇒ᴾ○ e'  →   P  ⊢[ ι ][ i ]⟨ e' ⟩∞  →   P  ⊢[ ι ][ i ]⟨ e ⟩∞
  ihor-⇒ᴾ○ (redᴾ e⇒K[e₀])  rewrite e⇒K[e₀] =  ihor-[]○

  ihor-⇒ᴾ● :  e ⇒ᴾ● e'  →   P  ⊢[< ι ][ i ]⟨ e' ⟩∞  →   P  ⊢[ ι ][ i ]⟨ e ⟩∞
  ihor-⇒ᴾ● (redᴾ e⇒K[e₀])  rewrite e⇒K[e₀] =  ihor-[]●

  ihor-⇒ᴾ :  e ⇒ᴾ e'  →   P  ⊢[ ι ][ i ]⟨ e' ⟩∞  →   P  ⊢[ ι ][ i ]⟨ e ⟩∞
  ihor-⇒ᴾ (-, redᴾ e⇒K[e₀])  rewrite e⇒K[e₀] =  ihor-[]

  -- Bind

  -->  hor-bind :  P  ⊢[ ι ]⟨ e ⟩[ κ ]  Q˙  →
  -->              (∀ v →  Q˙ v  ⊢[ ι ]⟨ K ᴷ◁ V⇒E v ⟩[ κ ]  R˙)  →
  -->              P  ⊢[ ι ]⟨ K ᴷ◁ e ⟩[ κ ]  R˙

  -->  ihor-bind :  P  ⊢[ ι ][ i ]⟨ e ⟩∞  →   P  ⊢[ ι ][ i ]⟨ K ᴷ◁ e ⟩∞

  -->  hor-ihor-bind :  P  ⊢[ ι ]⟨ e ⟩ᵀ[ i ] Q˙  →
  -->                   (∀ v →  Q˙ v  ⊢[ ι ][ j ]⟨ K ᴷ◁ V⇒E v ⟩∞)  →
  -->                   P  ⊢[ ι ][ j ]⟨ K ᴷ◁ e ⟩∞

  hor-⁏-bind :  P  ⊢[ ι ]⟨ e ⟩[ κ ]  Q˙  →
                (∀ v →  Q˙ v  ⊢[<ᴾ ι ]⟨ e'˂ .! ⟩[ κ ]  R˙)  →
                P  ⊢[ ι ]⟨ _⁏_ {T = T} e e'˂ ⟩[ κ ]  R˙
  hor-⁏-bind {T = ◸ʸ _} P⊢⟨e⟩Q Qv⊢⟨e'⟩R =
    hor-bind {K = •ᴷ ⁏ᴷ _} P⊢⟨e⟩Q λ v → hor-[] $ Qv⊢⟨e'⟩R v
  hor-⁏-bind {T = _ ʸ↷ _} P⊢⟨e⟩Q Qv⊢⟨e'⟩R =
    hor-bind {K = •ᴷ ⁏ᴷ _} P⊢⟨e⟩Q λ v → hor-[] $ Qv⊢⟨e'⟩R v

  ihor-⁏-bind :  P  ⊢[ ι ][ i ]⟨ e ⟩∞  →   P  ⊢[ ι ][ i ]⟨ e ⁏ e'˂ ⟩∞
  ihor-⁏-bind =  ihor-bind {K = •ᴷ ⁏ᴷ _}

  hor-ihor-⁏-bind :  P  ⊢[ ι ]⟨ e ⟩ᵀ[ i ]  Q˙  →
                     (∀ v →  Q˙ v  ⊢[ ι ][ j ]⟨ e'˂ .! ⟩∞)  →
                     P  ⊢[ ι ][ j ]⟨ _⁏_ {T = T} e e'˂ ⟩∞
  hor-ihor-⁏-bind {T = ◸ʸ _} P⊢⟨e⟩Q Qv⊢⟨e'⟩∞ =
    hor-ihor-bind {K = •ᴷ ⁏ᴷ _} P⊢⟨e⟩Q λ v → ihor-[] $ Qv⊢⟨e'⟩∞ v
  hor-ihor-⁏-bind {T = _ ʸ↷ _} P⊢⟨e⟩Q Qv⊢⟨e'⟩∞ =
    hor-ihor-bind {K = •ᴷ ⁏ᴷ _} P⊢⟨e⟩Q λ v → ihor-[] $ Qv⊢⟨e'⟩∞ v

  hor-let-bind :  P  ⊢[ ι ]⟨ e₀ ⟩[ κ ]  Q˙  →
                  (∀ x →  Q˙ x  ⊢[<ᴾ ι ]⟨ e˂˙ x .! ⟩[ κ ]  R˙) →
                  P  ⊢[ ι ]⟨ let˙ e₀ e˂˙ ⟩[ κ ]  R˙
  hor-let-bind P⊢⟨e₀⟩Q Qx⊢⟨ex⟩R =
    hor-bind {K = _ ◁ᴷʳ •ᴷ} P⊢⟨e₀⟩Q λ x → hor-[] $ Qx⊢⟨ex⟩R x

  ihor-let-bind :  P  ⊢[ ι ][ i ]⟨ e₀ ⟩∞  →   P  ⊢[ ι ][ i ]⟨ let˙ e₀ e˂˙ ⟩∞
  ihor-let-bind =  ihor-bind {K = _ ◁ᴷʳ •ᴷ}

  hor-ihor-let-bind :  P  ⊢[ ι ]⟨ e₀ ⟩ᵀ[ i ]  Q˙  →
                       (∀ x →  Q˙ x  ⊢[ ι ][ j ]⟨ e˂˙ x .! ⟩∞) →
                       P  ⊢[ ι ][ j ]⟨ let˙ e₀ e˂˙ ⟩∞
  hor-ihor-let-bind P⊢⟨e₀⟩Q Qx⊢⟨ex⟩∞ =
    hor-ihor-bind {K = _ ◁ᴷʳ •ᴷ} P⊢⟨e₀⟩Q λ x → ihor-[] $ Qx⊢⟨ex⟩∞ x

  -- Transform ⊢[<ᴾ ]⟨ ⟩[ ]

  hor<ᴾ-map :  (∀{ι'} →  P ⊢[ ι' ]⟨ e ⟩[ κ ] Q˙ →  P' ⊢[ ι' ]⟨ e' ⟩[ κ ] Q'˙) →
               P ⊢[<ᴾ ι ]⟨ e ⟩[ κ ] Q˙ →  P' ⊢[<ᴾ ι ]⟨ e' ⟩[ κ ] Q'˙
  hor<ᴾ-map {κ = par} P⊢⟨e⟩Q⇒P'⊢⟨e'⟩Q' =  P⊢⟨e⟩Q⇒P'⊢⟨e'⟩Q' $ᵀʰ_
  hor<ᴾ-map {κ = tot _} P⊢⟨e⟩Q⇒P'⊢⟨e'⟩Q' =  P⊢⟨e⟩Q⇒P'⊢⟨e'⟩Q'
