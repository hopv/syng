--------------------------------------------------------------------------------
-- Proof rules on the Hoare triples
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Hor where

open import Base.Func using (_$_; _∘_; const)
open import Base.Dec using (Inh)
open import Base.Size using (Size; !)
open import Base.Prod using (_,_; -,_)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Base.Nat using (ℕ)
open import Base.Sety using (Setʸ; ⸨_⸩ʸ)
open import Syho.Logic.Prop using (WpKind; par; tot; Prop∞; _∗_; [⊤]ᴺ)
open import Syho.Logic.Core using (_⊢[_]_; _»_; ∗-comm)
open import Syho.Logic.Supd using (_⊢[_][_]⇛_; ⊢⇒⊢⇛; ⇛-refl; ⇛⇒⇛ᴺ)
open import Syho.Lang.Expr using (Type; ◸ʸ_; _ʸ↷_; Expr∞; ∇_; _⁏_; let˙; V⇒E)
open import Syho.Lang.Ktxred using (Redex; ndᴿ; [_]ᴿ; Ktx; •ᴷ; _◁ᴷʳ_; _⁏ᴷ_;
  _ᴷ◁_; Val/Ktxred)

-- Import and re-export
open import Syho.Logic.Judg public using ([_]ᵃ⟨_⟩_; ⁺⟨_⟩[_]_; _⊢[_][_]ᵃ⟨_⟩_;
  _⊢[<_][_]ᵃ⟨_⟩_; _⊢[_]⁺⟨_⟩[_]_; _⊢[_]⁺⟨_/_⟩[_]_; _⊢[_]⁺⟨_⟩ᴾ_; _⊢[_]⁺⟨_⟩ᵀ[_]_;
  _⊢[_]⟨_⟩[_]_; _⊢[<_]⟨_⟩[_]_; _⊢[_]⟨_⟩ᴾ_; _⊢[<_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ[_]_;
  _⊢[<_]⟨_⟩ᵀ[_]_; hor-ᵀ⇒ᴾ; ahor-ṡ; horᵀ-ṡ; _ᵘ»ᵃʰ_; _ᵘᴺ»ʰ_; _ᵃʰ»ᵘ_; _ʰ»ᵘᴺ_;
  ahor-frameˡ; hor-frameˡ; ahor-horᴾ; ahor-horᵀ; hor-bind; hor-valᵘᴺ; ahor-nd;
  horᴾ-[]; horᵀ-[]; hor-fork)

private variable
  ι :  Size
  i j :  ℕ
  X :  Set₀
  Xʸ :  Setʸ
  T U :  Type
  κ :  WpKind
  P P' Q R :  Prop∞
  Q˙ Q'˙ R˙ :  X → Prop∞
  red :  Redex T
  vk :  Val/Ktxred T
  K :  Ktx T U
  e e' e₀ :  Expr∞ T
  e˙ :  X → Expr∞ T
  v :  X

infixr -1 _ᵃʰ»_ _ʰ»_

abstract

  -->  hor-ᵀ⇒ᴾ :  P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ  Q˙  →   P  ⊢[ ι ]⁺⟨ vk ⟩ᴾ  Q˙

  -->  horᵀ-ṡ :  P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ i ]  Q˙  →   P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ[ ṡ i ]  Q˙

  -->  hor-bind :  P  ⊢[ ι ]⟨ e ⟩[ κ ]  Q˙  →
  -->              (∀ v →  Q˙ v  ⊢[ ι ]⟨ K ᴷ◁ V⇒E v ⟩[ κ ]  R˙)  →
  -->              P  ⊢[ ι ]⟨ K ᴷ◁ e ⟩[ κ ]  R˙

  -->  hor-fork :  P  ⊢[ ι ]⟨ K ᴷ◁ ∇ _ ⟩[ κ ]  R˙  →
  -->              Q  ⊢[ ι ]⟨ e ⟩[ κ ]  (λ _ → ⊤')  →
  -->              P  ∗  Q  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , forkᴿ e) ⟩[ κ ]  R˙

  -- Compose

  -->  _ᵘ»ᵃʰ_ :  P  ⊢[ ι ][ j ]⇛  Q  →   Q  ⊢[ ι ][ i ]ᵃ⟨ red ⟩  R˙  →
  -->            P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩  R˙

  -->  _ᵘᴺ»ʰ_ :  P  ⊢[ ι ][ i ]⇛ᴺ  Q  →   Q  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  R˙  →
  -->            P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  R˙

  _ᵘ»ʰ_ :  P  ⊢[ ι ][ i ]⇛  Q  →   Q  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  R˙  →
           P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  R˙
  _ᵘ»ʰ_ =  _ᵘᴺ»ʰ_ ∘  ⇛⇒⇛ᴺ

  -->  _ᵃʰ»ᵘ_ :  P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩  Q˙  →
  -->            (∀ v →  Q˙ v  ⊢[ ι ][ j ]⇛  R˙ v)  →
  -->            P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩  R˙

  _ᵃʰ»_ :  P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩  Q˙  →   (∀ v →  Q˙ v  ⊢[ ι ]  R˙ v)  →
           P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩  R˙
  P⊢⟨red⟩Q ᵃʰ» ∀vQ⊢R =  P⊢⟨red⟩Q ᵃʰ»ᵘ λ _ → ⊢⇒⊢⇛ {i = 0} $ ∀vQ⊢R _

  -->  _ʰ»ᵘᴺ_ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  Q˙  →
  -->            (∀ v →  Q˙ v  ⊢[ ι ][ j ]⇛ᴺ  R˙ v)  →
  -->            P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  R˙

  _ʰ»ᵘ_ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  Q˙  →   (∀ v →  Q˙ v  ⊢[ ι ][ j ]⇛  R˙ v)  →
           P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  R˙
  _ʰ»ᵘ_ P⊢⟨vk⟩Q =  (P⊢⟨vk⟩Q ʰ»ᵘᴺ_) ∘ (⇛⇒⇛ᴺ ∘_)

  _ʰ»_ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  Q˙  →   (∀ v →  Q˙ v  ⊢[ ι ]  R˙ v)  →
          P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  R˙
  P⊢⟨vk⟩Q ʰ» ∀vQ⊢R =  P⊢⟨vk⟩Q ʰ»ᵘ λ _ → ⊢⇒⊢⇛ {i = 0} $ ∀vQ⊢R _

  -- Frame

  -->  ahor-frameˡ :  P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩  Q˙  →
  -->                 R  ∗  P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ λ v →  R  ∗  Q˙ v

  ahor-frameʳ :  P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩  Q˙  →
                 P  ∗  R  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ λ v →  Q˙ v  ∗  R
  ahor-frameʳ P⊢⟨red⟩Q =  ∗-comm » ahor-frameˡ P⊢⟨red⟩Q ᵃʰ» λ _ → ∗-comm

  -->  hor-frameˡ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  Q˙  →
  -->                R  ∗  P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ] λ v →  R  ∗  Q˙ v

  hor-frameʳ :  P  ⊢[ ι ]⁺⟨ vk ⟩[ κ ]  Q˙  →
                P  ∗  R  ⊢[ ι ]⁺⟨ vk ⟩[ κ ] λ v →  Q˙ v  ∗  R
  hor-frameʳ P⊢⟨vk⟩Q =  ∗-comm » hor-frameˡ P⊢⟨vk⟩Q ʰ» λ _ → ∗-comm

  -- Compose an atomic Hoare triple with a Hoare triple on the context

  -->  ahor-horᴾ :  (P ∗ [⊤]ᴺ  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ λ v →  Q˙ v ∗ [⊤]ᴺ)  →
  -->               (∀ v →  Q˙ v  ⊢[< ι ]⟨ K ᴷ◁ V⇒E v ⟩ᴾ  R˙)  →
  -->               P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , red) ⟩ᴾ  R˙

  -->  ahor-horᵀ :  (P ∗ [⊤]ᴺ  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ λ v →  Q˙ v ∗ [⊤]ᴺ)  →
  -->               (∀ v →  Q˙ v  ⊢[ ι ]⟨ K ᴷ◁ V⇒E v ⟩ᵀ[ j ]  R˙)  →
  -->               P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , red) ⟩ᵀ[ j ]  R˙

  ahor-hor :  (P ∗ [⊤]ᴺ  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ λ v →  Q˙ v ∗ [⊤]ᴺ)  →
              (∀ v →  Q˙ v  ⊢[ ι ]⟨ K ᴷ◁ V⇒E v ⟩[ κ ]  R˙)  →
              P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , red) ⟩[ κ ]  R˙
  ahor-hor {κ = par} ⊢⟨red⟩ ⊢⟨Kv⟩ =  ahor-horᴾ ⊢⟨red⟩ λ{ v .! → ⊢⟨Kv⟩ v }
  ahor-hor {κ = tot _} =  ahor-horᵀ

  -- Value

  -->  hor-valᵘᴺ :  P  ⊢[ ι ][ i ]⇛  Q˙ v  →   P  ⊢[ ι ]⁺⟨ T / ĩ₀ v ⟩[ κ ]  Q˙

  hor-valᵘ :  P  ⊢[ ι ][ i ]⇛  Q˙ v  →   P  ⊢[ ι ]⁺⟨ T / ĩ₀ v ⟩[ κ ]  Q˙
  hor-valᵘ =  hor-valᵘᴺ ∘ ⇛⇒⇛ᴺ

  hor-val :  P  ⊢[ ι ]  Q˙ v  →   P  ⊢[ ι ]⁺⟨ T / ĩ₀ v ⟩[ κ ]  Q˙
  hor-val P⊢Q =  hor-valᵘ $ ⊢⇒⊢⇛ {i = 0} P⊢Q

  -- Non-deterministic value

  -->  ahor-nd :  {{ Inh ⸨ Xʸ ⸩ʸ }} →  P  ⊢[ ι ][ i ]ᵃ⟨ ndᴿ {Xʸ} ⟩ λ _ →  P

  hor-nd :  {{ Inh ⸨ Xʸ ⸩ʸ }} →  (∀ x →  P ⊢[ ι ]⟨ K ᴷ◁ ∇ x ⟩[ κ ] Q˙)  →
            P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , ndᴿ {Xʸ}) ⟩[ κ ]  Q˙
  hor-nd {{InhXʸ}} P⊢⟨Kx⟩Q =
    ahor-hor (ahor-frameʳ $ ahor-nd {i = 0} {{InhXʸ}}) λ _ → P⊢⟨Kx⟩Q _

  -- Pure reduction

  -->  horᴾ-[] :  P  ⊢[< ι ]⟨ K ᴷ◁ e ⟩ᴾ  Q˙  →
  -->             P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , [ e ]ᴿ) ⟩ᴾ  Q˙

  -->  horᵀ-[] :  P  ⊢[ ι ]⟨ K ᴷ◁ e ⟩[ κ ]  Q˙  →
  -->             P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , [ e ]ᴿ) ⟩[ κ ]  Q˙

  hor-[] :  P  ⊢[ ι ]⟨ K ᴷ◁ e ⟩[ κ ]  Q˙  →
            P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , [ e ]ᴿ) ⟩[ κ ]  Q˙
  hor-[] {κ = par} P⊢⟨Ke⟩Q =  horᴾ-[] λ{ .! → P⊢⟨Ke⟩Q }
  hor-[] {κ = tot _} =  horᵀ-[]

  -- Sequential execution

  hor-⁏-bind :  P  ⊢[ ι ]⟨ e ⟩[ κ ]  const Q  →   Q  ⊢[ ι ]⟨ e' ⟩[ κ ]  R˙  →
                P  ⊢[ ι ]⟨ _⁏_ {T = T} e e' ⟩[ κ ]  R˙
  hor-⁏-bind {T = ◸ʸ _} P⊢⟨e⟩Q Q⊢⟨e'⟩R =
    hor-bind {K = •ᴷ ⁏ᴷ _} P⊢⟨e⟩Q λ _ → hor-[] Q⊢⟨e'⟩R
  hor-⁏-bind {T = _ ʸ↷ _} P⊢⟨e⟩Q Q⊢⟨e'⟩R =
    hor-bind {K = •ᴷ ⁏ᴷ _} P⊢⟨e⟩Q λ _ → hor-[] Q⊢⟨e'⟩R

  -- Let binding

  hor-let-bind :  P  ⊢[ ι ]⟨ e₀ ⟩[ κ ]  Q˙  →
                  (∀ x →  Q˙ x  ⊢[ ι ]⟨ e˙ x ⟩[ κ ]  R˙) →
                  P  ⊢[ ι ]⟨ let˙ e₀ e˙ ⟩[ κ ]  R˙
  hor-let-bind P⊢⟨e₀⟩Q ∀xQ⊢⟨e˙⟩R =
    hor-bind {K = _ ◁ᴷʳ •ᴷ} P⊢⟨e₀⟩Q λ x → hor-[] $ ∀xQ⊢⟨e˙⟩R x
