--------------------------------------------------------------------------------
-- Paradoxes on plausible proof rules
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Symp.Logic.Paradox where

open import Base.Func using (_$_)
open import Base.Eq using (refl)
open import Base.Size using (𝕊; !)
open import Base.Prod using (-,_)
open import Base.Nat using (ℕ)
open import Symp.Lang.Expr using (Type; Expr∞; Expr˂∞; loop; Val)
open import Symp.Lang.Ktxred using (Redex)
open import Symp.Lang.Reduce using (_⇒ᴾ_; redᴾ)
open import Symp.Logic.Prop using (Prop∞; Prop˂∞; ¡ᴾ_; ⊤'; □_; _∗_; ○_; _↪[_]⇛_;
  _↪[_]ᵃ⟨_⟩_; _↪⟨_⟩ᴾ_; _↪⟨_⟩ᵀ[_]_; _↪[_]⟨_⟩∞)
open import Symp.Logic.Core using (_⊢[_]_; ⇒<; _»_; -∗-introˡ; ∗-elimˡ;
  ∗⊤-intro; □-mono; □-elim)
open import Symp.Logic.Fupd using (_⊢[_][_]⇛_; _ᵘ»ᵘ_; _ᵘ»_; ⇛-frameʳ)
open import Symp.Logic.Hor using (_⊢[_][_]ᵃ⟨_⟩_; _⊢[_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ[_]_;
  _⊢[_][_]⟨_⟩∞; _ᵘ»ᵃʰ_; _ᵘ»ʰ_; _ᵘ»ⁱʰ_)
open import Symp.Logic.Ind using (○-mono; □○-new-rec; ○-use; ○⇒↪⇛; ○⇒↪ᵃ⟨⟩;
  ○⇒↪⟨⟩; ○⇒↪⟨⟩∞)

private variable
  ι :  𝕊
  i :  ℕ
  X :  Set₀
  T :  Type
  red :  Redex T
  e :  Expr∞ T
  P Q :  Prop∞
  P˂ Q˂ :  Prop˂∞
  Q˙ :  X →  Prop∞
  Q˂˙ :  X →  Prop˂∞

--------------------------------------------------------------------------------
-- Utility

-- If we can turn ○ P into P, then we get P after a fancy update,
-- thanks to □○-new-rec

○-rec :  ○ ¡ᴾ P ⊢[ ι ] P →  ⊤' ⊢[ ι ][ i ]⇛ P
○-rec ○P⊢P =  -∗-introˡ (∗-elimˡ » □-mono ○P⊢P) » □○-new-rec ᵘ»ᵘ □-elim » ○-use

--------------------------------------------------------------------------------
-- If we can use ↪⇛ without level increment, then we get a paradox

module _
  -- ↪⇛-use without level increment
  (↪⇛-use' :  ∀{P˂ Q˂ ι i} →  P˂ .!  ∗  (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ][ i ]⇛  Q˂ .!)
  where abstract

  -- We can strip ○ from ↪⇛, using ↪⇛-use'

  ○⇒-↪⇛/↪⇛-use' :  ○ ¡ᴾ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ]  P˂ ↪[ i ]⇛ Q˂
  ○⇒-↪⇛/↪⇛-use' =  ○⇒↪⇛ $ ⇒< ↪⇛-use'

  -- Therefore, by ○-rec, we can do any fancy update --- a paradox!

  ⇛/↪⇛-use' :  P  ⊢[ ι ][ i ]⇛  Q
  ⇛/↪⇛-use' =  ∗⊤-intro »
    ⇛-frameʳ (○-rec ○⇒-↪⇛/↪⇛-use') ᵘ»ᵘ ↪⇛-use' {¡ᴾ _} {¡ᴾ _}

--------------------------------------------------------------------------------
-- If we can use ↪ᵃ⟨ ⟩ without level increment, then we get a paradox

module _
  -- ↪ᵃ⟨⟩-use without level increment
  (↪ᵃ⟨⟩-use' :  ∀{T} {red : Redex T} {P˂ Q˂˙ i ι} →
    P˂ .!  ∗  (P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙)  ⊢[ ι ][ i ]ᵃ⟨ red ⟩ λ v →  Q˂˙ v .!)
  where abstract

  -- We can strip ○ from ↪ᵃ⟨⟩, using ↪ᵃ⟨⟩-use'

  ○⇒-↪ᵃ⟨⟩/↪ᵃ⟨⟩-use' :
    ○ ¡ᴾ (P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙)  ⊢[ ι ]  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙
  ○⇒-↪ᵃ⟨⟩/↪ᵃ⟨⟩-use' =  ○⇒↪ᵃ⟨⟩ $ ⇒< ↪ᵃ⟨⟩-use'

  -- Therefore, by ○-rec, we have any total Hoare triple --- a paradox!

  ahor/↪ᵃ⟨⟩-use' :  P  ⊢[ ι ][ i ]ᵃ⟨ red ⟩  Q˙
  ahor/↪ᵃ⟨⟩-use' =  ∗⊤-intro » ⇛-frameʳ (○-rec {i = 0} ○⇒-↪ᵃ⟨⟩/↪ᵃ⟨⟩-use') ᵘ»ᵃʰ
    ↪ᵃ⟨⟩-use' {P˂ = ¡ᴾ _} {λ v → ¡ᴾ _}

--------------------------------------------------------------------------------
-- If we can use ↪⟨ ⟩ᴾ without pure reduction, then we get a paradox

module _
  -- ↪⟨⟩ᴾ-use without pure reduction
  (↪⟨⟩ᴾ-use' :  ∀{T} {e : Expr∞ T} {P˂ Q˂˙ ι} →
    P˂ .!  ∗  (P˂ ↪⟨ e ⟩ᴾ Q˂˙)  ⊢[ ι ]⟨ e ⟩ᴾ λ v →  Q˂˙ v .!)
  where abstract

  -- We can strip ○ from ↪⟨⟩ᴾ, using ↪⟨⟩ᴾ-use'

  ○⇒-↪⟨⟩ᴾ/↪⟨⟩ᴾ-use' :  ○ ¡ᴾ (P˂ ↪⟨ e ⟩ᴾ Q˂˙)  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q˂˙
  ○⇒-↪⟨⟩ᴾ/↪⟨⟩ᴾ-use' =  ○⇒↪⟨⟩ $ ⇒< ↪⟨⟩ᴾ-use'

  -- Therefore, by ○-rec, we have any partial Hoare triple --- a paradox!

  horᴾ/↪⟨⟩ᴾ-use' :  P  ⊢[ ι ]⟨ e ⟩ᴾ  Q˙
  horᴾ/↪⟨⟩ᴾ-use' =  ∗⊤-intro » ⇛-frameʳ (○-rec {i = 0} ○⇒-↪⟨⟩ᴾ/↪⟨⟩ᴾ-use') ᵘ»ʰ
    ↪⟨⟩ᴾ-use' {P˂ = ¡ᴾ _} {λ _ → ¡ᴾ _}

--------------------------------------------------------------------------------
-- If we can use ↪⟨ ⟩ᵀ without level increment, then we get a paradox

module _
  -- ↪⟨⟩ᵀ-use without level increment
  (↪⟨⟩ᵀ-use' :  ∀{T} {e : Expr∞ T} {P˂ Q˂˙ i ι} →
    P˂ .!  ∗  (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙)  ⊢[ ι ]⟨ e ⟩ᵀ[ i ] λ v →  Q˂˙ v .!)
  where abstract

  -- We can strip ○ from ↪⟨⟩ᵀ, using ↪⟨⟩ᵀ-use'

  ○⇒-↪⟨⟩ᵀ/↪⟨⟩ᵀ-use' :  ○ ¡ᴾ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙)  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙
  ○⇒-↪⟨⟩ᵀ/↪⟨⟩ᵀ-use' =  ○⇒↪⟨⟩ $ ⇒< ↪⟨⟩ᵀ-use'

  -- Therefore, by ○-rec, we have any total Hoare triple --- a paradox!

  horᵀ/↪⟨⟩ᵀ-use' :  P  ⊢[ ι ]⟨ e ⟩ᵀ[ i ]  Q˙
  horᵀ/↪⟨⟩ᵀ-use' =  ∗⊤-intro » ⇛-frameʳ (○-rec {i = 0} ○⇒-↪⟨⟩ᵀ/↪⟨⟩ᵀ-use') ᵘ»ʰ
    ↪⟨⟩ᵀ-use' {P˂ = ¡ᴾ _} {λ _ → ¡ᴾ _}

--------------------------------------------------------------------------------
-- If we can use ↪⟨ ⟩ᵀ with pure reduction, not level increment,
-- then we get a paradox

module _
  -- ↪⟨⟩ᵀ-use with pure reduction, not level increment
  (↪⟨⟩ᵀ-use⇒ᴾ :  ∀{T} {e e' : Expr∞ T} {P˂ Q˂˙ i ι} →  e ⇒ᴾ e' →
    P˂ .!  ∗  (P˂ ↪⟨ e' ⟩ᵀ[ i ] Q˂˙)  ⊢[ ι ]⟨ e ⟩ᵀ[ i ] λ v →  Q˂˙ v .!)
  where abstract

  -- We can strip ○ from ↪⟨ loop ⟩ᵀ, using ↪⟨⟩ᵀ-use

  ○⇒-↪⟨loop⟩ᵀ/↪⟨⟩ᵀ-use⇒ᴾ :  ○ ¡ᴾ (P˂ ↪⟨ loop {T = T} ⟩ᵀ[ i ] Q˂˙)  ⊢[ ι ]
                              P˂ ↪⟨ loop {T = T} ⟩ᵀ[ i ] Q˂˙
  ○⇒-↪⟨loop⟩ᵀ/↪⟨⟩ᵀ-use⇒ᴾ =  ○⇒↪⟨⟩ $ ⇒< $ ↪⟨⟩ᵀ-use⇒ᴾ {e = loop} (-, redᴾ refl)

  -- Therefore, by ○-rec, we have any total Hoare triple for the expression
  -- loop, which is a paradox: Although the total Hoare triple should ensure
  -- termination, loop does not terminate!

  horᵀ-loop/↪⟨⟩ᵀ-use⇒ᴾ :  P  ⊢[ ι ]⟨ loop ⟩ᵀ[ i ]  Q˙
  horᵀ-loop/↪⟨⟩ᵀ-use⇒ᴾ =  ∗⊤-intro »
    ⇛-frameʳ (○-rec {i = 0} ○⇒-↪⟨loop⟩ᵀ/↪⟨⟩ᵀ-use⇒ᴾ) ᵘ»ʰ
    ↪⟨⟩ᵀ-use⇒ᴾ {e = loop} {P˂ = ¡ᴾ _} {λ _ → ¡ᴾ _} (-, redᴾ refl)

--------------------------------------------------------------------------------
-- If we can use ↪⟨ ⟩∞ without level increment, then we get a paradox

module _
  -- ↪⟨⟩∞-use without level increment
  (↪⟨⟩∞-use' :  ∀{T} {e : Expr∞ T} {P˂ i ι} →
    P˂ .!  ∗  (P˂ ↪[ i ]⟨ e ⟩∞)  ⊢[ ι ][ i ]⟨ e ⟩∞)
  where abstract

  -- We can strip ○ from ↪⟨⟩∞, using ↪⟨⟩∞-use'

  ○⇒-↪⟨⟩∞/↪⟨⟩∞-use' :  ○ ¡ᴾ (P˂ ↪[ i ]⟨ e ⟩∞)  ⊢[ ι ]  P˂ ↪[ i ]⟨ e ⟩∞
  ○⇒-↪⟨⟩∞/↪⟨⟩∞-use' =  ○⇒↪⟨⟩∞ $ ⇒< ↪⟨⟩∞-use'

  -- Therefore, by ○-rec, we have any total Hoare triple --- a paradox!

  ihor/↪⟨⟩∞-use' :  P  ⊢[ ι ][ i ]⟨ e ⟩∞
  ihor/↪⟨⟩∞-use' =  ∗⊤-intro »
    ⇛-frameʳ (○-rec {i = 0} ○⇒-↪⟨⟩∞/↪⟨⟩∞-use') ᵘ»ⁱʰ ↪⟨⟩∞-use' {P˂ = ¡ᴾ _}
