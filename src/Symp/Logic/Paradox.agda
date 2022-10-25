--------------------------------------------------------------------------------
-- Paradoxes on plausible proof rules
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Symp.Logic.Paradox where

open import Base.Func using (_$_)
open import Base.Eq using (refl)
open import Base.Size using (∞; !)
open import Base.Prod using (-,_)
open import Symp.Lang.Expr using (Type; Expr∞; loop; Val)
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
  X :  Set₀
  T :  Type
  P Q :  Prop∞
  P˂ Q˂ :  Prop˂∞
  Q˙ :  X →  Prop∞
  Q˂˙ :  X →  Prop˂∞

--------------------------------------------------------------------------------
-- Utility

-- If we can turn ○ P into P, then we get P after a fancy update,
-- thanks to □○-new-rec

○-rec :  ○ ¡ᴾ P ⊢[ ∞ ] P →  ⊤' ⊢[ ∞ ][ 0 ]⇛ P
○-rec ○P⊢P =  -∗-introˡ (∗-elimˡ » □-mono ○P⊢P) » □○-new-rec ᵘ»ᵘ □-elim » ○-use

--------------------------------------------------------------------------------
-- If we can use ↪⇛ without level increment, then we get a paradox

module _
  -- ↪⇛-use without level increment
  (↪⇛-use' :  ∀{P˂ Q˂} →  P˂ .!  ∗  (P˂ ↪[ 0 ]⇛ Q˂)  ⊢[ ∞ ][ 0 ]⇛  Q˂ .!)
  where abstract

  -- We can strip ○ from ↪⇛, using ↪⇛-use'

  ○⇒-↪⇛/↪⇛-use' :  ○ ¡ᴾ (P˂ ↪[ 0 ]⇛ Q˂)  ⊢[ ∞ ]  P˂ ↪[ 0 ]⇛ Q˂
  ○⇒-↪⇛/↪⇛-use' =  ○⇒↪⇛ $ ⇒< ↪⇛-use'

  -- Therefore, by ○-rec, we can do any fancy update --- a paradox!

  ⇛/↪⇛-use' :  P  ⊢[ ∞ ][ 0 ]⇛  Q
  ⇛/↪⇛-use' =  ∗⊤-intro »
    ⇛-frameʳ (○-rec ○⇒-↪⇛/↪⇛-use') ᵘ»ᵘ ↪⇛-use' {¡ᴾ _} {¡ᴾ _}

--------------------------------------------------------------------------------
-- If we can use ↪ᵃ⟨ ⟩ without level increment, then we get a paradox

module _ {red : Redex T}
  -- ↪ᵃ⟨⟩-use without level increment
  (↪ᵃ⟨⟩-use' :  ∀{P˂ Q˂˙} →
    P˂ .!  ∗  (P˂ ↪[ 0 ]ᵃ⟨ red ⟩ Q˂˙)  ⊢[ ∞ ][ 0 ]ᵃ⟨ red ⟩ λ v →  Q˂˙ v .!)
  where abstract

  -- We can strip ○ from ↪ᵃ⟨⟩, using ↪ᵃ⟨⟩-use'

  ○⇒-↪ᵃ⟨⟩/↪ᵃ⟨⟩-use' :
    ○ ¡ᴾ (P˂ ↪[ 0 ]ᵃ⟨ red ⟩ Q˂˙)  ⊢[ ∞ ]  P˂ ↪[ 0 ]ᵃ⟨ red ⟩ Q˂˙
  ○⇒-↪ᵃ⟨⟩/↪ᵃ⟨⟩-use' =  ○⇒↪ᵃ⟨⟩ $ ⇒< ↪ᵃ⟨⟩-use'

  -- Therefore, by ○-rec, we have any total Hoare triple --- a paradox!

  ahor/↪ᵃ⟨⟩-use' :  P  ⊢[ ∞ ][ 0 ]ᵃ⟨ red ⟩  Q˙
  ahor/↪ᵃ⟨⟩-use' =  ∗⊤-intro » ⇛-frameʳ (○-rec ○⇒-↪ᵃ⟨⟩/↪ᵃ⟨⟩-use') ᵘ»ᵃʰ
    ↪ᵃ⟨⟩-use' {P˂ = ¡ᴾ _} {λ v → ¡ᴾ _}

--------------------------------------------------------------------------------
-- If we can use ↪⟨ ⟩ᴾ without pure reduction, then we get a paradox

module _ {e : Expr∞ T}
  -- ↪⟨⟩ᴾ-use without pure reduction
  (↪⟨⟩ᴾ-use' :  ∀{P˂ Q˂˙} →
    P˂ .!  ∗  (P˂ ↪⟨ e ⟩ᴾ Q˂˙)  ⊢[ ∞ ]⟨ e ⟩ᴾ λ v →  Q˂˙ v .!)
  where abstract

  -- We can strip ○ from ↪⟨⟩ᴾ, using ↪⟨⟩ᴾ-use'

  ○⇒-↪⟨⟩ᴾ/↪⟨⟩ᴾ-use' :  ○ ¡ᴾ (P˂ ↪⟨ e ⟩ᴾ Q˂˙)  ⊢[ ∞ ]  P˂ ↪⟨ e ⟩ᴾ Q˂˙
  ○⇒-↪⟨⟩ᴾ/↪⟨⟩ᴾ-use' =  ○⇒↪⟨⟩ $ ⇒< ↪⟨⟩ᴾ-use'

  -- Therefore, by ○-rec, we have any partial Hoare triple --- a paradox!

  horᴾ/↪⟨⟩ᴾ-use' :  P  ⊢[ ∞ ]⟨ e ⟩ᴾ  Q˙
  horᴾ/↪⟨⟩ᴾ-use' =  ∗⊤-intro » ⇛-frameʳ (○-rec ○⇒-↪⟨⟩ᴾ/↪⟨⟩ᴾ-use') ᵘ»ʰ
    ↪⟨⟩ᴾ-use' {P˂ = ¡ᴾ _} {λ _ → ¡ᴾ _}

--------------------------------------------------------------------------------
-- If we can use ↪⟨ ⟩ᵀ without level increment, then we get a paradox

module _ {e : Expr∞ T}
  -- ↪⟨⟩ᵀ-use without level increment
  (↪⟨⟩ᵀ-use' :  ∀{P˂ Q˂˙} →
    P˂ .!  ∗  (P˂ ↪⟨ e ⟩ᵀ[ 0 ] Q˂˙)  ⊢[ ∞ ]⟨ e ⟩ᵀ[ 0 ] λ v →  Q˂˙ v .!)
  where abstract

  -- We can strip ○ from ↪⟨⟩ᵀ, using ↪⟨⟩ᵀ-use'

  ○⇒-↪⟨⟩ᵀ/↪⟨⟩ᵀ-use' :  ○ ¡ᴾ (P˂ ↪⟨ e ⟩ᵀ[ 0 ] Q˂˙)  ⊢[ ∞ ]  P˂ ↪⟨ e ⟩ᵀ[ 0 ] Q˂˙
  ○⇒-↪⟨⟩ᵀ/↪⟨⟩ᵀ-use' =  ○⇒↪⟨⟩ $ ⇒< ↪⟨⟩ᵀ-use'

  -- Therefore, by ○-rec, we have any total Hoare triple --- a paradox!

  horᵀ/↪⟨⟩ᵀ-use' :  P  ⊢[ ∞ ]⟨ e ⟩ᵀ[ 0 ]  Q˙
  horᵀ/↪⟨⟩ᵀ-use' =  ∗⊤-intro » ⇛-frameʳ (○-rec ○⇒-↪⟨⟩ᵀ/↪⟨⟩ᵀ-use') ᵘ»ʰ
    ↪⟨⟩ᵀ-use' {P˂ = ¡ᴾ _} {λ _ → ¡ᴾ _}

--------------------------------------------------------------------------------
-- If we can use ↪⟨ ⟩ᵀ with pure reduction, not level increment,
-- then we get a paradox

module _
  -- ↪⟨⟩ᵀ-use with pure reduction, not level increment
  (↪⟨⟩ᵀ-use⇒ᴾ :  ∀{e e' : Expr∞ T} {P˂ Q˂˙} →  e ⇒ᴾ e' →
    P˂ .!  ∗  (P˂ ↪⟨ e' ⟩ᵀ[ 0 ] Q˂˙)  ⊢[ ∞ ]⟨ e ⟩ᵀ[ 0 ] λ v →  Q˂˙ v .!)
  where abstract

  -- We can strip ○ from ↪⟨ loop ⟩ᵀ, using ↪⟨⟩ᵀ-use

  ○⇒-↪⟨loop⟩ᵀ/↪⟨⟩ᵀ-use⇒ᴾ :  ○ ¡ᴾ (P˂ ↪⟨ loop {T = T} ⟩ᵀ[ 0 ] Q˂˙)  ⊢[ ∞ ]
                              P˂ ↪⟨ loop {T = T} ⟩ᵀ[ 0 ] Q˂˙
  ○⇒-↪⟨loop⟩ᵀ/↪⟨⟩ᵀ-use⇒ᴾ =  ○⇒↪⟨⟩ $ ⇒< $ ↪⟨⟩ᵀ-use⇒ᴾ {loop} (-, redᴾ refl)

  -- Therefore, by ○-rec, we have any total Hoare triple for the expression
  -- loop, which is a paradox: Although the total Hoare triple should ensure
  -- termination, loop does not terminate!

  horᵀ-loop/↪⟨⟩ᵀ-use⇒ᴾ :  P  ⊢[ ∞ ]⟨ loop {T = T} ⟩ᵀ[ 0 ]  Q˙
  horᵀ-loop/↪⟨⟩ᵀ-use⇒ᴾ =  ∗⊤-intro »
    ⇛-frameʳ (○-rec ○⇒-↪⟨loop⟩ᵀ/↪⟨⟩ᵀ-use⇒ᴾ) ᵘ»ʰ
    ↪⟨⟩ᵀ-use⇒ᴾ {loop} {P˂ = ¡ᴾ _} {λ _ → ¡ᴾ _} (-, redᴾ refl)

--------------------------------------------------------------------------------
-- If we can use ↪⟨ ⟩∞ without level increment, then we get a paradox

module _ {e : Expr∞ T}
  -- ↪⟨⟩∞-use without level increment
  (↪⟨⟩∞-use' :  ∀{P˂} →  P˂ .!  ∗  (P˂ ↪[ 0 ]⟨ e ⟩∞)  ⊢[ ∞ ][ 0 ]⟨ e ⟩∞)
  where abstract

  -- We can strip ○ from ↪⟨⟩∞, using ↪⟨⟩∞-use'

  ○⇒-↪⟨⟩∞/↪⟨⟩∞-use' :  ○ ¡ᴾ (P˂ ↪[ 0 ]⟨ e ⟩∞)  ⊢[ ∞ ]  P˂ ↪[ 0 ]⟨ e ⟩∞
  ○⇒-↪⟨⟩∞/↪⟨⟩∞-use' =  ○⇒↪⟨⟩∞ $ ⇒< ↪⟨⟩∞-use'

  -- Therefore, by ○-rec, we have any total Hoare triple --- a paradox!

  ihor/↪⟨⟩∞-use' :  P  ⊢[ ∞ ][ 0 ]⟨ e ⟩∞
  ihor/↪⟨⟩∞-use' =  ∗⊤-intro »
    ⇛-frameʳ (○-rec ○⇒-↪⟨⟩∞/↪⟨⟩∞-use') ᵘ»ⁱʰ ↪⟨⟩∞-use' {P˂ = ¡ᴾ _}
