--------------------------------------------------------------------------------
-- Reduction
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Lang.Reduce (ℓ : Level) where

open import Base.Level using (^_; ↑_)
open import Base.Size using (Size; ∞)
open import Base.Func using (_$_; id)
open import Base.Prod using (∑-syntax; _×_; _,_)
open import Base.Sum using (_⊎_; inj₀; inj₁)
open import Base.Few using (⊤)
open import Shog.Lang.Type ℓ using (Type; ◸_; _➔_; ValGen; Val)
open import Shog.Lang.Expr ℓ using (Addr; Expr; Expr˂; ▶_; ∇*_; λ*˙; _◁_; ★_; _←_;
  Exprᵛ; ⇒Exprᵛ)

private variable
  T U :  Type
  Φ :  ValGen

-------------------------------------------------------------------------------
-- Redex

infix 4 ▶ᴿ_
infixl 0 _◁ᴿ_
infix 8 ★ᴿ_
infix 4 _←ᴿ_

data  Redex (Φ : ValGen) :  Type →  Set (^ ℓ)  where
  ▶ᴿ_ :  Expr˂ Φ ∞ T →  Redex Φ T
  _◁ᴿ_ :  Val (Exprᵛ Φ) (T ➔ U) →  Val (Exprᵛ Φ) T →  Redex Φ U
  ★ᴿ_ :  Addr →  Redex Φ T
  _←ᴿ_ :  Addr →  Val (Exprᵛ Φ) T →  Redex Φ (◸ ⊤)

--------------------------------------------------------------------------------
-- Value & Context-Redex Pair

-- Type for a context-redex pair

Ctxred :  ValGen →  Type →  Set (^ ℓ)
Ctxred Φ T =  ∑ U , (Expr Φ ∞ U → Expr Φ ∞ T) × Redex Φ U

-- Type for either a value or a context-redex pair

Val/Ctxred :  ValGen →  Type →  Set (^ ℓ)
Val/Ctxred Φ T =  Val (Exprᵛ Φ) T ⊎ Ctxred Φ T

-- Calculate the value or context-redex pair of the expression

val/ctxred :  Expr Φ ∞ T →  Val/Ctxred Φ T
val/ctxred {T = T} (∇* a) =  inj₀ $ ⇒Exprᵛ {T = T} a
val/ctxred (λ*˙ e˙) =  inj₀ $ λ*˙ e˙
val/ctxred (▶ e) =  inj₁ $ _ , id , ▶ᴿ e
val/ctxred (e ◁ e') =  inj₁ body
 where
  body :  _
  body  with val/ctxred e'
  ... | inj₁ (_ , ctx , red) =  _ , (λ • → e ◁ ctx •) , red
  ... | inj₀ v'  with val/ctxred e
  ...   | inj₁ (_ , ctx , red) =  _ , (λ • → ctx • ◁ e') , red
  ...   | inj₀ v =  _ , id , (v ◁ᴿ v')
val/ctxred (★ e) =  inj₁ body
 where
  body :  _
  body  with val/ctxred e
  ... | inj₁ (_ , ctx , red) =  _ , (λ • → ★ ctx •) , red
  ... | inj₀ (↑ x) =  _ , id , ★ᴿ x
val/ctxred (_←_ {T = T} e e') =  inj₁ body
 where
  body :  _
  body  with  val/ctxred e'
  ... | inj₁ (_ , ctx , red) =  _ , (λ • → e ← ctx •) , red
  ... | inj₀ v  with val/ctxred e
  ...   | inj₁ (_ , ctx , red) =  _ , (λ • → ctx • ← e') , red
  ...   | inj₀ (↑ x) =  _ , id , (_←ᴿ_ {T = T} x v)
