--------------------------------------------------------------------------------
-- Expression
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Lang.Expr (ℓ : Level) where

open import Base.Level using (^_; ↑_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk; !)
open import Base.Func using (_$_)
open import Base.Few using (⊤)
open import Shog.Lang.Type ℓ using (Type; ◸_; _➔_; VtyGen; Vty*; Vty)

private variable
  A :  Set ℓ
  ι :  Size
  T U :  Type
  Φ :  VtyGen

--------------------------------------------------------------------------------
-- Addr: Address

record  Addr (A : Set ℓ) :  Set ℓ  where

--------------------------------------------------------------------------------
-- Expr: Expression, possibly infinite, in PHOAS

data  Expr (Φ : VtyGen) (ι : Size) :  Type →  Set (^ ℓ)

-- Expr˂: Expr under Thunk
Expr˂ :  VtyGen →  Size →  Type →  Set (^ ℓ)
Expr˂ Φ ι T =  Thunk (λ ι → Expr Φ ι T) ι

infix 4 ▶_ ∇*_ ∇_
infix 8 ★_
infix 4 _←_
infixl 0 _◁_

data  Expr Φ ι  where
  -- Later, for infinite construction
  ▶_ :  Expr˂ Φ ι T →  Expr Φ ι T
  -- Turn a value into an expression
  ∇*_ :  Vty Φ T →  Expr Φ ι T
  -- Lambda abstraction over a value
  λ*˙ :  (Vty Φ T → Expr Φ ι U) →  Expr Φ ι (T ➔ U)
  -- Application
  _◁_ :  Expr Φ ι (T ➔ U) →  Expr Φ ι T →  Expr Φ ι U
  -- Read from the memory
  ★_ :  Expr Φ ι (◸ Addr A) →  Expr Φ ι (◸ A)
  -- Write to the memory
  _←_ :  Expr Φ ι (◸ Addr A) →  Expr Φ ι (◸ A) →  Expr Φ ι (◸ ⊤)

-- ∇* for a pure value
∇_ :  A →  Expr Φ ι (◸ A)
∇ a =  ∇* ↑ a

-- λ*˙ for a pure value
λ˙ :  (A → Expr Φ ι T) →  Expr Φ ι (◸ A ➔ T)
λ˙ e˙ =  λ*˙ $ λ (↑ a) → e˙ a

-- Syntax for lambda abstraction, for a general / pure value
λ*-syntax :  (Vty Φ T → Expr Φ ι U) →  Expr Φ ι (T ➔ U)
λ*-syntax =  λ*˙
λ-syntax :  (A → Expr Φ ι T) →  Expr Φ ι (◸ A ➔ T)
λ-syntax =  λ˙
infix 3 λ*-syntax λ-syntax
syntax λ*-syntax (λ x → e) =  λ* x , e
syntax λ-syntax (λ x → e) =  λ' x , e

-- Let binding for a general / pure value
let*-syntax :  Expr Φ ι T →  (Vty Φ T → Expr Φ ι U) →  Expr Φ ι U
let*-syntax e₀ e˙ =  λ*˙ e˙ ◁ e₀
let-syntax :  Expr Φ ι (◸ A) →  (A → Expr Φ ι T) →  Expr Φ ι T
let-syntax e₀ e˙ =  λ˙ e˙ ◁ e₀
infix 3 let*-syntax let-syntax
syntax let*-syntax e₀ (λ x → e) =  let* x := e₀ in' e
syntax let-syntax e₀ (λ x → e) =  let' x := e₀ in' e

--------------------------------------------------------------------------------
-- For β-reduction

-- Exprᵛ Φ: VtyGen that maps non-pure T to Expr Φ ∞ T
Exprᵛ :  VtyGen →  VtyGen
Exprᵛ Φ .Vty* T =  Expr Φ ∞ T

-- Conversion functions for Exprᵛ
Exprᵛ⇒Expr :  Vty (Exprᵛ Φ) T →  Expr Φ ∞ T
Exprᵛ⇒Expr {T = ◸ _} a =  ∇* a
Exprᵛ⇒Expr {T = _ ➔ _} e =  e
⇒Exprᵛ :  Vty Φ T →  Vty (Exprᵛ Φ) T
⇒Exprᵛ {T = ◸ _} a =  a
⇒Exprᵛ {T = _ ➔ _} a =  ∇* a

-- Core of substitution
squash :  Expr (Exprᵛ Φ) ι T →  Expr Φ ι T
squash (▶ e˂) =  ▶ λ{ .! → squash (e˂ .!) }
squash (∇* e) =  Exprᵛ⇒Expr e
squash {T = T ➔ _} (λ*˙ e˙) =  λ*˙ $ λ a → squash (e˙ (⇒Exprᵛ {T = T} a))
squash (e ◁ e') =  squash e ◁ squash e'
squash (★ e) =  ★ squash e
squash (e ← e') =  squash e ← squash e'
