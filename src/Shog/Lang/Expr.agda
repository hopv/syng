--------------------------------------------------------------------------------
-- Expression
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Lang.Expr (ℓ : Level) where

open import Base.Level using (^ˡ_; ↑ˡ_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk; !)
open import Base.Func using (_$_)
open import Base.Few using (⊤)
open import Shog.Lang.Type ℓ using (Type; ⌜_⌝ᵀ; _*→*_; _→*_; VTF; Vt*; Vt)

private variable
  A :  Set ℓ
  ι :  Size
  T U :  Type
  Φ :  VTF

--------------------------------------------------------------------------------
-- Addr: Address

record  Addr (A : Set ℓ) :  Set ℓ  where

--------------------------------------------------------------------------------
-- Expr*: Expression, possibly infinite, in PHOAS

data  Expr* (Φ : VTF) (ι : Size) :  Type →  Set (^ˡ ℓ)

-- Expr˂*: Expr* under Thunk
Expr˂* :  VTF →  Size →  Type →  Set (^ˡ ℓ)
Expr˂* Φ ι T =  Thunk (λ ι → Expr* Φ ι T) ι

-- Expr / Expr˂: Expr* / Expr˂* over a pure type
Expr Expr˂ :  VTF →  Size →  Set ℓ →  Set (^ˡ ℓ)
Expr Φ ι A =  Expr* Φ ι ⌜ A ⌝ᵀ
Expr˂ Φ ι A =  Expr˂* Φ ι ⌜ A ⌝ᵀ

infix 4 ▸_ ∇*_ ∇_
infix 8 ★_
infix 4 _←_
infixl 0 _◁_

data  Expr* Φ ι  where
  -- Later, for infinite construction
  ▸_ :  Expr˂* Φ ι T →  Expr* Φ ι T
  -- Turn a value into an expression
  ∇*_ :  Vt Φ T →  Expr* Φ ι T
  -- Lambda abstraction over a value
  λ*˙ :  (Vt Φ T → Expr* Φ ι U) →  Expr* Φ ι (T *→* U)
  -- Application
  _◁_ :  Expr* Φ ι (T *→* U) →  Expr* Φ ι T →  Expr* Φ ι U
  -- Read from the memory
  ★_ :  Expr Φ ι (Addr A) →  Expr Φ ι A
  -- Write to the memory
  _←_ :  Expr Φ ι (Addr A) →  Expr Φ ι A →  Expr Φ ι ⊤

-- ∇* for a pure value
∇_ :  A →  Expr Φ ι A
∇ a =  ∇* ↑ˡ a

-- λ*˙ for a pure value
λ˙ :  (A → Expr* Φ ι T) →  Expr* Φ ι (A →* T)
λ˙ e˙ =  λ*˙ $ λ (↑ˡ a) → e˙ a

-- Syntax for lambda abstraction, for a general / pure value
λ*-syntax :  (Vt Φ T → Expr* Φ ι U) →  Expr* Φ ι (T *→* U)
λ*-syntax =  λ*˙
λ-syntax :  (A → Expr* Φ ι T) →  Expr* Φ ι (A →* T)
λ-syntax =  λ˙
infix 3 λ*-syntax λ-syntax
syntax λ*-syntax (λ x → e) =  λ* x , e
syntax λ-syntax (λ x → e) =  λ' x , e

-- Let binding for a general / pure value
let*-syntax :  Expr* Φ ι T →  (Vt Φ T → Expr* Φ ι U) →  Expr* Φ ι U
let*-syntax e₀ e˙ =  λ*˙ e˙ ◁ e₀
let-syntax :  Expr Φ ι A →  (A → Expr* Φ ι T) →  Expr* Φ ι T
let-syntax e₀ e˙ =  λ˙ e˙ ◁ e₀
infix 3 let*-syntax let-syntax
syntax let*-syntax e₀ (λ x → e) =  let* x := e₀ in' e
syntax let-syntax e₀ (λ x → e) =  let' x := e₀ in' e

--------------------------------------------------------------------------------
-- For β-reduction

-- ExprVtf Φ: VTF that maps non-pure T to Expr* Φ ∞ T
ExprVtf :  VTF →  VTF
ExprVtf Φ .Vt* T =  Expr* Φ ∞ T

-- Conversion functions for ExprVtf
ExprVtf⇒Expr :  Vt (ExprVtf Φ) T →  Expr* Φ ∞ T
ExprVtf⇒Expr {T = ⌜ _ ⌝ᵀ} a =  ∇* a
ExprVtf⇒Expr {T = _ *→* _} e =  e
⇒ExprVtf :  Vt Φ T →  Vt (ExprVtf Φ) T
⇒ExprVtf {T = ⌜ _ ⌝ᵀ} a =  a
⇒ExprVtf {T = _ *→* _} a =  ∇* a

-- Core of substitution
squash :  Expr* (ExprVtf Φ) ι T →  Expr* Φ ι T
squash (▸ e˂) =  ▸ λ{ .! → squash (e˂ .!) }
squash (∇* e) =  ExprVtf⇒Expr e
squash {T = T *→* _} (λ*˙ e˙) =  λ*˙ $ λ a → squash (e˙ (⇒ExprVtf {T = T} a))
squash (e ◁ e') =  squash e ◁ squash e'
squash (★ e) =  ★ squash e
squash (e ← e') =  squash e ← squash e'
