--------------------------------------------------------------------------------
-- Expression
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Lang.Expr (ℓ : Level) where

open import Base.Level using (^ˡ_; ↑ˡ_)
open import Base.Size using (Size)
open import Base.Thunk using (Thunk)
open import Base.Few using (⊤)
open import Shog.Lang.Type ℓ using (Type; ⌜_⌝ᵀ; _*→*_; _→*_)

private variable
  A :  Set ℓ
  ι :  Size
  T U :  Type
  Φ :  Type → Set ℓ

--------------------------------------------------------------------------------
-- Addr: Address

record  Addr (A : Set ℓ) :  Set ℓ  where

--------------------------------------------------------------------------------
-- Expr*: Expression, possibly infinite, in PHOAS

data  Expr* (Φ : Type → Set ℓ) (ι : Size) :  Type →  Set (^ˡ ℓ)

-- Expr˂*: Expr* under Thunk
Expr˂* :  (Type → Set ℓ) →  Size →  Type →  Set (^ˡ ℓ)
Expr˂* Φ ι T =  Thunk (λ ι → Expr* Φ ι T) ι

-- Expr / Expr˂: Expr* / Expr˂* over a pure type
Expr Expr˂ :  (Type → Set ℓ) →  Size →  Set ℓ →  Set (^ˡ ℓ)
Expr Φ ι A =  Expr* Φ ι ⌜ A ⌝ᵀ
Expr˂ Φ ι A =  Expr˂* Φ ι ⌜ A ⌝ᵀ

infix 8 *ᴱ_
infix 4 _←ᴱ_
infix 4 #ᴱ_
infixr -1 _$ᴱ_

data  Expr* Φ ι  where
  -- Constructor for an infinite experssion
  ⟨_⟩ᴱ :  Expr˂* Φ ι T →  Expr* Φ ι T
  -- Embedding a value
  ⌜_⌝ᴱ :  A →  Expr Φ ι A
  -- Variable
  #ᴱ_ :  Φ T →  Expr* Φ ι T
  -- Lambda abstraction over any value
  λ*˙ :  (Φ T → Expr* Φ ι U) →  Expr* Φ ι (T *→* U)
  -- Lambda abstraction over a pure value
  λ˙ :  (A → Expr* Φ ι T) →  Expr* Φ ι (A →* T)
  -- Application
  _$ᴱ_ :  Expr* Φ ι (T *→* U) →  Expr* Φ ι T →  Expr* Φ ι U
  -- Read from the memory
  *ᴱ_ :  Expr Φ ι (Addr A) →  Expr Φ ι A
  -- Write to the memory
  _←ᴱ_ :  Expr Φ ι (Addr A) →  Expr Φ ι A →  Expr Φ ι ⊤

-- Utility for embedding
pattern ↑⌜_⌝ x =  ⌜ ↑ˡ x ⌝ᴱ

-- Syntax for lambda abstraction
λ*-syntax :  (Φ T → Expr* Φ ι U) →  Expr* Φ ι (T *→* U)
λ*-syntax =  λ*˙
λ-syntax :  (A → Expr* Φ ι T) →  Expr* Φ ι (A →* T)
λ-syntax =  λ˙
syntax λ*-syntax (λ x → e) =  λ* x , e
syntax λ-syntax (λ x → e) =  λᴱ x , e

-- Let binding over any value / a pure value
let*-syntax :  Expr* Φ ι T →  (Φ T → Expr* Φ ι U) →  Expr* Φ ι U
let*-syntax e₀ e˙ =  λ*˙ e˙ $ᴱ e₀
let-syntax :  Expr Φ ι A →  (A → Expr* Φ ι T) →  Expr* Φ ι T
let-syntax e₀ e˙ =  λ˙ e˙ $ᴱ e₀
syntax let*-syntax e₀ (λ x → e) =  let* x := e₀ inᴱ e
syntax let-syntax e₀ (λ x → e) =  letᴱ x := e₀ inᴱ e
