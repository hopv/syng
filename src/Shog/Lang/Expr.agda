--------------------------------------------------------------------------------
-- Expression
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Lang.Expr (ℓ : Level) where

open import Base.Level using (^ˡ_; 0ˡ)
open import Base.Size using (Size)
open import Base.Thunk using (Thunk)
open import Base.Few using (⊤)
open import Shog.Lang.Type ℓ using (Type; ⌜_⌝ᵀ; _⇒_)

private variable
  A :  Set ℓ
  ι :  Size
  T U :  Type
  Φ :  Type → Set ℓ

--------------------------------------------------------------------------------
-- Addr: Address

record  Addr (A : Set ℓ) :  Set ℓ  where

--------------------------------------------------------------------------------
-- Expr: Expression, possibly infinite, in PHOAS

data  Expr (Φ : Type → Set ℓ) (ι : Size) :  Type →  Set (^ˡ ℓ)

-- Expr˂: Expr under Thunk
Expr˂ :  (Type → Set ℓ) →  Size →  Type →  Set (^ˡ ℓ)
Expr˂ Φ ι T =  Thunk (λ ι → Expr Φ ι T) ι

-- Expr' / Expr˂': Expr / Expr˂ over a pure type
Expr' Expr˂' :  (Type → Set ℓ) →  Size →  Set ℓ →  Set (^ˡ ℓ)
Expr' Φ ι A =  Expr Φ ι ⌜ A ⌝ᵀ
Expr˂' Φ ι A =  Expr˂ Φ ι ⌜ A ⌝ᵀ

infix 8 *ᴱ_
infix 4 _←ᴱ_
infix 4 #ᴱ_
infixr -1 _$ᴱ_

data  Expr Φ ι  where
  -- Constructor for an infinite experssion
  ⟨_⟩ᴱ :  Expr˂ Φ ι T →  Expr Φ ι T
  -- Embedding a value
  ⌜_⌝ᴱ :  A →  Expr' Φ ι A
  -- Variable
  #ᴱ_ :  Φ T →  Expr Φ ι T
  -- Lambda abstraction over any value
  λ*˙ᴱ :  (Φ T → Expr Φ ι U) →  Expr Φ ι (T ⇒ U)
  -- Lambda abstraction over a pure value
  λ˙ᴱ :  (A → Expr Φ ι T) →  Expr Φ ι (⌜ A ⌝ᵀ ⇒ T)
  -- Application
  _$ᴱ_ :  Expr Φ ι (T ⇒ U) →  Expr Φ ι T →  Expr Φ ι U
  -- Read from the memory
  *ᴱ_ :  Expr' Φ ι (Addr A) →  Expr' Φ ι A
  -- Write to the memory
  _←ᴱ_ :  Expr' Φ ι (Addr A) →  Expr' Φ ι A →  Expr' Φ ι ⊤

-- Syntax for lambda abstraction
λ*ᴱ-syntax :  (Φ T → Expr Φ ι U) →  Expr Φ ι (T ⇒ U)
λ*ᴱ-syntax =  λ*˙ᴱ
λᴱ-syntax :  (A → Expr Φ ι T) →  Expr Φ ι (⌜ A ⌝ᵀ ⇒ T)
λᴱ-syntax =  λ˙ᴱ
syntax λ*ᴱ-syntax (λ x → e) =  λ*ᴱ x , e
syntax λᴱ-syntax (λ x → e) =  λᴱ x , e
