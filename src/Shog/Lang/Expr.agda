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
  V! :  Type → Set ℓ

--------------------------------------------------------------------------------
-- Addr: Address

record  Addr (A : Set ℓ) :  Set ℓ  where

--------------------------------------------------------------------------------
-- Expr: Expression, possibly infinite, in PHOAS

data  Expr (V! : Type → Set ℓ) (ι : Size) :  Type →  Set (^ˡ ℓ)

-- Expr˂: Expr under Thunk
Expr˂ :  (Type → Set ℓ) →  Size →  Type →  Set (^ˡ ℓ)
Expr˂ V! ι T =  Thunk (λ ι → Expr V! ι T) ι

-- Expr' / Expr˂': Expr / Expr˂ over Set ℓ
Expr' Expr˂' :  (Type → Set ℓ) →  Size →  Set ℓ →  Set (^ˡ ℓ)
Expr' V! ι A =  Expr V! ι ⌜ A ⌝ᵀ
Expr˂' V! ι A =  Expr˂ V! ι ⌜ A ⌝ᵀ

infix 8 *ᴱ_
infix 4 _←ᴱ_
infix 4 #ᴱ_
infixr -1 _$ᴱ_

data  Expr V! ι  where
  -- Constructor for an infinite experssion
  ⟨_⟩ᴱ :  Expr˂ V! ι T →  Expr V! ι T
  -- Embedding a value
  ⌜_⌝ᴱ :  A →  Expr' V! ι A
  -- Read from the memory
  *ᴱ_ :  Expr' V! ι (Addr A) →  Expr' V! ι A
  -- Write to the memory
  _←ᴱ_ :  Expr' V! ι (Addr A) →  Expr' V! ι A →  Expr' V! ι ⊤
  -- Variable
  #ᴱ_ :  V! T →  Expr V! ι T
  -- Lambda abstraction
  λ˙ᴱ :  (V! T → Expr V! ι U) →  Expr V! ι (T ⇒ U)
  -- Application
  _$ᴱ_ :  Expr V! ι (T ⇒ U) →  Expr V! ι T →  Expr V! ι U

-- Syntax for lambda abstraction
λᴱ-syntax :  (V! T → Expr V! ι U) →  Expr V! ι (T ⇒ U)
λᴱ-syntax =  λ˙ᴱ
syntax λᴱ-syntax (λ x → e) =  λᴱ x , e
