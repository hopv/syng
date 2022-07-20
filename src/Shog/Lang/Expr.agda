--------------------------------------------------------------------------------
-- Expression
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Lang.Expr (ℓ : Level) where

open import Base.Level using (○; ^_; Up; ↑_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk; !)
open import Base.Func using (_$_)
open import Base.Few using (⊤)
open import Base.Nat using (ℕ; _+_; +-assocʳ)
open import Base.Eq using (_≡_; cong)

--------------------------------------------------------------------------------
-- Addr: Address, pointing at a memory cell

record  Addr :  Set ○  where
  constructor addr
  field
    -- the memory block's id
    blᵃ :  ℕ
    -- the index in the memory block
    idxᵃ :  ℕ
open Addr public

private variable
  ρ :  Addr
  m n :  ℕ

-- ₒ: Address offset operation

infixl 6 _ₒ_
_ₒ_ :  Addr →  ℕ →  Addr
addr l i ₒ n =  addr l (n + i)

abstract

  -- Associativity of ₒ

  ₒ-assoc :  ρ ₒ m ₒ n ≡ ρ ₒ (n + m)
  ₒ-assoc {n = n} =  cong (addr _) (+-assocʳ {n})

--------------------------------------------------------------------------------
-- Type:  Simple type for expressions

infix 8 ◸_
infixr 4 _→*_

data  Type :  Set (^ ℓ)  where
  -- Embedding a pure type
  ◸_ :  Set ℓ →  Type
  -- Function
  _→*_ :  Set ℓ →  Type →  Type

private variable
  A :  Set ℓ
  ι :  Size
  T U :  Type

--------------------------------------------------------------------------------
-- Expr: Expression, possibly infinite

data  Expr (ι : Size) :  Type →  Set (^ ℓ)

-- Expr˂: Expr under Thunk

Expr˂ :  Size →  Type →  Set (^ ℓ)
Expr˂ ι T =  Thunk (λ ι → Expr ι T) ι

infix 7 ∇_
infix 6 ▶_ ★_ _←_
infixl 5 _◁_

data  Expr ι  where
  -- Later, for infinite construction
  ▶_ :  Expr˂ ι T →  Expr ι T
  -- Turn a value into an expression
  ∇_ :  A →  Expr ι (◸ A)
  -- Non-deterministic value
  nd :  Expr ι (◸ A)
  -- Lambda abstraction over a value
  λ˙ :  (A → Expr ι T) →  Expr ι (A →* T)
  -- Application
  _◁_ :  Expr ι (A →* T) →  Expr ι (◸ A) →  Expr ι T
  -- Read from the memory
  ★_ :  Expr ι (◸ Up Addr) →  Expr ι T
  -- Write to the memory
  _←_ :  Expr ι (◸ Up Addr) →  Expr ι T →  Expr ι (◸ ⊤)
  -- Allocating a new memory block
  alloc :  Expr ι (◸ Up ℕ) →  Expr ι (◸ Up Addr)
  -- Freeing a memory block
  free :  Expr ι (◸ Up Addr) →  Expr ι (◸ ⊤)

-- Lambda abstraction

λ∈-syntax λ-syntax :  (A → Expr ι T) →  Expr ι (A →* T)
λ∈-syntax =  λ˙
λ-syntax =  λ˙
infix 3 λ∈-syntax λ-syntax
syntax λ∈-syntax {A = A} (λ ρ → e) =  λ' ρ ∈ A , e
syntax λ-syntax (λ ρ → e) =  λ' ρ , e

-- Let binding

let˙ let∈-syntax let-syntax :  Expr ι (◸ A) →  (A → Expr ι T) →  Expr ι T
let˙ e₀ e˙ =  λ˙ e˙ ◁ e₀
let∈-syntax =  let˙
let-syntax =  let˙
infix 3 let∈-syntax let-syntax
syntax let∈-syntax {A = A} e₀ (λ ρ → e) =  let' ρ ∈ A := e₀ in' e
syntax let-syntax e₀ (λ ρ → e) =  let' ρ := e₀ in' e

--------------------------------------------------------------------------------
-- Val: Value type

Val :  Type →  Set (^ ℓ)
Val (◸ A) =  Up A
Val (A →* T) =  A → Expr ∞ T

-- Conversion from Val to Expr

V⇒E :  Val T →  Expr ∞ T
V⇒E {T = ◸ _} (↑ a) =  ∇ a
V⇒E {T = _ →* _} e˙ =  λ˙ e˙
