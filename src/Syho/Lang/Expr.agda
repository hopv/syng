--------------------------------------------------------------------------------
-- Expression
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Lang.Expr where

open import Base.Level using (Level; Up; ↑_)
open import Base.Func using (_$_)
open import Base.Few using (⊤; absurd)
open import Base.Eq using (_≡_; refl; cong)
open import Base.Size using (Size; ∞; Thunk; !)
open import Base.Prod using (∑-syntax; _,_)
open import Base.Dec using (yes; no; ≡Dec; _≡?_; ≡?-refl)
open import Base.Nat using (ℕ; _+_; +-assocʳ)

--------------------------------------------------------------------------------
-- Addr :  Address, pointing at a memory cell

record  Addr :  Set₀  where
  constructor addr
  field
    -- the memory block's id
    bloᵃ :  ℕ
    -- the index in the memory block
    idxᵃ :  ℕ
open Addr public

private variable
  θ :  Addr
  m n :  ℕ

-- ∘ :  Address offset operation

infixl 10 _ₒ_
_ₒ_ :  Addr →  ℕ →  Addr
addr o i ₒ n =  addr o (n + i)

abstract

  -- Associativity of ₒ

  ₒ-assoc :  θ ₒ m ₒ n ≡ θ ₒ (n + m)
  ₒ-assoc {n = n} =  cong (addr _) (+-assocʳ {n})

instance

  Addr-≡Dec :  ≡Dec Addr
  Addr-≡Dec ._≡?_ (addr o i) (addr o' j)  with o ≡? o' | i ≡? j
  ... | yes refl | yes refl =  yes refl
  ... | no o≢o' | _ =  no λ{ refl → absurd $ o≢o' refl }
  ... | _ | no i≢j =  no λ{ refl → absurd $ i≢j refl }
  Addr-≡Dec .≡?-refl {addr o i}  rewrite ≡?-refl {a = o} | ≡?-refl {a = i} =
    refl

--------------------------------------------------------------------------------
-- Type :   Simple type for expressions

infix 8 ◸_
infixr 4 _↷_

data  Type :  Set₁  where
  -- Embedding a pure type
  ◸_ :  Set₀ →  Type
  -- Function
  _↷_ :  Set₀ →  Type →  Type

private variable
  ł :  Level
  ι :  Size
  T U :  Type
  X :  Set₀
  Y :  Set ł

--------------------------------------------------------------------------------
-- Expr :  Expression, possibly infinite

data  Expr (ι : Size) :  Type →  Set₁

-- Expr˂ :  Expr under Thunk

Expr˂ :  Size →  Type →  Set₁
Expr˂ ι T =  Thunk (λ ι → Expr ι T) ι

infix 7 ∇_
infix 6 ▶_ 🞰_ _←_
infixl 5 _◁_
infixr 4 _⁏_

data  Expr ι  where

  -- Later, for infinite construction
  ▶_ :  Expr˂ ι T →  Expr ι T

  -- Turn a value into an expression
  ∇_ :  X →  Expr ι (◸ X)

  -- Non-deterministic value
  nd :  Expr ι (◸ X)

  -- Lambda abstraction over a value
  λ˙ :  (X → Expr ι T) →  Expr ι (X ↷ T)

  -- Application
  _◁_ :  Expr ι (X ↷ T) →  Expr ι (◸ X) →  Expr ι T

  -- Sequential execution
  -- We need this (apart from λ˙ and ◁) to support the case where T is non-pure
  _⁏_ :  Expr ι T →  Expr ι U →  Expr ι U

  -- Read from the memory
  🞰_ :  Expr ι (◸ Addr) →  Expr ι T

  -- Write to the memory
  _←_ :  Expr ι (◸ Addr) →  Expr ι T →  Expr ι (◸ ⊤)

  -- Allocating a new memory block
  alloc :  Expr ι (◸ ℕ) →  Expr ι (◸ Addr)

  -- Freeing a memory block
  free :  Expr ι (◸ Addr) →  Expr ι (◸ ⊤)

-- Lambda abstraction

λ∈-syntax λ-syntax :  (X → Expr ι T) →  Expr ι (X ↷ T)
λ∈-syntax =  λ˙
λ-syntax =  λ˙
infix 3 λ∈-syntax λ-syntax
syntax λ∈-syntax {X = X} (λ x → e) =  λ' x ∈ X , e
syntax λ-syntax (λ x → e) =  λ' x , e

-- Let binding

let˙ let∈-syntax let-syntax :  Expr ι (◸ X) →  (X → Expr ι T) →  Expr ι T
let˙ e₀ e˙ =  λ˙ e˙ ◁ e₀
let∈-syntax =  let˙
let-syntax =  let˙
infix 3 let∈-syntax let-syntax
syntax let∈-syntax {X = X} e₀ (λ x → e) =  let' x ∈ X := e₀ in' e
syntax let-syntax e₀ (λ x → e) =  let' x := e₀ in' e

--------------------------------------------------------------------------------
-- Val :  Value data

infix 8 ṽ_ ṽ↷_
data  Val :  Type →  Set₁  where
  ṽ_ :  X →  Val (◸ X)
  ṽ↷_ :  (X → Expr ∞ T) →  Val (X ↷ T)

-- Function on Val

λᵛ˙ λᵛ-syntax :  (X →  Y) →  Val (◸ X) →  Y
λᵛ˙ f (ṽ x) =  f x
λᵛ-syntax =  λᵛ˙

λᵛ↷˙ λᵛ↷-syntax :  ((X → Expr ∞ T) →  Y) →  Val (X ↷ T) →  Y
λᵛ↷˙ f (ṽ↷ e˙) =  f e˙
λᵛ↷-syntax =  λᵛ↷˙

infix 3 λᵛ-syntax λᵛ↷-syntax
syntax λᵛ-syntax (λ x → y) =  λᵛ x , y
syntax λᵛ↷-syntax (λ e˙ → y) =  λᵛ↷ e˙ , y

-- Conversion from Val to Expr

V⇒E :  Val T →  Expr ∞ T
V⇒E (ṽ x) =  ∇ x
V⇒E (ṽ↷ e˙) =  λ˙ e˙

-- Value of any type T

TyVal :  Set₁
TyVal =  ∑ T , Val T

⊤ṽ :  TyVal
⊤ṽ =  (◸ ⊤ , ṽ _)
