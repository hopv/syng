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
open import Base.Nat using (ℕ; _+_; +-assocʳ)
open import Base.Eq using (_≡_; cong)
open import Shog.Lang.Type ℓ using (Type; ◸_; _➔_; ValGen; Val*; Val)

private variable
  A :  Set ℓ
  ι :  Size
  T U :  Type
  Φ :  ValGen

--------------------------------------------------------------------------------
-- Addr: Address, pointing at a memory cell

record  Addr :  Set ℓ  where
  constructor addr
  field
    -- the memory block's id
    blᵃ :  ℕ
    -- the index in the memory block
    idxᵃ :  ℕ
open Addr public

private variable
  xᵃ :  Addr
  m n :  ℕ

-- ₒ: Address offset operation

infixl 6 _ₒ_
_ₒ_ :  Addr →  ℕ →  Addr
addr b i ₒ n =  addr b (n + i)

abstract

  -- Associativity of ₒ

  ₒ-assoc :  xᵃ ₒ m ₒ n ≡ xᵃ ₒ (n + m)
  ₒ-assoc {n = n} =  cong (addr _) (+-assocʳ {n})

--------------------------------------------------------------------------------
-- Expr: Expression, possibly infinite, in PHOAS

data  Expr (Φ : ValGen) (ι : Size) :  Type →  Set (^ ℓ)

-- Expr˂: Expr under Thunk

Expr˂ :  ValGen →  Size →  Type →  Set (^ ℓ)
Expr˂ Φ ι T =  Thunk (λ ι → Expr Φ ι T) ι

infix 4 ▶_ ∇*_ ∇_
infixl 0 _◁_
infix 8 ★_
infix 4 _←_

data  Expr Φ ι  where
  -- Later, for infinite construction
  ▶_ :  Expr˂ Φ ι T →  Expr Φ ι T
  -- Turn a value into an expression
  ∇*_ :  Val Φ T →  Expr Φ ι T
  -- Lambda abstraction over a value
  λ*˙ :  (Val Φ T → Expr Φ ι U) →  Expr Φ ι (T ➔ U)
  -- Application
  _◁_ :  Expr Φ ι (T ➔ U) →  Expr Φ ι T →  Expr Φ ι U
  -- Read from the memory
  ★_ :  Expr Φ ι (◸ Addr) →  Expr Φ ι T
  -- Write to the memory
  _←_ :  Expr Φ ι (◸ Addr) →  Expr Φ ι T →  Expr Φ ι (◸ ⊤)

-- ∇* for a pure value

∇_ :  A →  Expr Φ ι (◸ A)
∇ a =  ∇* ↑ a

-- λ*˙ for a pure value

λ˙ :  (A → Expr Φ ι T) →  Expr Φ ι (◸ A ➔ T)
λ˙ e˙ =  λ*˙ $ λ (↑ a) → e˙ a

-- Syntax for lambda abstraction, for a general / pure value

λ*-syntax :  (Val Φ T → Expr Φ ι U) →  Expr Φ ι (T ➔ U)
λ*-syntax =  λ*˙
λ-syntax :  (A → Expr Φ ι T) →  Expr Φ ι (◸ A ➔ T)
λ-syntax =  λ˙
infix 3 λ*-syntax λ-syntax
syntax λ*-syntax (λ x → e) =  λ* x , e
syntax λ-syntax (λ x → e) =  λ' x , e

-- Let binding for a general / pure value

let*-syntax :  Expr Φ ι T →  (Val Φ T → Expr Φ ι U) →  Expr Φ ι U
let*-syntax e₀ e˙ =  λ*˙ e˙ ◁ e₀
let-syntax :  Expr Φ ι (◸ A) →  (A → Expr Φ ι T) →  Expr Φ ι T
let-syntax e₀ e˙ =  λ˙ e˙ ◁ e₀
infix 3 let*-syntax let-syntax
syntax let*-syntax e₀ (λ x → e) =  let* x := e₀ in' e
syntax let-syntax e₀ (λ x → e) =  let' x := e₀ in' e

--------------------------------------------------------------------------------
-- For β-reduction

-- Exprᵛ Φ: ValGen that maps non-pure T to Expr Φ ∞ T

Exprᵛ :  ValGen →  ValGen
Exprᵛ Φ .Val* T =  Expr Φ ∞ T

-- Conversion from Val (Exprᵛ Φ) to Expr Φ ∞

Exprᵛ⇒Expr :  Val (Exprᵛ Φ) T →  Expr Φ ∞ T
Exprᵛ⇒Expr {T = ◸ _} a =  ∇* a
Exprᵛ⇒Expr {T = _ ➔ _} e =  e

-- Conversion from Val Φ to Val (Exprᵛ Φ)

⇒Exprᵛ :  Val Φ T →  Val (Exprᵛ Φ) T
⇒Exprᵛ {T = ◸ _} a =  a
⇒Exprᵛ {T = _ ➔ _} a =  ∇* a

-- Conversion from Expr (Exprᵛ Φ) to Expr Φ,
-- which is the core of β-reduction

squash :  Expr (Exprᵛ Φ) ι T →  Expr Φ ι T
squash (▶ e˂) =  ▶ λ{ .! → squash (e˂ .!) }
squash (∇* e) =  Exprᵛ⇒Expr e
squash {T = T ➔ _} (λ*˙ e˙) =  λ*˙ $ λ a → squash (e˙ (⇒Exprᵛ {T = T} a))
squash (e ◁ e') =  squash e ◁ squash e'
squash (★ e) =  ★ squash e
squash (e ← e') =  squash e ← squash e'
