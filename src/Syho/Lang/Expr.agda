--------------------------------------------------------------------------------
-- Expression
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Lang.Expr where

open import Base.Level using (Level; Up; ↑_)
open import Base.Func using (_$_; _∘_; id)
open import Base.Few using (⊤; absurd)
open import Base.Eq using (_≡_; refl; ◠_; cong; subst)
open import Base.Dec using (Dec; yes; no; ≡Dec; _≟_)
open import Base.Size using (Size; ∞; Thunk; !)
open import Base.Bool using (Bool)
open import Base.Prod using (∑-syntax; _×_; _,_)
open import Base.Nat using (ℕ; _+_; +-assocʳ)
open import Base.Sety using (Setʸ; ⸨_⸩ʸ; Syn; setʸ)

--------------------------------------------------------------------------------
-- Addr :  Address, pointing at a memory cell

Addr :  Set₀
Addr =  ℕ × ℕ

private variable
  θ :  Addr
  m n :  ℕ

-- ∘ :  Address offset operation

infixl 10 _ₒ_
_ₒ_ :  Addr →  ℕ →  Addr
(o , i) ₒ n =  (o , n + i)

abstract

  -- Associativity of ₒ

  ₒ-assoc :  θ ₒ m ₒ n ≡ θ ₒ (n + m)
  ₒ-assoc {o , _} {n = n} =  cong (o ,_) (+-assocʳ {n})

--------------------------------------------------------------------------------
-- Type :   Simple type for expressions

infix 8 ◸ʸ_ ◸_
infixr 3 _ʸ↷_ _↷_

data  Type :  Set₀  where
  -- Pure type
  ◸ʸ_ :  Setʸ →  Type
  -- Function type
  _ʸ↷_ :  Setʸ →  Type →  Type

-- Type constructors for Set₀

◸_ :  ∀ X →  {{Syn X}} →  Type
◸ X =  ◸ʸ setʸ {X}

_↷_ :  ∀ X →  {{Syn X}} →  Type →  Type
X ↷ T =  setʸ {X} ʸ↷ T

instance

  -- Equality decision for Type

  Type-≡Dec :  ≡Dec Type
  Type-≡Dec ._≟_ =  _≟'_
   where
    infix 4 _≟'_
    _≟'_ :  ∀ T U →  Dec $ T ≡ U
    ◸ʸ Xʸ ≟' ◸ʸ Yʸ  with Xʸ ≟ Yʸ
    … | yes refl =  yes refl
    … | no X≢Y =  no λ{ refl → X≢Y refl }
    (Xʸ ʸ↷ T) ≟' (Yʸ ʸ↷ U)  with Xʸ ≟ Yʸ | T ≟' U
    … | yes refl | yes refl =  yes refl
    … | no X≢Y | _ =  no λ{ refl → X≢Y refl }
    … | _ | no T≢U =  no λ{ refl → T≢U refl }
    ◸ʸ _ ≟' (_ ʸ↷ _) =  no λ ()
    (_ ʸ↷ _) ≟' ◸ʸ _ =  no λ ()

private variable
  ł :  Level
  ι :  Size
  T U :  Type
  Xʸ :  Setʸ
  Y :  Set ł

--------------------------------------------------------------------------------
-- Expr :  Expression, possibly infinite

data  Expr (ι : Size) :  Type →  Set₀

-- Expr˂ :  Expr under Thunk

Expr˂ :  Size →  Type →  Set₀
Expr˂ ι T =  Thunk (λ ι → Expr ι T) ι

infix 7 ∇_
infix 6 ▶_ 🞰_ _←_
infixl 5 _◁_
infixr 4 _⁏_

data  Expr ι  where

  -- Later, for infinite construction
  ▶_ :  Expr˂ ι T →  Expr ι T

  -- Pure value
  ∇_ :  ⸨ Xʸ ⸩ʸ →  Expr ι (◸ʸ Xʸ)

  -- Non-deterministic value
  nd :  Expr ι (◸ʸ Xʸ)

  -- Lambda abstraction over a value
  λ˙ :  (⸨ Xʸ ⸩ʸ → Expr ι T) →  Expr ι (Xʸ ʸ↷ T)

  -- Application
  _◁_ :  Expr ι (Xʸ ʸ↷ T) →  Expr ι (◸ʸ Xʸ) →  Expr ι T

  -- Sequential execution
  -- We need this (apart from λ˙ and ◁) to support the case where T is non-pure
  _⁏_ :  Expr ι T →  Expr ι U →  Expr ι U

  -- Fork a new thread
  fork :  Expr ι (◸ ⊤) →  Expr ι (◸ ⊤)

  -- Read from the memory
  🞰_ :  Expr ι (◸ Addr) →  Expr ι T

  -- Write to the memory
  _←_ :  Expr ι (◸ Addr) →  Expr ι T →  Expr ι (◸ ⊤)

  -- Fetch and update
  fau :  (⸨ Xʸ ⸩ʸ → ⸨ Xʸ ⸩ʸ) →  Expr ι (◸ Addr) →  Expr ι (◸ʸ Xʸ)

  -- Compare and swap
  cas :  Expr ι (◸ Addr) →  Expr ι (◸ʸ Xʸ) →  Expr ι (◸ʸ Xʸ) →  Expr ι (◸ Bool)

  -- Allocating a new memory block
  alloc :  Expr ι (◸ ℕ) →  Expr ι (◸ Addr)

  -- Freeing a memory block
  free :  Expr ι (◸ Addr) →  Expr ι (◸ ⊤)

-- Lambda abstraction

λ∈-syntax λ-syntax :  (⸨ Xʸ ⸩ʸ → Expr ι T) →  Expr ι (Xʸ ʸ↷ T)
λ∈-syntax =  λ˙
λ-syntax =  λ˙
infix 3 λ∈-syntax λ-syntax
syntax λ∈-syntax {Xʸ = Xʸ} (λ x → e) =  λ' x ∈ Xʸ , e
syntax λ-syntax (λ x → e) =  λ' x , e

-- Let binding

let˙ let∈-syntax let-syntax :
  Expr ι (◸ʸ Xʸ) →  (⸨ Xʸ ⸩ʸ → Expr ι T) →  Expr ι T
let˙ e₀ e˙ =  λ˙ e˙ ◁ e₀
let∈-syntax =  let˙
let-syntax =  let˙
infix 3 let∈-syntax let-syntax
syntax let∈-syntax {Xʸ = Xʸ} e₀ (λ x → e) =  let' x ∈ Xʸ := e₀ in' e
syntax let-syntax e₀ (λ x → e) =  let' x := e₀ in' e

-- ▶ ▶ ▶ …

loop :  Expr ι (◸ ⊤)
loop =  ▶ λ{ .! → loop }

--------------------------------------------------------------------------------
-- Val :  Value data

infix 8 ṽ_ ṽ↷_
data  Val :  Type →  Set₀  where
  ṽ_ :  ⸨ Xʸ ⸩ʸ →  Val (◸ʸ Xʸ)
  ṽ↷_ :  (⸨ Xʸ ⸩ʸ →  Expr ∞ T) →  Val (Xʸ ʸ↷ T)

-- Function on Val

λᵛ˙ λᵛ-syntax :  (⸨ Xʸ ⸩ʸ →  Y) →  Val (◸ʸ Xʸ) →  Y
λᵛ˙ f (ṽ x) =  f x
λᵛ-syntax =  λᵛ˙

λᵛ↷˙ λᵛ↷-syntax :  ((⸨ Xʸ ⸩ʸ → Expr ∞ T) →  Y) →  Val (Xʸ ʸ↷ T) →  Y
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

TyVal :  Set₀
TyVal =  ∑ T , Val T

⊤ṽ :  TyVal
⊤ṽ =  (◸ ⊤ , ṽ _)
