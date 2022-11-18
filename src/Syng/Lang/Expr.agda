--------------------------------------------------------------------------------
-- Expression
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syng.Lang.Expr where

open import Base.Level using (Level; Up; ↑_)
open import Base.Func using (_$_; _∘_; id)
open import Base.Few using (⊤; 0⊤; absurd)
open import Base.Eq using (_≡_; refl; ◠_; cong; subst)
open import Base.Dec using (Dec; yes; no; ≡Dec; _≟_; upd˙)
open import Base.Size using (𝕊; ∞; Thunk; !)
open import Base.Bool using (𝔹)
open import Base.Prod using (∑-syntax; _×_; _,_; _,-)
open import Base.Option using (¿_; ň; _$¿_; _»-¿_)
open import Base.Nat using (ℕ; _+_; +-assocˡ; Cofin; ∀⇒Cofin; Cofin-upd˙;
  Cofin-∑)
open import Base.List using (List; _‼_; upd)
open import Base.Sety using (Setʸ; ⸨_⸩ʸ; Syn; setʸ)

--------------------------------------------------------------------------------
-- Addr :  Address, pointing at a heap cell

Addr :  Set₀
Addr =  ℕ × ℕ

private variable
  θ :  Addr
  m n o :  ℕ

-- ∘ :  Address offset operation

infixl 10 _ₒ_
_ₒ_ :  Addr →  ℕ →  Addr
(o , i) ₒ n =  (o , n + i)

abstract

  -- Associativity of ₒ

  ₒ-assoc :  θ ₒ m ₒ n ≡ θ ₒ (n + m)
  ₒ-assoc {o , _} {n = n} =  cong (o ,_) (+-assocˡ {n})

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
  ι :  𝕊
  T U :  Type
  Xʸ :  Setʸ
  Y :  Set ł

--------------------------------------------------------------------------------
-- Expr :  Expression, possibly infinite

data  Expr (ι : 𝕊) :  Type →  Set₀

-- Expr˂ :  Expr under Thunk

Expr˂ :  𝕊 →  Type →  Set₀
Expr˂ ι T =  Thunk (λ ι → Expr ι T) ι

infix 8 ∇_
infixl 7 _◁_
infix 6 🞰_ _←_
infixr 3 _⁏_ _⁏¡_

data  Expr ι  where

  -- Pure value
  ∇_ :  ⸨ Xʸ ⸩ʸ →  Expr ι (◸ʸ Xʸ)

  -- Lambda abstraction over a value
  λ˙ :  (⸨ Xʸ ⸩ʸ → Expr˂ ι T) →  Expr ι (Xʸ ʸ↷ T)

  -- Non-deterministic value
  nd :  Expr ι (◸ʸ Xʸ)

  -- Application
  _◁_ :  Expr ι (Xʸ ʸ↷ T) →  Expr ι (◸ʸ Xʸ) →  Expr ι T

  -- Sequential execution
  -- We need this (apart from λ˙ and ◁) to support the case where T is non-pure
  _⁏_ :  Expr ι T →  Expr˂ ι U →  Expr ι U

  -- Observable event
  ev :  Expr˂ ι T →  Expr ι T

  -- Fork a new thread
  fork :  Expr˂ ι (◸ ⊤) →  Expr ι (◸ ⊤)

  -- Read from the heap
  🞰_ :  Expr ι (◸ Addr) →  Expr ι T

  -- Write to the heap
  _←_ :  Expr ι (◸ Addr) →  Expr ι T →  Expr ι (◸ ⊤)

  -- Fetch and update
  fau :  (⸨ Xʸ ⸩ʸ → ⸨ Xʸ ⸩ʸ) →  Expr ι (◸ Addr) →  Expr ι (◸ʸ Xʸ)

  -- Compare and swap
  cas :  Expr ι (◸ Addr) →  Expr ι (◸ʸ Xʸ) →  Expr ι (◸ʸ Xʸ) →  Expr ι (◸ 𝔹)

  -- Allocating a new heap block
  alloc :  Expr ι (◸ ℕ) →  Expr ι (◸ Addr)

  -- Freeing a heap block
  free :  Expr ι (◸ Addr) →  Expr ι (◸ ⊤)

-- Sequential execution

_⁏¡_ :  Expr ι T →  Expr ι U →  Expr ι U
e ⁏¡ e' =  e ⁏ λ{ .! → e' }

-- Lambda abstraction

λ∈-syntax λ-syntax :  (⸨ Xʸ ⸩ʸ → Expr˂ ι T) →  Expr ι (Xʸ ʸ↷ T)
λ∈-syntax =  λ˙
λ-syntax =  λ˙
λ∈¡-syntax λ¡-syntax :  (⸨ Xʸ ⸩ʸ → Expr ι T) →  Expr ι (Xʸ ʸ↷ T)
λ∈¡-syntax e˙ =  λ∈-syntax λ{ x .! → e˙ x }
λ¡-syntax =  λ∈¡-syntax
infix 3 λ∈-syntax λ-syntax λ∈¡-syntax λ¡-syntax
syntax λ∈-syntax {Xʸ = Xʸ} (λ x → e˂) =  λ' x ∈ Xʸ , e˂
syntax λ-syntax (λ x → e˂) =  λ' x , e˂
syntax λ∈¡-syntax {Xʸ = Xʸ} (λ x → e) =  λ' x ∈ Xʸ ,¡ e
syntax λ¡-syntax (λ x → e) =  λ' x ,¡ e

-- Let binding

let˙ let∈-syntax let-syntax :
  Expr ι (◸ʸ Xʸ) →  (⸨ Xʸ ⸩ʸ → Expr˂ ι T) →  Expr ι T
let˙ e₀ e˂˙ =  λ˙ e˂˙ ◁ e₀
let∈-syntax =  let˙
let-syntax =  let˙
let∈¡-syntax let¡-syntax :  Expr ι (◸ʸ Xʸ) →  (⸨ Xʸ ⸩ʸ → Expr ι T) →  Expr ι T
let∈¡-syntax e₀ e˙ =  let˙ e₀ λ{ x .! → e˙ x }
let¡-syntax =  let∈¡-syntax
infix 3 let∈-syntax let-syntax let∈¡-syntax let¡-syntax
syntax let∈-syntax {Xʸ = Xʸ} e₀ (λ x → e˂) =  let' x ∈ Xʸ := e₀ in' e˂
syntax let-syntax e₀ (λ x → e˂) =  let' x := e₀ in' e˂
syntax let∈¡-syntax {Xʸ = Xʸ} e₀ (λ x → e) =  let' x ∈ Xʸ := e₀ in¡ e
syntax let¡-syntax e₀ (λ x → e) =  let' x := e₀ in¡ e

-- No-op

infix 8 ▶_
▶_ :  Expr˂ ι T →  Expr ι T
▶ e˂ =  ∇ 0⊤ ⁏ e˂

-- Infinite loop

loop :  Expr ι T
loop =  ▶ λ{ .! → loop }

-- Fork

fork¡ :  Expr ι (◸ ⊤) →  Expr ι (◸ ⊤)
fork¡ e =  fork λ{ .! → e }

-- Utility

Expr∞ Expr˂∞ :  Type →  Set₀
Expr∞ T =  Expr ∞ T
Expr˂∞ T =  Expr˂ ∞ T

--------------------------------------------------------------------------------
-- Val :  Value data

Val :  Type →  Set₀
Val (◸ʸ Xʸ) =  ⸨ Xʸ ⸩ʸ
Val (Xʸ ʸ↷ T) =  ⸨ Xʸ ⸩ʸ →  Expr˂∞ T

-- Conversion from Val to Expr

V⇒E :  Val T →  Expr∞ T
V⇒E {◸ʸ _} =  ∇_
V⇒E {_ ʸ↷ _} =  λ˙

-- Value of any type T

TyVal :  Set₀
TyVal =  ∑ T , Val T

⊤- :  TyVal
⊤- =  ◸ ⊤ ,-

--------------------------------------------------------------------------------
-- Heap

-- Hblo :  Heap block

Hblo :  Set₀
Hblo =  ¿ List TyVal

-- Heap :  Heap

Heap :  Set₀
Heap =  ℕ →  Hblo

private variable
  H H' H'' :  Heap
  Hb :  Hblo
  ᵗv :  TyVal

-- Heap read

infix 5 _‼ᴴ_
_‼ᴴ_ :  Heap →  Addr →  ¿ TyVal
H ‼ᴴ (o , i) =  H o »-¿ _‼ i

-- Empty heap

∅ᴴ :  Heap
∅ᴴ _ =  ň

-- Heap update

updᴴ :  Addr →  TyVal →  Heap →  Heap
updᴴ (o , i) ᵗv H =  upd˙ o (upd i ᵗv $¿ H o) H

-- Heap validity, saying that the domain of the heap is a finite set

infix 3 ✓ᴴ_
✓ᴴ_ :  Heap →  Set₀
✓ᴴ H =  Cofin (λ _ → _≡ ň) H

abstract

  -- ✓ᴴ holds for ∅ᴴ

  ✓ᴴ-∅ :  ✓ᴴ ∅ᴴ
  ✓ᴴ-∅ =  ∀⇒Cofin {F = λ _ → _≡ ň} λ _ → refl

  -- ✓ᴴ is preserved by upd˙ and updᴴ

  ✓ᴴ-upd˙ :  ✓ᴴ H →  ✓ᴴ (upd˙ o Hb H)
  ✓ᴴ-upd˙ =  Cofin-upd˙ {F = λ _ → _≡ ň}

  -- If ✓ᴴ H holds, then H o ≡ ň for some o

  ✓ᴴ-∑ň :  ✓ᴴ H →  ∑ o , H o ≡ ň
  ✓ᴴ-∑ň =  Cofin-∑ {F = λ _ → _≡ ň}
