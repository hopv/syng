--------------------------------------------------------------------------------
-- Expression
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Lang.Expr where

open import Base.Level using (Level; Up; ↑_)
open import Base.Func using (_$_; _∘_; id)
open import Base.Few using (⊤; 0⊤; absurd)
open import Base.Eq using (_≡_; refl; ◠_; cong; subst)
open import Base.Dec using (Dec; yes; no; ≡Dec; _≟_; upd˙)
open import Base.Size using (𝕊; ∞; Thunk; !)
open import Base.Bool using (𝔹)
open import Base.Prod using (∑-syntax; _×_; _,_; _,-)
open import Base.Option using (¿_; ň; _$¿_; _»-¿_)
open import Base.Nat using (ℕ; _+_; +-assocʳ; Cofin; ∀⇒Cofin; Cofin-upd˙;
  Cofin-∑)
open import Base.List using (List; _‼_; upd)
open import Base.Sety using (Setʸ; ⸨_⸩ʸ; Syn; setʸ)

--------------------------------------------------------------------------------
-- Addr :  Address, pointing at a memory cell

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
  ●_ :  Expr˂ ι T →  Expr ι T

  -- Fork a new thread
  fork :  Expr˂ ι (◸ ⊤) →  Expr ι (◸ ⊤)

  -- Read from the memory
  🞰_ :  Expr ι (◸ Addr) →  Expr ι T

  -- Write to the memory
  _←_ :  Expr ι (◸ Addr) →  Expr ι T →  Expr ι (◸ ⊤)

  -- Fetch and update
  fau :  (⸨ Xʸ ⸩ʸ → ⸨ Xʸ ⸩ʸ) →  Expr ι (◸ Addr) →  Expr ι (◸ʸ Xʸ)

  -- Compare and swap
  cas :  Expr ι (◸ Addr) →  Expr ι (◸ʸ Xʸ) →  Expr ι (◸ʸ Xʸ) →  Expr ι (◸ 𝔹)

  -- Allocating a new memory block
  alloc :  Expr ι (◸ ℕ) →  Expr ι (◸ Addr)

  -- Freeing a memory block
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
-- Memory

-- Mblo :  Memory block state
-- Mem :  Memory state

Mblo Mem :  Set₀
Mblo =  ¿ List TyVal
Mem =  ℕ →  Mblo

private variable
  M M' M'' :  Mem
  Mb :  Mblo
  ᵗv :  TyVal

-- Memory read

infix 5 _‼ᴹ_
_‼ᴹ_ :  Mem →  Addr →  ¿ TyVal
M ‼ᴹ (o , i) =  M o »-¿ _‼ i

-- Empty memory

empᴹ :  Mem
empᴹ _ =  ň

-- Memory update

updᴹ :  Addr →  TyVal →  Mem →  Mem
updᴹ (o , i) ᵗv M =  upd˙ o (upd i ᵗv $¿ M o) M

-- Memory validity, saying that the domain of the memory is a finite set

infix 3 ✓ᴹ_
✓ᴹ_ :  Mem →  Set₀
✓ᴹ M =  Cofin (λ _ → _≡ ň) M

abstract

  -- ✓ᴹ holds for empᴹ

  ✓ᴹ-emp :  ✓ᴹ empᴹ
  ✓ᴹ-emp =  ∀⇒Cofin {F = λ _ → _≡ ň} λ _ → refl

  -- ✓ᴹ is preserved by upd˙ and updᴹ

  ✓ᴹ-upd˙ :  ✓ᴹ M →  ✓ᴹ (upd˙ o Mb M)
  ✓ᴹ-upd˙ =  Cofin-upd˙ {F = λ _ → _≡ ň}

  -- If ✓ᴹ M holds, then M o ≡ ň for some o

  ✓ᴹ-∑ň :  ✓ᴹ M →  ∑ o , M o ≡ ň
  ✓ᴹ-∑ň =  Cofin-∑ {F = λ _ → _≡ ň}
