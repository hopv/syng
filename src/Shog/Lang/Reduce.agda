--------------------------------------------------------------------------------
-- Reduction
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Lang.Reduce (ℓ : Level) where

open import Base.Level using (^_; ↑_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (!)
open import Base.Func using (_$_; id)
open import Base.Prod using (∑-syntax; _×_; _,_)
open import Base.Sum using (_⊎_; inj₀; inj₁)
open import Base.Few using (⊤)
open import Base.Nat using (ℕ)
open import Base.List using (List)
open import Base.List.Nat using (_!!_)
open import Base.Option using (some)
open import Base.Eq using (_≡_)
open import Shog.Lang.Expr ℓ using (Type; ◸_; _➔_; Addr; addr; Expr; Expr˂; ▶_;
  ∇_; λ˙; _◁_; ★_; _←_; Val; Val⇒Expr)

private variable
  A :  Set ℓ
  T U V :  Type

-------------------------------------------------------------------------------
-- Redex

infix 4 ▶ᴿ_
infixl 0 _◁ᴿ_
infix 8 ★ᴿ_
infix 4 _←ᴿ_

data  Redex :  Type →  Set (^ ℓ)  where
  ▶ᴿ_ :  Expr˂ ∞ T →  Redex T
  _◁ᴿ_ :  Val (A ➔ T) →  A →  Redex T
  ★ᴿ_ :  Addr →  Redex T
  _←ᴿ_ :  Addr →  Val T →  Redex (◸ ⊤)

--------------------------------------------------------------------------------
-- Memory

-- Memory cell, containing a value of any type T, parametrized over

MemCell :  Set (^ ℓ)
MemCell =  ∑ T , Val T

-- Memory, consisting of memory blocks, which are a list of memory cells

Mem :  Set (^ ℓ)
Mem =  ℕ →  List MemCell

--------------------------------------------------------------------------------
-- Value & Context-Redex Pair

-- Type for a context-redex pair

Ctxred :  Type →  Set (^ ℓ)
Ctxred T =  ∑ U , (Expr ∞ U → Expr ∞ T) × Redex U

-- Type for either a value or a context-redex pair

Val/Ctxred :  Type →  Set (^ ℓ)
Val/Ctxred T =  Val T ⊎ Ctxred T

-- Calculate the value or context-redex pair of the expression

val/ctxred :  Expr ∞ T →  Val/Ctxred T
val/ctxred (∇ a) =  inj₀ $ ↑ a
val/ctxred (λ˙ e˙) =  inj₀ $ λ˙ e˙
val/ctxred (▶ e) =  inj₁ $ _ , id , ▶ᴿ e
val/ctxred (e ◁ e') =  inj₁ body
 where
  body :  _
  body  with val/ctxred e'
  ... | inj₁ (_ , ctx , red) =  _ , (λ • → e ◁ ctx •) , red
  ... | inj₀ (↑ a)  with val/ctxred e
  ...   | inj₁ (_ , ctx , red) =  _ , (λ • → ctx • ◁ e') , red
  ...   | inj₀ v =  _ , id , (v ◁ᴿ a)
val/ctxred (★ e) =  inj₁ body
 where
  body :  _
  body  with val/ctxred e
  ... | inj₁ (_ , ctx , red) =  _ , (λ • → ★ ctx •) , red
  ... | inj₀ (↑ x) =  _ , id , ★ᴿ x
val/ctxred (e ← e') =  inj₁ body
 where
  body :  _
  body  with  val/ctxred e'
  ... | inj₁ (_ , ctx , red) =  _ , (λ • → e ← ctx •) , red
  ... | inj₀ v  with val/ctxred e
  ...   | inj₁ (_ , ctx , red) =  _ , (λ • → ctx • ← e') , red
  ...   | inj₀ (↑ x) =  _ , id , (x ←ᴿ v)

--------------------------------------------------------------------------------
-- Reduction

-- Red' vc M e M' :  vc & M reduces to e & M',
-- where vc is supposed to be obtained by val/ctxred

private variable
  M :  Mem
  ctx :  Expr ∞ U → Expr ∞ T
  e˂ :  Expr˂ ∞ U
  e˙ :  A → Expr ∞ U
  a :  A
  v : Val U
  b i :  ℕ

data  Red' {T} :  Val/Ctxred T →  Mem →  Expr ∞ T →  Mem →  Set (^ ^ ℓ)  where
  ▶-red :  Red' (inj₁ $ _ , ctx , ▶ᴿ e˂) M (ctx $ e˂ .!) M
  ◁-red :  Red' (inj₁ $ _ , ctx , (λ˙ e˙ ◁ᴿ a)) M (ctx $ e˙ a) M
  ★-red :  M b !! i ≡ some (U , v) →
    Red' (inj₁ $ _ , ctx , ★ᴿ (addr b i)) M (ctx $ Val⇒Expr v) M

-- Red e M e' M' :  e & M reduces to e' & M'

Red :  Expr ∞ T →  Mem →  Expr ∞ T →  Mem →  Set (^ ^ ℓ)
Red e M e' M' =  Red' (val/ctxred e) M e' M'

--------------------------------------------------------------------------------
-- Example

loop :  ∀ {ι : Size} → Expr ι (◸ ⊤)
loop =  ▶ λ{ .! → loop }

check :  Red loop M loop M
check =  ▶-red

open import Base.Eq using (refl⁼)

check2 :  ∀ {e M'} →  Red loop M e M' →  e ≡ loop
check2 ▶-red =  refl⁼
