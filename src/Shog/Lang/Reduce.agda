--------------------------------------------------------------------------------
-- Reduction
--------------------------------------------------------------------------------

-- {-# OPTIONS --without-K --sized-types #-}
{-# OPTIONS --sized-types #-}

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
open import Shog.Lang.Type ℓ using (Type; ◸_; _➔_; ValGen; Val)
open import Shog.Lang.Expr ℓ using (Addr; addr; Expr; Expr˂; ▶_; ∇*_; λ*˙; _◁_;
  ★_; _←_; Exprᵛ; Exprᵛ⇒Expr; ⇒Exprᵛ; squash)

private variable
  T U V :  Type
  Φ :  ValGen

-------------------------------------------------------------------------------
-- Redex

infix 4 ▶ᴿ_
infixl 0 _◁ᴿ_
infix 8 ★ᴿ_
infix 4 _←ᴿ_

data  Redex (Φ : ValGen) :  Type →  Set (^ ℓ)  where
  ▶ᴿ_ :  Expr˂ Φ ∞ T →  Redex Φ T
  _◁ᴿ_ :  Val (Exprᵛ Φ) (T ➔ U) →  Val (Exprᵛ Φ) T →  Redex Φ U
  ★ᴿ_ :  Addr →  Redex Φ T
  _←ᴿ_ :  Addr →  Val (Exprᵛ Φ) T →  Redex Φ (◸ ⊤)

--------------------------------------------------------------------------------
-- Memory

-- Memory cell, containing a value of any type T, parametrized over Φ

MemCell :  Set (^ ^ ℓ)
MemCell =  ∑ T , ∀ {Φ} → Val (Exprᵛ Φ) T

-- Memory, consisting of memory blocks, which are a list of memory cells

Mem :  Set (^ ^ ℓ)
Mem =  ℕ →  List MemCell

--------------------------------------------------------------------------------
-- Value & Context-Redex Pair

-- Type for a context-redex pair

Ctxred :  ValGen →  Type →  Set (^ ℓ)
Ctxred Φ T =  ∑ U , (Expr Φ ∞ U → Expr Φ ∞ T) × Redex Φ U

-- Type for either a value or a context-redex pair

Val/Ctxred :  ValGen →  Type →  Set (^ ℓ)
Val/Ctxred Φ T =  Val (Exprᵛ Φ) T ⊎ Ctxred Φ T

-- Calculate the value or context-redex pair of the expression

val/ctxred :  Expr Φ ∞ T →  Val/Ctxred Φ T
val/ctxred {T = T} (∇* a) =  inj₀ $ ⇒Exprᵛ {T = T} a
val/ctxred (λ*˙ e˙) =  inj₀ $ λ*˙ e˙
val/ctxred (▶ e) =  inj₁ $ _ , id , ▶ᴿ e
val/ctxred (e ◁ e') =  inj₁ body
 where
  body :  _
  body  with val/ctxred e'
  ... | inj₁ (_ , ctx , red) =  _ , (λ • → e ◁ ctx •) , red
  ... | inj₀ v'  with val/ctxred e
  ...   | inj₁ (_ , ctx , red) =  _ , (λ • → ctx • ◁ e') , red
  ...   | inj₀ v =  _ , id , (v ◁ᴿ v')
val/ctxred (★ e) =  inj₁ body
 where
  body :  _
  body  with val/ctxred e
  ... | inj₁ (_ , ctx , red) =  _ , (λ • → ★ ctx •) , red
  ... | inj₀ (↑ x) =  _ , id , ★ᴿ x
val/ctxred (_←_ {T = T} e e') =  inj₁ body
 where
  body :  _
  body  with  val/ctxred e'
  ... | inj₁ (_ , ctx , red) =  _ , (λ • → e ← ctx •) , red
  ... | inj₀ v  with val/ctxred e
  ...   | inj₁ (_ , ctx , red) =  _ , (λ • → ctx • ← e') , red
  ...   | inj₀ (↑ x) =  _ , id , (_←ᴿ_ {T = T} x v)

--------------------------------------------------------------------------------
-- Reduction

-- Red' vc M e M' :  vc & M reduces to e & M',
-- where vc is supposed to be obtained by val/ctxred

private variable
  M :  Mem
  ctx :  ∀ {Φ} → Expr Φ ∞ U → Expr Φ ∞ T
  b i :  ℕ

data  Red' {T : Type} :  (∀ {Φ} → Val/Ctxred Φ T) →  Mem →
                        (∀ {Φ} → Expr Φ ∞ T) →  Mem →  Set (^ ^ ℓ)  where
  ▶-red :  ∀ {e˂ :  ∀{Φ} → Expr˂ Φ ∞ U} →
    Red' (inj₁ (_ , ctx , ▶ᴿ e˂)) M (ctx (e˂ .!)) M
  ◁-red : ∀ {e˙ : ∀{Φ} → Val Φ V → Expr Φ ∞ U} {v : ∀{Φ} → Val (Exprᵛ Φ) V} →
    Red' (inj₁ $ _ , ctx , _◁ᴿ_ {T = V} (λ*˙ e˙) v) M (ctx $ squash $ e˙ v) M
  ★-red :  ∀ {v : ∀{Φ} → Val (Exprᵛ Φ) U} →  M b !! i ≡ some (U , v) →
    Red' (inj₁ $ _ , ctx , ★ᴿ (addr b i)) M (ctx $ Exprᵛ⇒Expr {T = U} v) M

-- Red e M e' M' :  e & M reduces to e' & M'

Red :  (∀ {Φ} → Expr Φ ∞ T) →  Mem →  (∀ {Φ} → Expr Φ ∞ T) →  Mem →  Set (^ ^ ℓ)
Red e M e' M' =  Red' (val/ctxred e) M e' M'

--------------------------------------------------------------------------------
-- Example

loop :  ∀ {ι : Size} → Expr Φ ι (◸ ⊤)
loop =  ▶ λ{ .! → loop }

check :  Red loop M loop M
check =  ▶-red

check2 :  ∀{e : ∀{Φ} → Expr Φ ∞ (◸ ⊤)} →  Red loop M e M →  e ≡ loop
check2 ▶-red =  ?
{-
  We get the following error for the pattern ▶-red,
  due to higher-order pattern matching.
  Parametrized HOAS seems a bad idea in this regard.
  > I'm not sure if there should be a case for the constructor ▶-red,
    because I get stuck when trying to solve the following unification
    problems (inferred index ≟ expected index):
      inj₁ (U , ctx , (▶ᴿ e˂)) ≟ val/ctxred loop
      M ≟ M₁
      ctx (e˂ .!) ≟ e
      M ≟ M₁
    when checking that the pattern ▶-red has type Red loop M e M
-}
