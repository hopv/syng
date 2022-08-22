--------------------------------------------------------------------------------
-- Reduction
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Lang.Reduce where

open import Base.Level using (↑_)
open import Base.Size using (∞)
open import Base.Thunk using (!)
open import Base.Func using (_$_)
open import Base.Few using (⊤)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_)
open import Base.Sum using (inj₁)
open import Base.Option using (??_; some)
open import Base.Nat using (ℕ)
open import Base.List using (List; [])
open import Base.List.Nat using (_‼_; upd; rep)
open import Base.Eq using (_≡_; refl; ◠_)
open import Syho.Lang.Expr using (Type; ◸_; Addr; addr; Expr; Expr˂; ∇_; Val;
  V⇒E; AnyVal; ⊤-val)
open import Syho.Lang.Ktxred using (Redex; ▶ᴿ_; ndᴿ; _◁ᴿ_; 🞰ᴿ_; _←ᴿ_; allocᴿ;
  freeᴿ; Ktx; _ᴷ◁_; ᴷ∘ᴷ-ᴷ◁; _ᴷ|ᴿ_; val/ktxred; nonval; val/ktxred-ktx;
  val/ktxred-ktx-inv)

--------------------------------------------------------------------------------
-- Memory

-- Re-export
open import Base.Finmap (List AnyVal) (_≡ []) public using () renaming (

  -- Memory, consisting of a finite number of memory blocks,
  -- each of which is a list of memory cells
  Finmap to Mem;
  _|ᶠᵐ_ to _|ᴹ_; !ᶠᵐ to bloᴹ; finᶠᵐ to finᴹ;

  -- Memory block update
  updᶠᵐ to updᴹᴮ)

open import Base.Finmap (List AnyVal) (_≡ []) using (initᶠᵐ)

-- Empty memory

empᴹ :  Mem
empᴹ =  initᶠᵐ [] refl

-- Memory read

infix 5 _‼ᴹ_
_‼ᴹ_ :  Mem →  Addr →  ?? AnyVal
M ‼ᴹ addr l i =  M .bloᴹ l ‼ i

-- Memory update

updᴹ :  Addr →  AnyVal →  Mem →  Mem
updᴹ (addr l i) av M =  updᴹᴮ l (upd i av $ M .bloᴹ l) M

--------------------------------------------------------------------------------
-- Reduction

private variable
  T U V :  Type
  X :  Set₀
  M M' :  Mem
  e e' e'' :  Expr ∞ T
  e˂ :  Expr˂ ∞ T
  e˙ :  X → Expr ∞ T
  ktx :  Ktx U T
  red : Redex T
  x :  X
  θ :  Addr
  v :  Val V
  l n :  ℕ

infix 4 _⇒ᴿ_ _⇒ᴱ_

-- Reduction on a redex
data  _⇒ᴿ_ :  ∀{T} →  (Redex T × Mem) →  (Expr ∞ T × Mem) →  Set₁  where
  ▶-red :  (▶ᴿ e˂ , M) ⇒ᴿ (e˂ .! , M)
  nd-red :  ∀(x : X) →  (ndᴿ , M) ⇒ᴿ (∇ x , M)
  ◁-red :  (e˙ ◁ᴿ x , M) ⇒ᴿ (e˙ x , M)
  🞰-red :  M ‼ᴹ θ ≡ some (V , v) →  (🞰ᴿ θ , M) ⇒ᴿ (V⇒E v , M)
  ←-red :  (θ ←ᴿ v , M) ⇒ᴿ (∇ _ , updᴹ θ (V , v) M)
  alloc-red :  ∀ l →  M .bloᴹ l ≡ [] →
    (allocᴿ n , M) ⇒ᴿ (∇ addr l 0 , updᴹᴮ l (rep n ⊤-val) M)
  free-red :  (freeᴿ (addr l 0) , M) ⇒ᴿ (∇ _ , updᴹᴮ l [] M)

-- Reduction on an expression
data  _⇒ᴱ_ {T} :  (Expr ∞ T × Mem) →  (Expr ∞ T × Mem) →  Set₁  where
  redᴱ :  val/ktxred e ≡ inj₁ (ktx ᴷ|ᴿ red) →  (red , M) ⇒ᴿ (e' , M') →
          (e , M) ⇒ᴱ (ktx ᴷ◁ e' , M')

abstract

  -- Enrich a reduction with an evaluation context

  red-ktx :  (e , M) ⇒ᴱ (e' , M') →  (ktx ᴷ◁ e , M) ⇒ᴱ (ktx ᴷ◁ e' , M')
  red-ktx {ktx = ktx} (redᴱ {ktx = ktx'} {e' = e'} eq r⇒)
    rewrite ◠ ᴷ∘ᴷ-ᴷ◁ {ktx = ktx} {ktx' = ktx'} {e'}
    =  redᴱ (val/ktxred-ktx eq) r⇒

  -- Unwrap an evaluation context from a reduction

  red-ktx-inv :  nonval e →  (ktx ᴷ◁ e , M) ⇒ᴱ (e'' , M') →
                 ∑ e' ,  e'' ≡ ktx ᴷ◁ e'  ×  (e , M) ⇒ᴱ (e' , M')
  red-ktx-inv {ktx = ktx} nv'e (redᴱ eq r⇒)  with val/ktxred-ktx-inv nv'e eq
  ... | -, refl , eq' =  -, ᴷ∘ᴷ-ᴷ◁ {ktx = ktx} , redᴱ eq' r⇒
