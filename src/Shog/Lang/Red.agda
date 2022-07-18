--------------------------------------------------------------------------------
-- Reduction
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Lang.Red (ℓ : Level) where

open import Base.Level using (○; ^_; Up; ↑_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (!)
open import Base.Func using (_$_)
open import Base.Few using (⊤)
open import Base.Prod using (∑-syntax; _×_; _,_)
open import Base.Sum using (inj₁)
open import Base.Option using (??_; some)
open import Base.Nat using (ℕ)
open import Base.List using (List; [])
open import Base.List.Nat using (_!!_; upd; repeat)
open import Base.Eq using (_≡_; refl; ◠_)
open import Shog.Lang.Expr ℓ using (Type; ◸_; _→*_; Addr; addr; Expr; Expr˂; ▶_;
  ∇_; nd; λ˙; _◁_; ★_; _←_; alloc; free; Val; V⇒E)
open import Shog.Lang.Ktx ℓ using (Redex; ▶ᴿ_; ndᴿ; _◁ᴿ_; ★ᴿ_; _←ᴿ_; allocᴿ;
  freeᴿ; Ktx; _ᴷ◀_; ᴷ∙ᴷ-ᴷ◀; val/ktxred; nonval; val/ktxred-ktx;
  val/ktxred-ktx-inv)

--------------------------------------------------------------------------------
-- Memory

-- Memory cell, containing a value of any type T, parametrized over

MemCell :  Set (^ ℓ)
MemCell =  ∑ T , Val T

-- Re-export
open import Base.Finmap (List MemCell) (_≡ []) public using () renaming (

  -- Memory, consisting of a finite number of memory blocks,
  -- each of which is a list of memory cells
  Finmap to Mem;
  _|ᶠᵐ_ to _|ᴹ_; mapᶠᵐ to bloᴹ; finᶠᵐ to finᴹ;

  -- Memory block update
  updᶠᵐ to updᴹᴮ; updaᶠᵐ to updaᴹᴮ; updaᶠᵐ-eq to updaᴹᴮ-eq)

open import Base.Finmap (List MemCell) (_≡ []) using (initᶠᵐ)

-- Empty memory

empᴹ :  Mem
empᴹ =  initᶠᵐ [] refl

-- Memory read

infix 5 _!!ᴹ_
_!!ᴹ_ :  Mem →  Addr →  ?? MemCell
M !!ᴹ addr b i =  M .bloᴹ b !! i

-- Memory update

updᴹ :  Addr →  MemCell →  Mem →  Mem
updᴹ (addr b i) c M =  updᴹᴮ b (upd i c $ M .bloᴹ b) M

--------------------------------------------------------------------------------
-- Reduction

private variable
  T U V :  Type
  A :  Set ℓ
  M M' :  Mem
  e e' e'' :  Expr ∞ T
  e˂ :  Expr˂ ∞ T
  e˙ :  A → Expr ∞ T
  ktx :  Ktx U T
  red : Redex T
  a :  A
  x :  Addr
  u :  Val U
  b n :  ℕ

infix 4 _⇒ᴿ_ _⇒ᴱ_

-- Reduction on a redex
data  _⇒ᴿ_ :  ∀{T} →  (Redex T × Mem) →  (Expr ∞ T × Mem) →  Set (^ ^ ℓ)  where
  ▶-red :  (▶ᴿ e˂ , M) ⇒ᴿ (e˂ .! , M)
  nd-red :  ∀ (a : A) →  (ndᴿ , M) ⇒ᴿ (∇ a , M)
  ◁-red :  (e˙ ◁ᴿ a , M) ⇒ᴿ (e˙ a , M)
  ★-red :  M !!ᴹ x ≡ some (U , u) →  (★ᴿ x , M) ⇒ᴿ (V⇒E u , M)
  ←-red :  ∀{v : Val V} →  (x ←ᴿ v , M) ⇒ᴿ (∇ _ , updᴹ x (_ , v) M)
  alloc-red :  ∀ b →  M .bloᴹ b ≡ [] →
    (allocᴿ n , M) ⇒ᴿ (∇ ↑ addr b 0 , updᴹᴮ b (repeat n (◸ ⊤ , _)) M)
  free-red :  (freeᴿ (addr b 0) , M) ⇒ᴿ (∇ _ , updᴹᴮ b [] M)

-- Reduction on an expression
data  _⇒ᴱ_ {T} :  (Expr ∞ T × Mem) →  (Expr ∞ T × Mem) →  Set (^ ^ ℓ)  where
  redᴱ :  val/ktxred e ≡ inj₁ (_ , ktx , red) →  (red , M) ⇒ᴿ (e' , M') →
          (e , M) ⇒ᴱ (ktx ᴷ◀ e' , M')

abstract

  -- Enrich a reduction with an evaluation context

  red-ktx :  (e , M) ⇒ᴱ (e' , M') →  (ktx ᴷ◀ e , M) ⇒ᴱ (ktx ᴷ◀ e' , M')
  red-ktx {ktx = ktx} (redᴱ {ktx = ktx'} {e' = e'} eq r⇒)
    rewrite ◠ ᴷ∙ᴷ-ᴷ◀ {ktx = ktx} {ktx'} {e'} =  redᴱ (val/ktxred-ktx eq) r⇒

  -- Unwrap an evaluation context from a reduction

  red-ktx-inv :  nonval e →  (ktx ᴷ◀ e , M) ⇒ᴱ (e'' , M') →
                ∑ e' ,  e'' ≡ ktx ᴷ◀ e'  ×  (e , M) ⇒ᴱ (e' , M')
  red-ktx-inv {ktx = ktx} nv'e (redᴱ eq r⇒)  with val/ktxred-ktx-inv nv'e eq
  ... | _ , refl , eq' =  _ , ᴷ∙ᴷ-ᴷ◀ {ktx = ktx} , redᴱ eq' r⇒
