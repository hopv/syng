--------------------------------------------------------------------------------
-- Reduction
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Lang.Reduce (ℓ : Level) where

open import Base.Level using (○; ^_; Up; ↑_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (!)
open import Base.Func using (_$_; id; _∘_)
open import Base.Few using (⊤; ⊥)
open import Base.Prod using (∑-syntax; ∑∈-syntax; _×_; _,_)
open import Base.Sum using (_⊎_; inj₀; inj₁)
open import Base.Option using (??_)
open import Base.Bool using (tt; ff)
open import Base.Nat using (ℕ; _≡ᵇ_)
open import Base.List using (List; [])
open import Base.List.Nat using (_!!_; upd; repeat)
open import Base.Option using (some)
open import Base.Eq using (_≡_; refl; ◠_)
open import Shog.Lang.Expr ℓ using (Type; ◸_; _→*_; Addr; addr; Expr; Expr˂; ▶_;
  ∇_; nd; λ˙; _◁_; ★_; _←_; alloc; free; Val; V⇒E)

private variable
  A :  Set ℓ
  T U V :  Type
  e :  Expr ∞ T

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

-------------------------------------------------------------------------------
-- Redex

infix 6 ▶ᴿ_ ★ᴿ_ _←ᴿ_
infixl 5 _◁ᴿ_

data  Redex :  Type →  Set (^ ℓ)  where
  ▶ᴿ_ :  Expr˂ ∞ T →  Redex T
  ndᴿ :  Redex (◸ A)
  _◁ᴿ_ :  (A → Expr ∞ T) →  A →  Redex T
  ★ᴿ_ :  Addr →  Redex T
  _←ᴿ_ :  Addr →  Val T →  Redex (◸ ⊤)
  allocᴿ :  ℕ →  Redex (◸ Up Addr)
  freeᴿ :  Addr →  Redex (◸ ⊤)

R⇒E :  Redex T →  Expr ∞ T
R⇒E (▶ᴿ e˂) =  ▶ e˂
R⇒E ndᴿ =  nd
R⇒E (e˙ ◁ᴿ a) =  λ˙ e˙ ◁ ∇ a
R⇒E (★ᴿ x) =  ★ ∇ ↑ x
R⇒E (x ←ᴿ v) =  ∇ ↑ x ← V⇒E v
R⇒E (allocᴿ n) =  alloc $ ∇ ↑ n
R⇒E (freeᴿ x) =  free $ ∇ ↑ x

--------------------------------------------------------------------------------
-- Ktx: Syntactic evaluation context

infix 6 ★ᴷ_ _←ᴷʳ_ _←ᴷˡ_
infixl 5 _◁ᴷʳ_ _◁ᴷˡ_
data  Ktx :  Type →  Type →  Set (^ ℓ)  where
  -- Hole
  •ᴷ :  Ktx T T
  -- On _◁_
  _◁ᴷʳ_ :  Expr ∞ (A →* T) →  Ktx U (◸ A) →  Ktx U T
  _◁ᴷˡ_ :  Ktx U (A →* T) →  A →  Ktx U T
  -- On ★_
  ★ᴷ_ :  Ktx U (◸ Up Addr) →  Ktx U T
  -- On _←_
  _←ᴷʳ_ :  Expr ∞ (◸ Up Addr) →  Ktx U T →  Ktx U (◸ ⊤)
  _←ᴷˡ_ :  Ktx U (◸ Up Addr) →  Val T →  Ktx U (◸ ⊤)
  -- On alloc
  allocᴷ :  Ktx T (◸ Up ℕ) →  Ktx T (◸ Up Addr)
  -- On free
  freeᴷ :  Ktx T (◸ Up Addr) →  Ktx T (◸ ⊤)

-- Fill in the hole of Ktx U T with Expr ∞ U to get Expr ∞ T

infix 5 _ᴷ◀_
_ᴷ◀_ :  Ktx U T →  Expr ∞ U →  Expr ∞ T
•ᴷ ᴷ◀ e =  e
(e' ◁ᴷʳ ktx) ᴷ◀ e =  e' ◁ (ktx ᴷ◀ e)
(ktx ◁ᴷˡ a) ᴷ◀ e =  (ktx ᴷ◀ e) ◁ ∇ a
★ᴷ ktx ᴷ◀ e =  ★ (ktx ᴷ◀ e)
(e' ←ᴷʳ ktx) ᴷ◀ e =  e' ← (ktx ᴷ◀ e)
(ktx ←ᴷˡ v) ᴷ◀ e =  (ktx ᴷ◀ e) ← V⇒E v
allocᴷ ktx ᴷ◀ e =  alloc $ ktx ᴷ◀ e
freeᴷ ktx ᴷ◀ e =  free $ ktx ᴷ◀ e

-- Compose Ktx U T and Ktx V U

infix 5 _ᴷ∙ᴷ_
_ᴷ∙ᴷ_ :  Ktx U T →  Ktx V U →  Ktx V T
•ᴷ ᴷ∙ᴷ ktx =  ktx
(e ◁ᴷʳ ktx) ᴷ∙ᴷ ktx' =  e ◁ᴷʳ (ktx ᴷ∙ᴷ ktx')
(ktx ◁ᴷˡ a) ᴷ∙ᴷ ktx' =  (ktx ᴷ∙ᴷ ktx') ◁ᴷˡ a
★ᴷ ktx ᴷ∙ᴷ ktx' =  ★ᴷ (ktx ᴷ∙ᴷ ktx')
(e ←ᴷʳ ktx) ᴷ∙ᴷ ktx' =  e ←ᴷʳ (ktx ᴷ∙ᴷ ktx')
(ktx ←ᴷˡ v) ᴷ∙ᴷ ktx' =  (ktx ᴷ∙ᴷ ktx') ←ᴷˡ v
allocᴷ ktx ᴷ∙ᴷ ktx' =  allocᴷ $ ktx ᴷ∙ᴷ ktx'
freeᴷ ktx ᴷ∙ᴷ ktx' =  freeᴷ $ ktx ᴷ∙ᴷ ktx'

-- Type for a context-redex pair
Ktxred :  Type →  Set (^ ℓ)
Ktxred T =  ∑ U , Ktx U T × Redex U

-- Type for either a value or a context-redex pair

Val/Ktxred :  Type →  Set (^ ℓ)
Val/Ktxred T =  Val T ⊎ Ktxred T

private variable
  ktx ktx' ktx'' :  Ktx V U
  red :  Redex V
  e' e! :  Expr ∞ U
  kr : Ktxred T

abstract
  ᴷ∙ᴷ-ᴷ◀ :  ∀{ktx : Ktx U V} {ktx' : Ktx T U} {e} →
            (ktx ᴷ∙ᴷ ktx') ᴷ◀ e ≡ ktx ᴷ◀ (ktx' ᴷ◀ e)
  ᴷ∙ᴷ-ᴷ◀ {ktx = •ᴷ} =  refl
  ᴷ∙ᴷ-ᴷ◀ {ktx = _ ◁ᴷʳ ktx} {ktx'} {e}
    rewrite ᴷ∙ᴷ-ᴷ◀ {ktx = ktx} {ktx'} {e} =  refl
  ᴷ∙ᴷ-ᴷ◀ {ktx = ktx ◁ᴷˡ _} {ktx'} {e}
    rewrite ᴷ∙ᴷ-ᴷ◀ {ktx = ktx} {ktx'} {e} =  refl
  ᴷ∙ᴷ-ᴷ◀ {ktx = ★ᴷ ktx} {ktx'} {e}
    rewrite ᴷ∙ᴷ-ᴷ◀ {ktx = ktx} {ktx'} {e} =  refl
  ᴷ∙ᴷ-ᴷ◀ {ktx = _ ←ᴷʳ ktx} {ktx'} {e}
    rewrite ᴷ∙ᴷ-ᴷ◀ {ktx = ktx} {ktx'} {e} =  refl
  ᴷ∙ᴷ-ᴷ◀ {ktx = ktx ←ᴷˡ _} {ktx'} {e}
    rewrite ᴷ∙ᴷ-ᴷ◀ {ktx = ktx} {ktx'} {e} =  refl
  ᴷ∙ᴷ-ᴷ◀ {ktx = allocᴷ ktx} {ktx'} {e}
    rewrite ᴷ∙ᴷ-ᴷ◀ {ktx = ktx} {ktx'} {e} =  refl
  ᴷ∙ᴷ-ᴷ◀ {ktx = freeᴷ ktx} {ktx'} {e}
    rewrite ᴷ∙ᴷ-ᴷ◀ {ktx = ktx} {ktx'} {e} =  refl

--------------------------------------------------------------------------------
-- Calculate the value or context-redex pair of the expression

val/ktxred :  Expr ∞ T →  Val/Ktxred T
val/ktxred (∇ a) =  inj₀ $ ↑ a
val/ktxred (λ˙ e˙) =  inj₀ $ e˙
val/ktxred (▶ e˂) =  inj₁ $ _ , •ᴷ , ▶ᴿ e˂
val/ktxred nd =  inj₁ $ _ , •ᴷ , ndᴿ
val/ktxred (e ◁ e') =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e'
  ... | inj₁ (_ , ktx , red) =  _ , e ◁ᴷʳ ktx , red
  ... | inj₀ (↑ a)  with val/ktxred e
  ...   | inj₁ (_ , ktx , red) =  _ , ktx ◁ᴷˡ a , red
  ...   | inj₀ v =  _ , •ᴷ , v ◁ᴿ a
val/ktxred (★ e) =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  ... | inj₁ (_ , ktx , red) =  _ , ★ᴷ ktx , red
  ... | inj₀ (↑ ↑ x) =  _ , •ᴷ , ★ᴿ x
val/ktxred (e ← e') =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e'
  ... | inj₁ (_ , ktx , red) =  _ , e ←ᴷʳ ktx , red
  ... | inj₀ v  with val/ktxred e
  ...   | inj₁ (_ , ktx , red) =  _ , ktx ←ᴷˡ v , red
  ...   | inj₀ (↑ ↑ x) =  _ , •ᴷ , x ←ᴿ v
val/ktxred (alloc e) =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  ... | inj₁ (_ , ktx , red) =  _ , allocᴷ ktx , red
  ... | inj₀ (↑ ↑ n) =  _ , •ᴷ , allocᴿ n
val/ktxred (free e) =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  ... | inj₁ (_ , ktx , red) =  _ , freeᴷ ktx , red
  ... | inj₀ (↑ ↑ x) =  _ , •ᴷ , freeᴿ x

-- Judge if the expression is non-value

nonval :  Expr ∞ T →  Set ○
nonval e  with val/ktxred e
... | inj₀ _ =  ⊥
... | inj₁ _ =  ⊤

abstract

  -- If val/ktxred e returns a value v, then e is v

  val/ktxred-val :  ∀{v : Val T} →  val/ktxred e ≡ inj₀ v →  e ≡ V⇒E v
  val/ktxred-val {e = ∇ _} refl =  refl
  val/ktxred-val {e = λ˙ _} refl =  refl

  -- Calculate val/ktxred (ktx ᴷ◀ e)

  val/ktxred-ktx :  val/ktxred e ≡ inj₁ (_ , ktx' , red) →
                    val/ktxred (ktx ᴷ◀ e) ≡ inj₁ (_ , ktx ᴷ∙ᴷ ktx' , red)
  val/ktxred-ktx {ktx = •ᴷ} eq =  eq
  val/ktxred-ktx {e = e} {ktx = _ ◁ᴷʳ ktx} eq
    rewrite val/ktxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ktxred-ktx {e = e} {ktx = ktx ◁ᴷˡ _} eq
    rewrite val/ktxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ktxred-ktx {e = e} {ktx = ★ᴷ ktx} eq
    rewrite val/ktxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ktxred-ktx {e = e} {ktx = _ ←ᴷʳ ktx} eq
    rewrite val/ktxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ktxred-ktx {e = e} {ktx = _←ᴷˡ_ {T = ◸ _} ktx _} eq
    rewrite val/ktxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ktxred-ktx {e = e} {ktx = _←ᴷˡ_ {T = _ →* _} ktx _} eq
    rewrite val/ktxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ktxred-ktx {e = e} {ktx = allocᴷ ktx} eq
    rewrite val/ktxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ktxred-ktx {e = e} {ktx = freeᴷ ktx} eq
    rewrite val/ktxred-ktx {e = e} {ktx = ktx} eq =  refl

  -- Nonval and syntactic context

  nonval-ktx :  nonval e →  nonval (ktx ᴷ◀ e)
  nonval-ktx {ktx = •ᴷ} n'e =  n'e
  nonval-ktx {ktx = _ ◁ᴷʳ _} =  _
  nonval-ktx {ktx = _ ◁ᴷˡ _} =  _
  nonval-ktx {ktx = ★ᴷ _} =  _
  nonval-ktx {ktx = _ ←ᴷʳ _} =  _
  nonval-ktx {ktx = _ ←ᴷˡ _} =  _
  nonval-ktx {ktx = allocᴷ _} =  _
  nonval-ktx {ktx = freeᴷ _} =  _

  -- Invert from val/ktxred (ktx ᴷ◀ e)

  val/ktxred-ktx-inv :  nonval e →  let (V , ktx'' , red) = kr in
    val/ktxred (ktx ᴷ◀ e) ≡ inj₁ (V , ktx'' , red) →
    ∑ ktx' ,  ktx'' ≡ ktx ᴷ∙ᴷ ktx'  ×  val/ktxred e ≡ inj₁ (V , ktx' , red)
  val/ktxred-ktx-inv {ktx = •ᴷ} _ eq =  _ , refl , eq
  val/ktxred-ktx-inv {e = e} {ktx = _ ◁ᴷʳ ktx} nv'e eq
    with val/ktxred (ktx ᴷ◀ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {kr = kr} {ktx} nv'e)
  ...   | inj₁ _ | _ | refl | ind  with ind refl
  ...     | ktx' , refl , eq' =  ktx' , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = ktx ◁ᴷˡ _} nv'e eq
    with val/ktxred (ktx ᴷ◀ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {kr = kr} {ktx} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = ★ᴷ ktx} nv'e eq
    with val/ktxred (ktx ᴷ◀ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {kr = kr} {ktx} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = _ ←ᴷʳ ktx} nv'e eq
    with val/ktxred (ktx ᴷ◀ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {kr = kr} {ktx} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = _←ᴷˡ_ {T = ◸ _} ktx _} nv'e eq
    with val/ktxred (ktx ᴷ◀ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {kr = kr} {ktx} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = _←ᴷˡ_ {T = _ →* _} ktx _} nv'e eq
    with val/ktxred (ktx ᴷ◀ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {kr = kr} {ktx} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = allocᴷ ktx} nv'e eq
    with val/ktxred (ktx ᴷ◀ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {kr = kr} {ktx} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = freeᴷ ktx} nv'e eq
    with val/ktxred (ktx ᴷ◀ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {kr = kr} {ktx} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'

--------------------------------------------------------------------------------
-- Reduction

private variable
  M M' :  Mem
  e˂ :  Expr˂ ∞ T
  e˙ :  A → Expr ∞ U
  a :  A
  x :  Addr
  u :  Val U
  b n :  ℕ

infix 4 _⇒ᴿ_ _⇒ᴱ_

-- Reduction on a redex
data  _⇒ᴿ_ :  ∀{T} →  (Redex T × Mem) →  (Expr ∞ T × Mem) →  Set (^ ^ ℓ)  where
  nd-red :  ∀ (a : A) →  (ndᴿ , M) ⇒ᴿ (∇ a , M)
  ▶-red :  (▶ᴿ e˂ , M) ⇒ᴿ (e˂ .! , M)
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

-- Enrich reduction with syntactic context

red-ktx :  (e , M) ⇒ᴱ (e' , M') →  (ktx ᴷ◀ e , M) ⇒ᴱ (ktx ᴷ◀ e' , M')
red-ktx {ktx = ktx} (redᴱ {ktx = ktx'} {e' = e'} eq r⇒)
  rewrite ◠ ᴷ∙ᴷ-ᴷ◀ {ktx = ktx} {ktx'} {e'} =  redᴱ (val/ktxred-ktx eq) r⇒

red-ktx-inv :  nonval e →  (ktx ᴷ◀ e , M) ⇒ᴱ (e! , M') →
               ∑ e' ,  e! ≡ ktx ᴷ◀ e'  ×  (e , M) ⇒ᴱ (e' , M')
red-ktx-inv {ktx = ktx} nv'e (redᴱ eq r⇒)  with val/ktxred-ktx-inv nv'e eq
... | _ , refl , eq' =  _ , ᴷ∙ᴷ-ᴷ◀ {ktx = ktx} , redᴱ eq' r⇒
