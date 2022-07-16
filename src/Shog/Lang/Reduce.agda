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
open import Base.Eq using (_≡_; refl)
open import Shog.Lang.Expr ℓ using (Type; ◸_; _→*_; Addr; addr; Expr; ▶_; ∇_;
  nd; λ˙; _◁_; ★_; _←_; alloc; free; Val; V⇒E)

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

infix 6 ▶ᴿ_
infixl 5 _◁ᴿ_
infix 6 ★ᴿ_ _←ᴿ_

data  Redex :  Type →  Set (^ ℓ)  where
  ndᴿ :  Redex (◸ A)
  ▶ᴿ_ :  Expr ∞ T →  Redex T
  _◁ᴿ_ :  (A → Expr ∞ T) →  A →  Redex T
  ★ᴿ_ :  Addr →  Redex T
  _←ᴿ_ :  Addr →  Val T →  Redex (◸ ⊤)
  allocᴿ :  ℕ →  Redex (◸ Up Addr)
  freeᴿ :  Addr →  Redex (◸ ⊤)

--------------------------------------------------------------------------------
-- Context-redex pair

-- Type for a context-redex pair, i.e. a pair of an evaluation context & a redex

Ctxred :  Type →  Set (^ ℓ)
Ctxred T =  ∑ U , (Expr ∞ U → Expr ∞ T) × Redex U

-- Type for either a value or a context-redex pair

Val/Ctxred :  Type →  Set (^ ℓ)
Val/Ctxred T =  Val T ⊎ Ctxred T

-- Calculate the value or context-redex pair of the expression

val/ctxred :  Expr ∞ T →  Val/Ctxred T
val/ctxred (∇ a) =  inj₀ $ ↑ a
val/ctxred (λ˙ e˙) =  inj₀ $ e˙
val/ctxred (▶ e˂) =  inj₁ $ _ , id , ▶ᴿ (e˂ .!)
val/ctxred nd =  inj₁ $ _ , id , ndᴿ
val/ctxred (e ◁ e') =  inj₁ body
 where
  body :  Ctxred _
  body  with val/ctxred e'
  ... | inj₁ (_ , ctx , red) =  _ , (λ • → e ◁ ctx •) , red
  ... | inj₀ (↑ a)  with val/ctxred e
  ...   | inj₁ (_ , ctx , red) =  _ , (λ • → ctx • ◁ e') , red
  ...   | inj₀ v =  _ , id , v ◁ᴿ a
val/ctxred (★ e) =  inj₁ body
 where
  body :  Ctxred _
  body  with val/ctxred e
  ... | inj₁ (_ , ctx , red) =  _ , (λ • → ★ ctx •) , red
  ... | inj₀ (↑ ↑ x) =  _ , id , ★ᴿ x
val/ctxred (e ← e') =  inj₁ body
 where
  body :  Ctxred _
  body  with val/ctxred e'
  ... | inj₁ (_ , ctx , red) =  _ , (λ • → e ← ctx •) , red
  ... | inj₀ v  with val/ctxred e
  ...   | inj₁ (_ , ctx , red) =  _ , (λ • → ctx • ← V⇒E v) , red
  ...   | inj₀ (↑ ↑ x) =  _ , id , x ←ᴿ v
val/ctxred (alloc e) =  inj₁ body
 where
  body :  Ctxred _
  body  with val/ctxred e
  ... | inj₁ (_ , ctx , red) =  _ , (λ • → alloc $ ctx •) , red
  ... | inj₀ (↑ ↑ n) =  _ , id , allocᴿ n
val/ctxred (free e) =  inj₁ body
 where
  body :  Ctxred _
  body  with val/ctxred e
  ... | inj₁ (_ , ctx , red) =  _ , (λ • → free $ ctx •) , red
  ... | inj₀ (↑ ↑ x) =  _ , id , freeᴿ x

-- Judge if the expression is non-value

nonval :  Expr ∞ T →  Set ○
nonval e  with val/ctxred e
... | inj₀ _ =  ⊥
... | inj₁ _ =  ⊤

abstract

  -- If val/ctxred e returns a value v, then e is v

  val/ctxred-val :  ∀{v : Val T} →  val/ctxred e ≡ inj₀ v →  e ≡ V⇒E v
  val/ctxred-val {e = ∇ _} refl =  refl
  val/ctxred-val {e = λ˙ _} refl =  refl

--------------------------------------------------------------------------------
-- Ktx: Syntactic evaluation context

data  Ktx :  Type →  Type →  Set (^ ℓ)  where
  -- Hole
  [•] :  Ktx T T
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

-- Interpret Ktx U T as Expr ∞ U → Expr ∞ T

infix 5 _•←_
_•←_ :  Ktx U T →  Expr ∞ U →  Expr ∞ T
[•] •← e =  e
(e' ◁ᴷʳ ktx) •← e =  e' ◁ (ktx •← e)
(ktx ◁ᴷˡ a) •← e =  (ktx •← e) ◁ ∇ a
★ᴷ ktx •← e =  ★ (ktx •← e)
(e' ←ᴷʳ ktx) •← e =  e' ← (ktx •← e)
(ktx ←ᴷˡ v) •← e =  (ktx •← e) ← V⇒E v
allocᴷ ktx •← e =  alloc (ktx •← e)
freeᴷ ktx •← e =  free (ktx •← e)

private variable
  ctx ctx' :  Expr ∞ V → Expr ∞ U
  red :  Redex V
  ktx : Ktx U T
  e' e! :  Expr ∞ U

abstract

  -- Calculate val/ctxred (ktx •← e)

  val/ctxred-ktx :  val/ctxred e ≡ inj₁ (_ , ctx , red) →
                    val/ctxred (ktx •← e) ≡ inj₁ (_ , (ktx •←_) ∘ ctx , red)
  val/ctxred-ktx {ktx = [•]} eq =  eq
  val/ctxred-ktx {e = e} {ktx = _ ◁ᴷʳ ktx} eq
    rewrite val/ctxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ctxred-ktx {e = e} {ktx = ktx ◁ᴷˡ _} eq
    rewrite val/ctxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ctxred-ktx {e = e} {ktx = ★ᴷ ktx} eq
    rewrite val/ctxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ctxred-ktx {e = e} {ktx = _ ←ᴷʳ ktx} eq
    rewrite val/ctxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ctxred-ktx {e = e} {ktx = _←ᴷˡ_ {T = ◸ _} ktx _} eq
    rewrite val/ctxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ctxred-ktx {e = e} {ktx = _←ᴷˡ_ {T = _ →* _} ktx _} eq
    rewrite val/ctxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ctxred-ktx {e = e} {ktx = allocᴷ ktx} eq
    rewrite val/ctxred-ktx {e = e} {ktx = ktx} eq =  refl
  val/ctxred-ktx {e = e} {ktx = freeᴷ ktx} eq
    rewrite val/ctxred-ktx {e = e} {ktx = ktx} eq =  refl

  -- Nonval and syntactic context

  nonval-ktx :  nonval e →  nonval (ktx •← e)
  nonval-ktx {ktx = [•]} n'e =  n'e
  nonval-ktx {ktx = _ ◁ᴷʳ _} =  _
  nonval-ktx {ktx = _ ◁ᴷˡ _} =  _
  nonval-ktx {ktx = ★ᴷ _} =  _
  nonval-ktx {ktx = _ ←ᴷʳ _} =  _
  nonval-ktx {ktx = _ ←ᴷˡ _} =  _
  nonval-ktx {ktx = allocᴷ _} =  _
  nonval-ktx {ktx = freeᴷ _} =  _

  -- Invert from val/ctxred (ktx •← e)

  val/ctxred-ktx-inv :
    nonval e →  val/ctxred (ktx •← e) ≡ inj₁ (V , ctx' , red) →
    ∑ ctx ,  ctx' ≡ (ktx •←_) ∘ ctx  ×  val/ctxred e ≡ inj₁ (V , ctx , red)
  val/ctxred-ktx-inv {ktx = [•]} _ eq =  _ , refl , eq
  val/ctxred-ktx-inv {e = e} {ktx = _ ◁ᴷʳ ktx} nv'e eq
    with val/ctxred (ktx •← e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{V ctx' red} → val/ctxred-ktx-inv {ktx = ktx} {V} {ctx'} {red} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ctx , refl , eq' =  ctx , refl , eq'
  val/ctxred-ktx-inv {e = e} {ktx = ktx ◁ᴷˡ _} nv'e eq
    with val/ctxred (ktx •← e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{V ctx' red} → val/ctxred-ktx-inv {ktx = ktx} {V} {ctx'} {red} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ctx , refl , eq' =  ctx , refl , eq'
  val/ctxred-ktx-inv {e = e} {ktx = ★ᴷ ktx} nv'e eq
    with val/ctxred (ktx •← e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{V ctx' red} → val/ctxred-ktx-inv {ktx = ktx} {V} {ctx'} {red} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ctx , refl , eq' =  ctx , refl , eq'
  val/ctxred-ktx-inv {e = e} {ktx = _ ←ᴷʳ ktx} nv'e eq
    with val/ctxred (ktx •← e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{V ctx' red} → val/ctxred-ktx-inv {ktx = ktx} {V} {ctx'} {red} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ctx , refl , eq' =  ctx , refl , eq'
  val/ctxred-ktx-inv {e = e} {ktx = _←ᴷˡ_ {T = ◸ _} ktx _} nv'e eq
    with val/ctxred (ktx •← e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{V ctx' red} → val/ctxred-ktx-inv {ktx = ktx} {V} {ctx'} {red} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ctx , refl , eq' =  ctx , refl , eq'
  val/ctxred-ktx-inv {e = e} {ktx = _←ᴷˡ_ {T = _ →* _} ktx _} nv'e eq
    with val/ctxred (ktx •← e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{V ctx' red} → val/ctxred-ktx-inv {ktx = ktx} {V} {ctx'} {red} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ctx , refl , eq' =  ctx , refl , eq'
  val/ctxred-ktx-inv {e = e} {ktx = allocᴷ ktx} nv'e eq
    with val/ctxred (ktx •← e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{V ctx' red} → val/ctxred-ktx-inv {ktx = ktx} {V} {ctx'} {red} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ctx , refl , eq' =  ctx , refl , eq'
  val/ctxred-ktx-inv {e = e} {ktx = freeᴷ ktx} nv'e eq
    with val/ctxred (ktx •← e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{V ctx' red} → val/ctxred-ktx-inv {ktx = ktx} {V} {ctx'} {red} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ctx , refl , eq' =  ctx , refl , eq'

--------------------------------------------------------------------------------
-- Reduction

private variable
  M M' :  Mem
  e˙ :  A → Expr ∞ U
  a :  A
  x :  Addr
  u :  Val U
  b n :  ℕ

infix 4 _⇒ᴿ_ _⇒ᴱ_

-- Reduction on a redex
data  _⇒ᴿ_ :  ∀{T} →  (Redex T × Mem) →  (Expr ∞ T × Mem) →  Set (^ ^ ℓ)  where
  nd-red :  ∀ (a : A) →  (ndᴿ , M) ⇒ᴿ (∇ a , M)
  ▶-red :  (▶ᴿ e , M) ⇒ᴿ (e , M)
  ◁-red :  (e˙ ◁ᴿ a , M) ⇒ᴿ (e˙ a , M)
  ★-red :  M !!ᴹ x ≡ some (U , u) →  (★ᴿ x , M) ⇒ᴿ (V⇒E u , M)
  ←-red :  ∀{v : Val V} →  (x ←ᴿ v , M) ⇒ᴿ (∇ _ , updᴹ x (_ , v) M)
  alloc-red :  ∀ b →  M .bloᴹ b ≡ [] →
    (allocᴿ n , M) ⇒ᴿ (∇ ↑ addr b 0 , updᴹᴮ b (repeat n (◸ ⊤ , _)) M)
  free-red :  (freeᴿ (addr b 0) , M) ⇒ᴿ (∇ _ , updᴹᴮ b [] M)

-- Reduction on an expression
data  _⇒ᴱ_ {T} :  (Expr ∞ T × Mem) →  (Expr ∞ T × Mem) →  Set (^ ^ ℓ)  where
  redᴱ :  val/ctxred e ≡ inj₁ (_ , ctx , red) →  (red , M) ⇒ᴿ (e' , M') →
          (e , M) ⇒ᴱ (ctx e' , M')

-- Enrich reduction with syntactic context

red-ktx :  (e , M) ⇒ᴱ (e' , M') → (ktx •← e , M) ⇒ᴱ (ktx •← e' , M')
red-ktx (redᴱ eq r⇒) =  redᴱ (val/ctxred-ktx eq) r⇒

red-ktx-inv :  nonval e →  (ktx •← e , M) ⇒ᴱ (e! , M') →
               ∑ e' ,  e! ≡ ktx •← e' × (e , M) ⇒ᴱ (e' , M')
red-ktx-inv nv'e (redᴱ eq r⇒)  with val/ctxred-ktx-inv nv'e eq
... | _ , refl , eq' =  _ , refl , redᴱ eq' r⇒
