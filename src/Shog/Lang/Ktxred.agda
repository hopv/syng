--------------------------------------------------------------------------------
-- Evaluation context and redex
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Lang.Ktxred (ℓ : Level) where

open import Base.Level using (○; ^_; Up; ↑_)
open import Base.Size using (∞)
open import Base.Func using (_$_)
open import Base.Few using (⊤; ⊥)
open import Base.Prod using (∑-syntax; _×_; _,_)
open import Base.Sum using (_⊎_; inj₀; inj₁)
open import Base.Eq using (_≡_; refl)
open import Base.Nat using (ℕ)
open import Shog.Lang.Expr ℓ using (Type; ◸_; _→*_; Addr; Expr; Expr˂; ▶_; ∇_;
  nd; λ˙; _◁_; ★_; _←_; alloc; free; Val; V⇒E)

private variable
  A :  Set ℓ
  T U V :  Type
  e :  Expr ∞ T

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

infix 5 _ᴷ◁_
_ᴷ◁_ :  Ktx U T →  Expr ∞ U →  Expr ∞ T
•ᴷ ᴷ◁ e =  e
(e' ◁ᴷʳ ktx) ᴷ◁ e =  e' ◁ (ktx ᴷ◁ e)
(ktx ◁ᴷˡ a) ᴷ◁ e =  (ktx ᴷ◁ e) ◁ ∇ a
★ᴷ ktx ᴷ◁ e =  ★ (ktx ᴷ◁ e)
(e' ←ᴷʳ ktx) ᴷ◁ e =  e' ← (ktx ᴷ◁ e)
(ktx ←ᴷˡ v) ᴷ◁ e =  (ktx ᴷ◁ e) ← V⇒E v
allocᴷ ktx ᴷ◁ e =  alloc $ ktx ᴷ◁ e
freeᴷ ktx ᴷ◁ e =  free $ ktx ᴷ◁ e

-- Compose Ktx U T and Ktx V U

infix 5 _ᴷ∘ᴷ_
_ᴷ∘ᴷ_ :  Ktx U T →  Ktx V U →  Ktx V T
•ᴷ ᴷ∘ᴷ ktx =  ktx
(e ◁ᴷʳ ktx) ᴷ∘ᴷ ktx' =  e ◁ᴷʳ (ktx ᴷ∘ᴷ ktx')
(ktx ◁ᴷˡ a) ᴷ∘ᴷ ktx' =  (ktx ᴷ∘ᴷ ktx') ◁ᴷˡ a
★ᴷ ktx ᴷ∘ᴷ ktx' =  ★ᴷ (ktx ᴷ∘ᴷ ktx')
(e ←ᴷʳ ktx) ᴷ∘ᴷ ktx' =  e ←ᴷʳ (ktx ᴷ∘ᴷ ktx')
(ktx ←ᴷˡ v) ᴷ∘ᴷ ktx' =  (ktx ᴷ∘ᴷ ktx') ←ᴷˡ v
allocᴷ ktx ᴷ∘ᴷ ktx' =  allocᴷ $ ktx ᴷ∘ᴷ ktx'
freeᴷ ktx ᴷ∘ᴷ ktx' =  freeᴷ $ ktx ᴷ∘ᴷ ktx'

-- Type for a context-redex pair
Ktxred :  Type →  Set (^ ℓ)
Ktxred T =  ∑ U , Ktx U T × Redex U

-- Type for either a value or a context-redex pair

Val/Ktxred :  Type →  Set (^ ℓ)
Val/Ktxred T =  Val T ⊎ Ktxred T

private variable
  ktx ktx' ktx'' :  Ktx V U
  red :  Redex V
  kr : Ktxred T

abstract

  -- On ᴷ∘ᴷ and ᴷ◁

  ᴷ∘ᴷ-ᴷ◁ :  ∀{ktx : Ktx U V} {ktx' : Ktx T U} {e} →
            (ktx ᴷ∘ᴷ ktx') ᴷ◁ e ≡ ktx ᴷ◁ (ktx' ᴷ◁ e)
  ᴷ∘ᴷ-ᴷ◁ {ktx = •ᴷ} =  refl
  ᴷ∘ᴷ-ᴷ◁ {ktx = _ ◁ᴷʳ ktx} {ktx'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {ktx = ktx} {ktx'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {ktx = ktx ◁ᴷˡ _} {ktx'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {ktx = ktx} {ktx'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {ktx = ★ᴷ ktx} {ktx'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {ktx = ktx} {ktx'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {ktx = _ ←ᴷʳ ktx} {ktx'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {ktx = ktx} {ktx'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {ktx = ktx ←ᴷˡ _} {ktx'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {ktx = ktx} {ktx'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {ktx = allocᴷ ktx} {ktx'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {ktx = ktx} {ktx'} {e} =  refl
  ᴷ∘ᴷ-ᴷ◁ {ktx = freeᴷ ktx} {ktx'} {e}
    rewrite ᴷ∘ᴷ-ᴷ◁ {ktx = ktx} {ktx'} {e} =  refl

--------------------------------------------------------------------------------
-- Calculate the value or context-redex pair of the expression

val/ktxred :  Expr ∞ T →  Val/Ktxred T
val/ktxred (∇ a) =  inj₀ $ ↑ a
val/ktxred (λ˙ e˙) =  inj₀ $ e˙
val/ktxred (▶ e˂) =  inj₁ $ _ , •ᴷ , ▶ᴿ e˂
val/ktxred nd =  inj₁ $ _ , •ᴷ , ndᴿ
val/ktxred (e' ◁ e) =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  ... | inj₁ (_ , ktx , red) =  _ , e' ◁ᴷʳ ktx , red
  ... | inj₀ (↑ a)  with val/ktxred e'
  ...   | inj₁ (_ , ktx , red) =  _ , ktx ◁ᴷˡ a , red
  ...   | inj₀ v =  _ , •ᴷ , v ◁ᴿ a
val/ktxred (★ e) =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  ... | inj₁ (_ , ktx , red) =  _ , ★ᴷ ktx , red
  ... | inj₀ (↑ ↑ x) =  _ , •ᴷ , ★ᴿ x
val/ktxred (e' ← e) =  inj₁ body
 where
  body :  Ktxred _
  body  with val/ktxred e
  ... | inj₁ (_ , ktx , red) =  _ , e' ←ᴷʳ ktx , red
  ... | inj₀ v  with val/ktxred e'
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

  -- If val/ktxred e returns a context-redex pair (_ , ktx , red),
  -- then e is ktx with the hole filled with red

  val/ktxred-ktxred :  ∀{kr : Ktxred T} → let (_ , ktx , red) = kr in
    val/ktxred e ≡ inj₁ (_ , ktx , red) →  e ≡ ktx ᴷ◁ R⇒E red
  val/ktxred-ktxred {e = ▶ _} refl =  refl
  val/ktxred-ktxred {e = nd} refl =  refl
  val/ktxred-ktxred {e = e' ◁ e} refl  with val/ktxred e |
    val/ktxred-ktxred {e = e} | val/ktxred-val {e = e}
  ... | inj₁ _ | ind | val  rewrite ind refl =  refl
  ... | inj₀ _ | _ | val  rewrite val refl  with val/ktxred e' |
    val/ktxred-ktxred {e = e'} | val/ktxred-val {e = e'}
  ...   | inj₁ _ | ind' | _  rewrite ind' refl =  refl
  ...   | inj₀ _ | _ | val'  rewrite val' refl =  refl
  val/ktxred-ktxred {e = ★ e} refl  with val/ktxred e |
    val/ktxred-ktxred {e = e} | val/ktxred-val {e = e}
  ... | inj₁ _ | ind | _  rewrite ind refl =  refl
  ... | inj₀ _ | _ | val  rewrite val refl =  refl
  val/ktxred-ktxred {e = e' ← e} refl  with val/ktxred e |
    val/ktxred-ktxred {e = e} | val/ktxred-val {e = e}
  ... | inj₁ _ | ind | _  rewrite ind refl =  refl
  ... | inj₀ _ | _ | val  rewrite val refl  with val/ktxred e' |
    val/ktxred-ktxred {e = e'} | val/ktxred-val {e = e'}
  ...   | inj₁ _ | ind' | _  rewrite ind' refl =  refl
  ...   | inj₀ _ | _ | val'  rewrite val' refl =  refl
  val/ktxred-ktxred {e = alloc e} refl  with val/ktxred e |
    val/ktxred-ktxred {e = e} | val/ktxred-val {e = e}
  ... | inj₁ _ | ind | _  rewrite ind refl =  refl
  ... | inj₀ _ | _ | val  rewrite val refl =  refl
  val/ktxred-ktxred {e = free e} refl  with val/ktxred e |
    val/ktxred-ktxred {e = e} | val/ktxred-val {e = e}
  ... | inj₁ _ | ind | _  rewrite ind refl =  refl
  ... | inj₀ _ | _ | val  rewrite val refl =  refl

  -- Nonval enriched with an evaluation context

  nonval-ktx :  nonval e →  nonval (ktx ᴷ◁ e)
  nonval-ktx {ktx = •ᴷ} n'e =  n'e
  nonval-ktx {ktx = _ ◁ᴷʳ _} =  _
  nonval-ktx {ktx = _ ◁ᴷˡ _} =  _
  nonval-ktx {ktx = ★ᴷ _} =  _
  nonval-ktx {ktx = _ ←ᴷʳ _} =  _
  nonval-ktx {ktx = _ ←ᴷˡ _} =  _
  nonval-ktx {ktx = allocᴷ _} =  _
  nonval-ktx {ktx = freeᴷ _} =  _

  -- Calculate val/ktxred (ktx ᴷ◁ e)

  val/ktxred-ktx :  val/ktxred e ≡ inj₁ (_ , ktx' , red) →
                    val/ktxred (ktx ᴷ◁ e) ≡ inj₁ (_ , ktx ᴷ∘ᴷ ktx' , red)
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

  -- Invert from val/ktxred (ktx ᴷ◁ e)

  val/ktxred-ktx-inv :  nonval e →  let (V , ktx'' , red) = kr in
    val/ktxred (ktx ᴷ◁ e) ≡ inj₁ (V , ktx'' , red) →
    ∑ ktx' ,  ktx'' ≡ ktx ᴷ∘ᴷ ktx'  ×  val/ktxred e ≡ inj₁ (V , ktx' , red)
  val/ktxred-ktx-inv {ktx = •ᴷ} _ eq =  _ , refl , eq
  val/ktxred-ktx-inv {e = e} {ktx = _ ◁ᴷʳ ktx} nv'e eq
    with val/ktxred (ktx ᴷ◁ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {kr = kr} {ktx} nv'e)
  ...   | inj₁ _ | _ | refl | ind  with ind refl
  ...     | ktx' , refl , eq' =  ktx' , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = ktx ◁ᴷˡ _} nv'e eq
    with val/ktxred (ktx ᴷ◁ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {kr = kr} {ktx} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = ★ᴷ ktx} nv'e eq
    with val/ktxred (ktx ᴷ◁ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {kr = kr} {ktx} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = _ ←ᴷʳ ktx} nv'e eq
    with val/ktxred (ktx ᴷ◁ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {kr = kr} {ktx} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = _←ᴷˡ_ {T = ◸ _} ktx _} nv'e eq
    with val/ktxred (ktx ᴷ◁ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {kr = kr} {ktx} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = _←ᴷˡ_ {T = _ →* _} ktx _} nv'e eq
    with val/ktxred (ktx ᴷ◁ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {kr = kr} {ktx} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = allocᴷ ktx} nv'e eq
    with val/ktxred (ktx ᴷ◁ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {kr = kr} {ktx} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
  val/ktxred-ktx-inv {e = e} {ktx = freeᴷ ktx} nv'e eq
    with val/ktxred (ktx ᴷ◁ e) | nonval-ktx {ktx = ktx} nv'e | eq |
      (λ{kr} → val/ktxred-ktx-inv {kr = kr} {ktx} nv'e)
  ... | inj₁ _ | _ | refl | ind  with ind refl
  ...   | ktx , refl , eq' =  ktx , refl , eq'
