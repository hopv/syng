--------------------------------------------------------------------------------
-- Reduction
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syng.Lang.Reduce where

open import Base.Func using (_$_; flip)
open import Base.Few using (⊤)
open import Base.Eq using (_≡_; _≢_; refl; ◠_)
open import Base.Dec using (upd˙)
open import Base.Acc using (Acc)
open import Base.Size using (𝕊; Thunk)
open import Base.Bool using (𝔹; tt; ff)
open import Base.Option using (¿_; ň; š_)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_)
open import Base.Sum using (ĩ₁_)
open import Base.Nat using (ℕ)
open import Base.List using (List; _∷_; ¿⇒ᴸ; _⧺_; rep)
open import Base.Sety using (Setʸ; ⸨_⸩ʸ)
open import Syng.Lang.Expr using (Type; ◸ʸ_; ◸_; Addr; Expr∞; Expr˂∞; ∇_; V⇒E;
  TyVal; ⊤-; Heap; _‼ᴴ_; updᴴ)
open import Syng.Lang.Ktxred using (Redex; ndᴿ; [_]ᴿ⟨_⟩; forkᴿ; 🞰ᴿ_; _←ᴿ_; fauᴿ;
  casᴿ; allocᴿ; freeᴿ; Ktx; _ᴷ◁_; Ktxred; val/ktxred)

--------------------------------------------------------------------------------
-- Reduction

private variable
  ι :  𝕊
  T U :  Type
  Xʸ :  Setʸ
  X :  Set₀
  b :  𝔹
  e₀ e e' e'' :  Expr∞ T
  e˂ :  Expr˂∞ T
  e˙ :  ⸨ Xʸ ⸩ʸ → Expr∞ T
  eˇ :  ¿ Expr∞ (◸ ⊤)
  es es' es'' :  List (Expr∞ (◸ ⊤))
  K :  Ktx T U
  red : Redex T
  v x y z :  X
  ᵗu :  TyVal
  f :  X → X
  n o :  ℕ
  kr :  Ktxred T
  H H' H'' :  Heap
  θ :  Addr

infix 4 _⇒ᴾ⟨_⟩_ _⇒ᴾ○_ _⇒ᴾ●_ _⇒ᴿ⟨_⟩_ _⇒ᴿ○_ _⇒ᴿ●_ _⇒ᴿ_ _⇒ᴷᴿ⟨_⟩_ _⇒ᴷᴿ_ _⇒ᴱ⟨_⟩_ _⇒ᴱ_
  _⇒ᵀ⟨_⟩_ _⇒ᵀ_ _⇐ᴿ_ _⇐ᴷᴿ⟨_⟩_ _⇐ᴷᴿ_ _⇐ᴱ_ _⇐ᵀ⟨_⟩_ _⇒ᵀ○_ _⇒ᵀ●_ _⇐ᵀ_ _⇒ᴿ∑ _⇒ᴷᴿ∑

-- ⇒ᴾ :  Pure reduction of an expression

data  _⇒ᴾ⟨_⟩_ :  Expr∞ T →  𝔹 →  Expr∞ T →  Set₀  where
  redᴾ :  val/ktxred e ≡ ĩ₁ (-, K , [ e₀ ]ᴿ⟨ b ⟩) →  e ⇒ᴾ⟨ b ⟩ K ᴷ◁ e₀

_⇒ᴾ_ _⇒ᴾ○_ _⇒ᴾ●_ :  Expr∞ T →  Expr∞ T →  Set₀
e ⇒ᴾ e' =  ∑ b , e ⇒ᴾ⟨ b ⟩ e'
e ⇒ᴾ○ e' =  e ⇒ᴾ⟨ ff ⟩ e'
e ⇒ᴾ● e' =  e ⇒ᴾ⟨ tt ⟩ e'

-- ⇒ᴿ :  Reduction of a redex
--       The 𝔹 part is the event flag
--       The ¿ Expr∞ (◸ ⊤) part is a possibly forked thread

data  _⇒ᴿ⟨_⟩_ :  Redex T × Heap →  𝔹 →  Expr∞ T × ¿ Expr∞ (◸ ⊤) × Heap →  Set₀

_⇒ᴿ○_ _⇒ᴿ●_ :  Redex T × Heap →  Expr∞ T × ¿ Expr∞ (◸ ⊤) × Heap →  Set₀
red ⇒ᴿ○ eeˇH =  red ⇒ᴿ⟨ ff ⟩ eeˇH
red ⇒ᴿ● eeˇH =  red ⇒ᴿ⟨ tt ⟩ eeˇH

data _⇒ᴿ⟨_⟩_ where

  -- For nd
  nd⇒ :  ∀(x : ⸨ Xʸ ⸩ʸ) →  (ndᴿ , H) ⇒ᴿ○ (∇ x , ň , H)

  -- Pure reduction
  []⇒ :  ([ e ]ᴿ⟨ b ⟩ , H) ⇒ᴿ⟨ b ⟩ (e , ň , H)

  -- For fork
  fork⇒ :  (forkᴿ e , H) ⇒ᴿ○ (∇ _ , š e , H)

  -- For 🞰
  🞰⇒ :  H ‼ᴴ θ ≡ š (T , v) →  (🞰ᴿ θ , H) ⇒ᴿ○ (V⇒E {T} v , ň , H)

  -- For ←, with a check that θ is in the domain of H
  ←⇒ :  H ‼ᴴ θ ≡ š ᵗu →  (_←ᴿ_ {T} θ v , H) ⇒ᴿ○ (∇ _ , ň , updᴴ θ (T , v) H)

  -- For fau
  fau⇒ :  H ‼ᴴ θ ≡ š (◸ʸ Xʸ , x) →
          (fauᴿ f θ , H) ⇒ᴿ○ (∇ x , ň , updᴴ θ (-, f x) H)

  -- For cas, the success and failure cases
  cas⇒-tt :  H ‼ᴴ θ ≡ š (◸ʸ Xʸ , x) →
             (casᴿ θ x y , H) ⇒ᴿ○ (∇ tt , ň , updᴴ θ (-, y) H)
  cas⇒-ff :  H ‼ᴴ θ ≡ š (◸ʸ Xʸ , z) →  z ≢ x →
             (casᴿ θ x y , H) ⇒ᴿ○ (∇ ff , ň , H)

  -- For alloc, for any o out of the domain of H
  alloc⇒ :  ∀ o →  H o ≡ ň →
    (allocᴿ n , H) ⇒ᴿ○ (∇ (o , 0) , ň , upd˙ o (š rep n ⊤-) H)

  -- For free, with a check that o is in the domain of H
  free⇒ :  ∑ ᵗvs , H o ≡ š ᵗvs →
    (freeᴿ (o , 0) , H) ⇒ᴿ○ (∇ _ , ň , upd˙ o ň H)

_⇒ᴿ_ :  Redex T × Heap →  Expr∞ T × ¿ Expr∞ (◸ ⊤) × Heap →  Set₀
redH ⇒ᴿ eeˇH' =  ∑ b , redH ⇒ᴿ⟨ b ⟩ eeˇH'

-- ⇒ᴷᴿ :  Reduction of a context-redex pair

data  _⇒ᴷᴿ⟨_⟩_ :  Ktxred T × Heap →  𝔹 →  Expr∞ T × ¿ Expr∞ (◸ ⊤) × Heap →
                  Set₀  where
  redᴷᴿ :  (red , H) ⇒ᴿ⟨ b ⟩ (e , eˇ , H') →
           ((-, K , red) , H) ⇒ᴷᴿ⟨ b ⟩ (K ᴷ◁ e , eˇ , H')

_⇒ᴷᴿ_ :  Ktxred T × Heap →  Expr∞ T × ¿ Expr∞ (◸ ⊤) × Heap →  Set₀
krH ⇒ᴷᴿ eeˇH' =  ∑ b , krH ⇒ᴷᴿ⟨ b ⟩ eeˇH'

-- ⇒ᴱ :  Reduction of an expression

data  _⇒ᴱ⟨_⟩_ :  Expr∞ T × Heap →  𝔹 →  Expr∞ T × ¿ Expr∞ (◸ ⊤) × Heap →
                 Set₀  where
  redᴱ :  val/ktxred e ≡ ĩ₁ kr →  (kr , H) ⇒ᴷᴿ⟨ b ⟩ (e' , eˇ , H') →
          (e , H) ⇒ᴱ⟨ b ⟩ (e' , eˇ , H')

_⇒ᴱ_ :  Expr∞ T × Heap →  Expr∞ T × ¿ Expr∞ (◸ ⊤) × Heap →  Set₀
eH ⇒ᴱ e'eˇH' =  ∑ b , eH ⇒ᴱ⟨ b ⟩ e'eˇH'

-- ⇒ᵀ :  Reduction of a thread list
-- The Bool part is the event flag for the head thread only

data  _⇒ᵀ⟨_⟩_ :  Expr∞ T × List (Expr∞ (◸ ⊤)) × Heap →
                 𝔹 →  Expr∞ T × List (Expr∞ (◸ ⊤)) × Heap →  Set₀  where

  -- Reduce the head thread
  redᵀ-hd :  (e , H) ⇒ᴱ⟨ b ⟩ (e' , eˇ , H') →
             (e , es , H) ⇒ᵀ⟨ b ⟩ (e' , ¿⇒ᴸ eˇ ⧺ es , H')

  -- Continue to the tail threads
  redᵀ-tl :  (e , es , H) ⇒ᵀ⟨ b ⟩ (e' , es' , H') →
             (e₀ , e ∷ es , H) ⇒ᵀ⟨ ff ⟩ (e₀ , e' ∷ es' , H')

_⇒ᵀ○_ _⇒ᵀ●_ _⇒ᵀ_ :  Expr∞ T × List (Expr∞ (◸ ⊤)) × Heap →
                    Expr∞ T × List (Expr∞ (◸ ⊤)) × Heap →  Set₀
eesH ⇒ᵀ○ e'es'H' =  eesH ⇒ᵀ⟨ ff ⟩ e'es'H'
eesH ⇒ᵀ● e'es'H' =  eesH ⇒ᵀ⟨ tt ⟩ e'es'H'
eesH ⇒ᵀ e'es'H' =  ∑ b , eesH ⇒ᵀ⟨ b ⟩ e'es'H'

-- ⇐ᴿ, ⇐ᴷᴿ⟨ ⟩, ⇐ᴷᴿ, ⇐ᴱ, ⇐ᵀ :  Flipped ⇒ᴿ, ⇒ᴷᴿ⟨ ⟩, ⇒ᴷᴿ, ⇒ᴱ, ⇒ᵀ

_⇐ᴿ_ :  Expr∞ T × ¿ Expr∞ (◸ ⊤) × Heap →  Redex T × Heap →  Set₀
_⇐ᴿ_ =  flip _⇒ᴿ_

_⇐ᴷᴿ⟨_⟩_ :  Expr∞ T × ¿ Expr∞ (◸ ⊤) × Heap →  𝔹 →  Ktxred T × Heap →  Set₀
e'eˇH' ⇐ᴷᴿ⟨ b ⟩ krH =  krH ⇒ᴷᴿ⟨ b ⟩ e'eˇH'

_⇐ᴷᴿ_ :  Expr∞ T × ¿ Expr∞ (◸ ⊤) × Heap →  Ktxred T × Heap →  Set₀
_⇐ᴷᴿ_ =  flip _⇒ᴷᴿ_

_⇐ᴱ_ :  Expr∞ T × ¿ Expr∞ (◸ ⊤) × Heap →  Expr∞ T × Heap →  Set₀
_⇐ᴱ_ =  flip _⇒ᴱ_

_⇐ᵀ⟨_⟩_ :  Expr∞ T × List (Expr∞ (◸ ⊤)) × Heap →
           𝔹 →  Expr∞ T × List (Expr∞ (◸ ⊤)) × Heap →  Set₀
e'es'H' ⇐ᵀ⟨ b ⟩ eesH =  eesH ⇒ᵀ⟨ b ⟩ e'es'H'

_⇐ᵀ_ :  Expr∞ T × List (Expr∞ (◸ ⊤)) × Heap →
        Expr∞ T × List (Expr∞ (◸ ⊤)) × Heap →  Set₀
_⇐ᵀ_ =  flip _⇒ᵀ_

-- ⇒ᴿ∑, ⇒ᴷᴿ∑ :  A redex / contex-redex pair is reducible

_⇒ᴿ∑ :   Redex T × Heap →  Set₀
redH ⇒ᴿ∑ =  ∑ beeˇH' , redH ⇒ᴿ beeˇH'

_⇒ᴷᴿ∑ :  Ktxred T × Heap →  Set₀
krH ⇒ᴷᴿ∑ =  ∑ beeˇH' , krH ⇒ᴷᴿ beeˇH'

abstract

  -- ⇒ᴾ implies ⇒ᴱ

  ⇒ᴾ⇒⇒ᴱ :  e ⇒ᴾ⟨ b ⟩ e' →  (e , H) ⇒ᴱ⟨ b ⟩ (e' , ň , H)
  ⇒ᴾ⇒⇒ᴱ (redᴾ e⇒K[e₀]) =  redᴱ e⇒K[e₀] $ redᴷᴿ []⇒

--------------------------------------------------------------------------------
-- ⇒ᵀ* :  Finite reduction sequence

infix 4 _⇒ᵀ*_

data  _⇒ᵀ*_ :  Expr∞ T × List (Expr∞ (◸ ⊤)) × Heap →
               Expr∞ T × List (Expr∞ (◸ ⊤)) × Heap →  Set₀  where

  -- End reduction
  ⇒ᵀ*-refl :  (e , es , H) ⇒ᵀ* (e , es , H)

  -- Continue reduction
  ⇒ᵀ*-step :  (e , es , H) ⇒ᵀ (e' , es' , H') →
              (e' , es' , H') ⇒ᵀ* (e'' , es'' , H'') →
              (e , es , H) ⇒ᵀ* (e'' , es'' , H'')

--------------------------------------------------------------------------------
-- SNᵀ :  The thread list with the heap is strongly normalizing, i.e., any
--        execution starting with the state eventually terminates
--        We define it by Acc, saying that the state is accessible w.r.t. ⇐ᵀ
--        We don't assume fair scheduling of threads here

SNᵀ :  Expr∞ T × List (Expr∞ (◸ ⊤)) × Heap →  Set₀
SNᵀ =  Acc _⇐ᵀ_

--------------------------------------------------------------------------------
-- Infᵀ :  Any execution starting with the thread list with the heap triggers
--         the event an infinite number of times
--         This means that the execution never terminates and from any point of
--         execution the event occurs in a finite number of steps
--         We don't assume fair scheduling of threads here

data  Infᵀ (ι : 𝕊) :  Expr∞ T × List (Expr∞ (◸ ⊤)) × Heap →  Set₀

-- Infᵀ˂ᴮ :  Infᵀ, under the thunk if the boolean is true

Infᵀ˂ᴮ :  𝔹 →  𝕊 →  Expr∞ T × List (Expr∞ (◸ ⊤)) × Heap →  Set₀
Infᵀ˂ᴮ ff ι eesH =  Infᵀ ι eesH
Infᵀ˂ᴮ tt ι eesH =  Thunk (λ ι' → Infᵀ ι' eesH) ι

data  Infᵀ ι  where
  infᵀ :  (∀{b e' es' H'} →  (e' , es' , H') ⇐ᵀ⟨ b ⟩ (e , es , H) →
            Infᵀ˂ᴮ b ι (e' , es' , H')) → Infᵀ ι (e , es , H)
