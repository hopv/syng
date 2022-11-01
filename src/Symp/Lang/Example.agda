--------------------------------------------------------------------------------
-- Example
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Symp.Lang.Example where

open import Base.Func using (_$_; _▷_)
open import Base.Few using (⊤; ¬_)
open import Base.Eq using (_≡_; refl)
open import Base.Size using (𝕊; !)
open import Base.Bool using (𝔹; tt; ff)
open import Base.Option using (¿_; ň)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_)
open import Base.Nat using (ℕ; ṡ_; ṗ_; _+_)
open import Base.Sety using ()
open import Symp.Lang.Expr using (Addr; Type; ◸_; _↷_; Expr; Expr∞; Expr˂∞; ∇_;
  λ¡-syntax; nd; _◁_; _⁏¡_; let-syntax; let¡-syntax; ev; fork¡; 🞰_; _←_; fau;
  free; loop; Heap)
open import Symp.Lang.Ktxred using (Redex; fauᴿ)
open import Symp.Lang.Reduce using (nd⇒; []⇒; redᴷᴿ; _⇒ᴱ⟨_⟩_; redᴱ)

private variable
  ι :  𝕊
  b :  𝔹
  T :  Type
  e e' :  Expr∞ T
  eˇ :  ¿ Expr∞ T
  e˂ :  Expr˂∞ T
  H H' :  Heap
  n :  ℕ

--------------------------------------------------------------------------------
-- Various expressions

-- stuck :  Some stuck expression

stuck :  Expr∞ (◸ ⊤)
stuck =  free $ ∇ (0 , 42)

-- plus:  Just add two natural-number arguments

plus :  Expr∞ $ (ℕ × ℕ) ↷ ◸ ℕ
plus =  λ' (m , n) ,¡ ∇ (m + n)

-- plus◁3,4 :  plus on 3 and 4

plus◁3,4 :  Expr∞ $ ◸ ℕ
plus◁3,4 =  plus ◁ ∇ (3 , 4)

-- ndnat :  Non-deterministic natural number

ndnat :  Expr∞ $ ◸ ℕ
ndnat =  nd

-- decrep :  Repeat decrementing the natural number at the address until it
--           becomes zero

decrep :  Addr →  Expr ι $ ◸ ⊤
decrep' :  Addr →  ℕ →  Expr ι $ ◸ ⊤

decrep θ =  let' n := 🞰 ∇ θ in' λ{ .! → decrep' θ n }

decrep' _ 0 =  ∇ _
decrep' θ (ṡ n) =  ∇ θ ← ∇ n ⁏¡ decrep θ

-- ndecrep :  decrep after initialization by a non-deterministic natural number

ndecrep :  Addr →  Expr∞ $ ◸ ⊤
ndecrep θ =  ∇ θ ← ndnat ⁏¡ decrep θ

-- ndecrepev∞ :  Loop ndecrep with an event

ndecrepev∞ :  Addr →  Expr ι $ ◸ ⊤
ndecrepev∞ θ =  ndecrep θ ⁏¡ ev λ{ .! → ndecrepev∞ θ }

-- fad :  Fetch and decrement, i.e., atomic decrement of the natural number at
--        the address, returning the original value

fadᴿ :  Addr →  Redex $ ◸ ℕ
fadᴿ =  fauᴿ ṗ_

fad :  Expr ι $ ◸ Addr →  Expr ι $ ◸ ℕ
fad =  fau ṗ_

-- fadrep θ :  Repeat fad on the address until the value becomes zero

fadrep :  Addr →  Expr ι $ ◸ ⊤
fadrep' :  Addr →  ℕ →  Expr ι $ ◸ ⊤

fadrep θ =  let' n := fad (∇ θ) in' λ{ .! → fadrep' θ n }
fadrep' _ 0 =  ∇ _
fadrep' θ (ṡ _) =  fadrep θ

-- forksfadrep θ k :  Fork threads that perform fadrep θ

forksfadrep :  Addr →  ℕ →  Expr ι $ ◸ ⊤
forksfadrep _ 0 =  ∇ _
forksfadrep θ (ṡ k') =  fork¡ (fadrep θ) ⁏¡ forksfadrep θ k'

-- nforksfadrep :  forksfadrep with non-deterministic natural numbers

nforksfadrep :  Addr →  Expr∞ $ ◸ ⊤
nforksfadrep θ =  ∇ θ ← ndnat ⁏¡ let' k := ndnat in¡ forksfadrep θ k

-- cntr← :  Counter using the heap, which increments the natural number at the
--          address θ and returns the original value n

cntr← :  Addr →  ℕ →  Expr˂∞ $ ◸ ℕ
cntr← θ k .! =  let' n := 🞰 ∇ θ in¡ ∇ θ ← ∇ (k + n) ⁏¡ ∇ n

--------------------------------------------------------------------------------
-- Construct reduction

abstract

  -- Reduce loop

  loop⇒ :  (loop {T = T} , H) ⇒ᴱ⟨ ff ⟩ (loop , ň , H)
  loop⇒ =  redᴱ refl $ redᴷᴿ []⇒

  -- Reduce plus◁3,4

  plus◁3,4⇒ :  (plus◁3,4 , H) ⇒ᴱ⟨ ff ⟩ (∇ 7 , ň , H)
  plus◁3,4⇒ =  redᴱ refl $ redᴷᴿ []⇒

  -- Reduce ndnat

  ndnat⇒ :  (ndnat , H) ⇒ᴱ⟨ ff ⟩ (∇ n , ň , H)
  ndnat⇒ =  redᴱ refl $ redᴷᴿ $ nd⇒ _

  -- Reduce ev

  ev⇒ :  (ev e˂ , H) ⇒ᴱ⟨ tt ⟩ (e˂ .! , ň , H)
  ev⇒ =  redᴱ refl $ redᴷᴿ []⇒

--------------------------------------------------------------------------------
-- Destruct reduction

abstract

  -- Invert reduction on loop

  loop⇒-inv :  (loop {T = T} , H) ⇒ᴱ⟨ b ⟩ (e , eˇ , H') →
               (b , e , eˇ , H') ≡ (ff , loop , ň , H)
  loop⇒-inv (redᴱ refl (redᴷᴿ []⇒)) =  refl

  -- stuck can't be reduced (it's stuck!)

  stuck-no⇒ :  ¬ (stuck , H) ⇒ᴱ⟨ b ⟩ (e , eˇ , H')
  stuck-no⇒ (redᴱ refl (redᴷᴿ r⇒)) =  r⇒ ▷ λ ()

  -- Invert reduction on plus◁3,4

  plus◁3,4⇒-inv :  (plus◁3,4 , H) ⇒ᴱ⟨ b ⟩ (e , eˇ , H') →
                   (b , e , eˇ , H') ≡ (ff , ∇ 7 , ň , H)
  plus◁3,4⇒-inv (redᴱ refl (redᴷᴿ []⇒)) =  refl

  -- Invert reduction on ndnat

  ndnat⇒-inv :  (ndnat , H) ⇒ᴱ⟨ b ⟩ (e , eˇ , H') →
                ∑ n , (b , e , eˇ , H') ≡ (ff , ∇ n , ň , H)
  ndnat⇒-inv (redᴱ refl (redᴷᴿ (nd⇒ _))) =  -, refl

  -- Invert reduction on ev

  ev⇒-inv :  (ev {T = T} e˂ , H) ⇒ᴱ⟨ b ⟩ (e' , eˇ , H') →
             (b , e' , eˇ , H') ≡ (tt , e˂ .! , ň , H)
  ev⇒-inv (redᴱ refl (redᴷᴿ []⇒)) =  refl
