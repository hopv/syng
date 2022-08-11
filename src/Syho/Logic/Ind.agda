--------------------------------------------------------------------------------
-- Proof rules on ○ and ↪=>>
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Ind where

open import Base.Level using (Level; ↓_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk; ¡_; !)
open import Base.Few using (0⊤)
open import Base.Func using (_∘_; const)
open import Base.Prod using (_×_; _,_)
open import Base.Nat using (ℕ)
open import Base.List using ([_])
open import Base.List.All using ()
open import Syho.Logic.Prop using (Prop'; Prop˂; ∀₀-syntax; _∧_; _→'_; _∗_; □_;
  ○_; _↪[_]=>>_; Basic; ⊤-Basic)
open import Syho.Logic.Core using (_⊢[_]_; _⊢[<_]_; Pers; ⊢-refl; _»_; ∀₁-elim;
  ∧-elimˡ; ∧⊤-intro; →-mono; →-const; ∗-comm; ∗-elimʳ; ⊤∗-intro)
open import Syho.Logic.Supd using ([_]=>>_; _⊢[_][_]=>>_; _⊢[<_][_]=>>_; _ᵘ»_)

-- Import and re-export
open import Syho.Logic.Judg public using (○-mono-∗; ○-alloc; □○-alloc-mutrec;
  ○-use; ↪=>>-monoˡ-∗; ↪=>>-monoʳ-∗; ↪=>>-suc; ↪=>>-frameˡ; ○⇒∀₁↪=>>; ↪=>>-use)

private variable
  ℓ :  Level
  ι :  Size
  i j :  ℕ
  P Q :  Prop' ∞
  P˂ P'˂ Q˂ Q'˂ R˂ :  Prop˂ ∞
  X :  Set ℓ
  x :  X
  P˂˙ Q˂˙ :  X → Prop˂ ∞
  R :  Prop' ∞

abstract

  ------------------------------------------------------------------------------
  -- On ○

  -->  ○-use :  ○ P˂ ⊢[ ι ][ i ]=>> P˂ .!

  -- Monotonicity

  -->  ○-mono-∗ :  {{Basic R}} →  R ∗ P˂ .! ⊢[< ι ] Q˂ .! →
  -->              R ∗ ○ P˂ ⊢[ ι ] ○ Q˂

  ○-mono :  P˂ .! ⊢[< ι ] Q˂ .! →  ○ P˂ ⊢[ ι ] ○ Q˂
  ○-mono P⊢<Q =  ⊤∗-intro » ○-mono-∗ λ{ .! → ∗-elimʳ » P⊢<Q .! }

  -- Allocation

  -->  ○-alloc :  P˂ .! ⊢[ ι ][ i ]=>> ○ P˂

  -->  □○-alloc-mutrec :  {{All (λ P˂ → Pers (P˂ .!)) P˂s}} →
  -->    [∧ P˂ ∈ P˂s ] □ ○ P˂ →' [∧ P˂ ∈ P˂s ] P˂ .!
  -->                   ⊢[ ι ][ i ]=>> [∧ P˂ ∈ P˂s ] □ ○ P˂

  □○-alloc-rec :  {{Pers (P˂ .!)}} →  □ ○ P˂ →' P˂ .! ⊢[ ι ][ i ]=>> □ ○ P˂
  □○-alloc-rec =  →-mono ∧-elimˡ ∧⊤-intro » □○-alloc-mutrec ᵘ» ∧-elimˡ

  □○-alloc :  {{Pers (P˂ .!)}} →  P˂ .! ⊢[ ι ][ i ]=>> □ ○ P˂
  □○-alloc =  →-const » □○-alloc-rec

  ------------------------------------------------------------------------------
  -- On ↪=>>

  -->  ↪=>>-use :  P˂ .! ∗ (P˂ ↪[ i ]=>> Q˂)  ⊢[ ι ][ suc i ]=>>  Q˂ .!

  -- Monotonicity of ↪=>>

  -->  ↪=>>-monoˡ-∗ :  {{Basic R}} →  R ∗ P'˂ .! ⊢[< ι ] P˂ .! →
  -->                  R ∗ (P˂ ↪[ i ]=>> Q˂)  ⊢[ ι ]  P'˂ ↪[ i ]=>> Q˂

  -->  ↪=>>-monoʳ-∗ :  {{Basic R}} →  R ∗ Q˂ .! ⊢[< ι ] Q'˂ .! →
  -->                  R ∗ (P˂ ↪[ i ]=>> Q˂)  ⊢[ ι ]  P˂ ↪[ i ]=>> Q'˂

  -- We don't have ↪=>>-mono rules (which modify both the P and Q sides),
  -- because handling two thunks doesn't work well on the current Agda

  ↪=>>-monoˡ :  P'˂ .! ⊢[< ι ] P˂ .! →
                P˂ ↪[ i ]=>> Q˂  ⊢[ ι ]  P'˂ ↪[ i ]=>> Q˂
  ↪=>>-monoˡ P'⊢<P =  ⊤∗-intro » ↪=>>-monoˡ-∗ λ{ .! → ∗-elimʳ » P'⊢<P .! }

  ↪=>>-monoʳ :  Q˂ .! ⊢[< ι ] Q'˂ .! →
                P˂ ↪[ i ]=>> Q˂  ⊢[ ι ]  P˂ ↪[ i ]=>> Q'˂
  ↪=>>-monoʳ Q⊢<Q' =  ⊤∗-intro » ↪=>>-monoʳ-∗ λ{ .! → ∗-elimʳ » Q⊢<Q' .! }

  -- Modify =>> proof

  --> ↪=>>-suc :  P˂ ↪[ i ]=>> Q˂  ⊢[ ι ]  P˂ ↪[ suc i ]=>> Q˂

  --> ↪=>>-frameˡ :  ¡ P ↪[ i ]=>> ¡ Q  ⊢[ ι ]  ¡ (R ∗ P) ↪[ i ]=>> ¡ (R ∗ Q)

  ↪=>>-frameʳ :  ¡ P ↪[ i ]=>> ¡ Q  ⊢[ ι ]  ¡ (P ∗ R) ↪[ i ]=>> ¡ (Q ∗ R)
  ↪=>>-frameʳ =  ↪=>>-frameˡ » ↪=>>-monoˡ (¡ ∗-comm) » ↪=>>-monoʳ (¡ ∗-comm)

  -- Make ↪=>> out of ○

  -->  ○⇒∀₁↪=>> :  (∀ x →  R˂ .! ∗ P˂˙ x .! ⊢[< ι ][ i ]=>> Q˂˙ x .!) →
  -->              ○ R˂  ⊢[ ι ]  ∀₁ x , (P˂˙ x ↪[ i ]=>> Q˂˙ x)

  ○⇒∀₀↪=>> :  (∀ x →  R˂ .! ∗ P˂˙ x .! ⊢[< ι ][ i ]=>> Q˂˙ x .!) →
              ○ R˂  ⊢[ ι ]  ∀₀ x , (P˂˙ x ↪[ i ]=>> Q˂˙ x)
  ○⇒∀₀↪=>> =  ○⇒∀₁↪=>> ∘ _∘ ↓_

  ○⇒↪=>> :  R˂ .! ∗ P˂ .! ⊢[< ι ][ i ]=>> Q˂ .! →
            ○ R˂  ⊢[ ι ]  P˂ ↪[ i ]=>> Q˂
  ○⇒↪=>> =  (_» ∀₁-elim 0⊤) ∘ ○⇒∀₁↪=>> ∘ const
