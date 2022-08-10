--------------------------------------------------------------------------------
-- Proof rules on ○ and ↪=>>
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Ind where

open import Base.Level using (Level; ↓_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk; !)
open import Base.Few using (0⊤)
open import Base.Func using (_∘_; const)
open import Base.Prod using (_×_; _,_)
open import Base.Nat using (ℕ)
open import Base.List using ([_])
open import Base.List.All using ()
open import Syho.Logic.Prop using (Prop'; Prop˂; ∀₀-syntax; _∧_; _→'_; _∗_; □_;
  ○_; _↪[_]=>>_; Basic; ⊤-Basic)
open import Syho.Logic.Core using (_⊢[_]_; _⊢[<_]_; Pers; ⊢-refl; _»_; ∀₁-elim;
  ∧-elimˡ; ∧-elimʳ; ∧⊤-intro; ⊤∧-intro; →-mono; →-const; ∗⇒∧; Basic-Pers;
  Persˡ-∧⇒∗)
open import Syho.Logic.Supd using ([_]=>>_; _⊢[_][_]=>>_; _ᵘ»_)

-- Import and re-export
open import Syho.Logic.Judg public using (○-mono-∧; ○-alloc; □○-alloc-mutrec;
  ○-use; ↪=>>-monoˡ-∧; ↪=>>-monoʳ-∧; ∀₁↪=>>-alloc; ∀₁□↪=>>-alloc;
  ↪=>>-alloc-use)

private variable
  ℓ :  Level
  ι :  Size
  i j :  ℕ
  P˂ P'˂ Q˂ Q'˂ :  Prop˂ ∞
  X :  Set ℓ
  x :  X
  P˂˙ Q˂˙ :  X → Prop˂ ∞
  R :  Prop' ∞

abstract

  ------------------------------------------------------------------------------
  -- On ○

  -->  ○-use :  ○ P˂ ⊢[ ι ][ i ]=>> P˂ .!

  -- Monotonicity

  -->  ○-mono-∧ :  {{Basic R}} →  R ∧ P˂ .! ⊢[< ι ] Q˂ .! →
  -->              R ∧ ○ P˂ ⊢[ ι ] ○ Q˂

  ○-mono-∗ :  {{Basic R}} →  R ∗ P˂ .! ⊢[< ι ] Q˂ .! →  R ∗ ○ P˂ ⊢[ ι ] ○ Q˂
  ○-mono-∗ R∗P⊢<Q =  let instance _ = Basic-Pers in
    ∗⇒∧ » ○-mono-∧ λ{ .! → Persˡ-∧⇒∗ » R∗P⊢<Q .! }

  ○-mono :  P˂ .! ⊢[< ι ] Q˂ .! →  ○ P˂ ⊢[ ι ] ○ Q˂
  ○-mono P⊢<Q =  ⊤∧-intro » ○-mono-∧ λ{ .! → ∧-elimʳ » P⊢<Q .! }

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

  -->  ↪=>>-alloc-use :  (P˂ ↪[ i ]=>> Q˂) ∗ P˂ .!  ⊢[ ι ][ suc i ]=>>  Q˂ .!

  -- Monotonicity of ↪=>>

  -->  ↪=>>-monoˡ-∧ :  {{Basic R}} →  (R ∧ P'˂ .! ⊢[< ι ] P˂ .!) →
  -->                  R ∧ (P˂ ↪[ i ]=>> Q˂)  ⊢[ ι ]  P'˂ ↪[ i ]=>> Q˂

  -->  ↪=>>-monoʳ-∧ :  {{Basic R}} →  (R ∧ Q˂ .! ⊢[< ι ] Q'˂ .!) →
  -->                  R ∧ (P˂ ↪[ i ]=>> Q˂)  ⊢[ ι ]  P˂ ↪[ i ]=>> Q'˂

  -- We don't have ↪=>>-mono rules (which modify both the P and Q sides),
  -- because handling two thunks doesn't work well on the current Agda

  ↪=>>-monoˡ-∗ :  {{Basic R}} →  R ∗ P'˂ .! ⊢[< ι ] P˂ .! →
                  R ∗ (P˂ ↪[ i ]=>> Q˂)  ⊢[ ι ]  P'˂ ↪[ i ]=>> Q˂
  ↪=>>-monoˡ-∗ R∗P'⊢<P =  let instance _ = Basic-Pers in
    ∗⇒∧ » ↪=>>-monoˡ-∧ λ{ .! → Persˡ-∧⇒∗ » R∗P'⊢<P .! }

  ↪=>>-monoʳ-∗ :  {{Basic R}} →  R ∗ Q˂ .! ⊢[< ι ] Q'˂ .! →
                  R ∗ (P˂ ↪[ i ]=>> Q˂)  ⊢[ ι ]  P˂ ↪[ i ]=>> Q'˂
  ↪=>>-monoʳ-∗ R∗Q⊢<Q' =  let instance _ = Basic-Pers in
    ∗⇒∧ » ↪=>>-monoʳ-∧ λ{ .! → Persˡ-∧⇒∗ » R∗Q⊢<Q' .! }

  ↪=>>-monoˡ :  P'˂ .! ⊢[< ι ] P˂ .! →
                P˂ ↪[ i ]=>> Q˂  ⊢[ ι ]  P'˂ ↪[ i ]=>> Q˂
  ↪=>>-monoˡ P'⊢<P =  ⊤∧-intro » ↪=>>-monoˡ-∧ λ{ .! → ∧-elimʳ » P'⊢<P .! }

  ↪=>>-monoʳ :  Q˂ .! ⊢[< ι ] Q'˂ .! →
                P˂ ↪[ i ]=>> Q˂  ⊢[ ι ]  P˂ ↪[ i ]=>> Q'˂
  ↪=>>-monoʳ Q⊢<Q' =  ⊤∧-intro » ↪=>>-monoʳ-∧ λ{ .! → ∧-elimʳ » Q⊢<Q' .! }

  -- Allocate ↪=>>

  -->  ∀₁↪=>>-alloc :  (∀ x →  R ∗ P˂˙ x .! ⊢[ ι ][ i ]=>> Q˂˙ x .!) →
  -->                  R  ⊢[ ι ][ j ]=>>  ∀₁ x , (P˂˙ x ↪[ i ]=>> Q˂˙ x)

  ∀₀↪=>>-alloc :  (∀ x →  R ∗ P˂˙ x .! ⊢[ ι ][ i ]=>> Q˂˙ x .!) →
                  R  ⊢[ ι ][ j ]=>>  ∀₀ x , (P˂˙ x ↪[ i ]=>> Q˂˙ x)
  ∀₀↪=>>-alloc =  ∀₁↪=>>-alloc ∘ (_∘ ↓_)

  ↪=>>-alloc :  R ∗ P˂ .! ⊢[ ι ][ i ]=>> Q˂ .! →
                R  ⊢[ ι ][ j ]=>>  (P˂ ↪[ i ]=>> Q˂)
  ↪=>>-alloc =  (_ᵘ» ∀₁-elim 0⊤) ∘ ∀₁↪=>>-alloc ∘ const

  -->  ∀₁□↪=>>-alloc :  {{Pers R}} →
  -->                   (∀ x →  R ∗ P˂˙ x .! ⊢[ ι ][ i ]=>> Q˂˙ x .!) →
  -->                   R  ⊢[ ι ][ j ]=>>  ∀₁ x , □ (P˂˙ x ↪[ i ]=>> Q˂˙ x)

  ∀₀□↪=>>-alloc :  {{Pers R}} →  (∀ x →  R ∗ P˂˙ x .! ⊢[ ι ][ i ]=>> Q˂˙ x .!) →
                   R  ⊢[ ι ][ j ]=>>  ∀₀ x , □ (P˂˙ x ↪[ i ]=>> Q˂˙ x)
  ∀₀□↪=>>-alloc =  ∀₁□↪=>>-alloc ∘ (_∘ ↓_)

  □↪=>>-alloc :  {{Pers R}} →  R ∗ P˂ .! ⊢[ ι ][ i ]=>> Q˂ .! →
                 R  ⊢[ ι ][ j ]=>>  □ (P˂ ↪[ i ]=>> Q˂)
  □↪=>>-alloc =  (_ᵘ» ∀₁-elim 0⊤) ∘ ∀₁□↪=>>-alloc ∘ const
