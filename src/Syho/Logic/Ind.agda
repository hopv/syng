--------------------------------------------------------------------------------
-- Proof rules on ○
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Ind where

open import Base.Size using (Size; ∞)
open import Base.Thunk using (!)
open import Base.List using ([_])
open import Base.List.All using ([]ᴬ-it; ∷ᴬ-it)
open import Syho.Logic.Prop using (Prop'; Prop˂; _∧_; _→'_; _∗_; □_; ○_; Basic;
  ⊤-Basic)
open import Syho.Logic.Core using (_⊢[_]_; _⊢[<_]_; Pers; ⊢-refl; _»_; ∧-elimˡ;
  ∧-elimʳ; ∧⊤-intro; ⊤∧-intro; →-mono; →-const; ∗⇒∧; Basic-Pers; Persˡ-∧⇒∗)
open import Syho.Logic.Supd using (|=>>_; _⊢[_]=>>_; _ᵘ»_)

-- Import and re-export
open import Syho.Logic.Judg public using (○-mono-∧; ○-alloc; □○-alloc-mutrec;
  ○-use)

private variable
  ι :  Size
  P˂ Q˂ :  Prop˂ ∞
  R :  Prop' ∞

abstract

  -- Monotonicity

  ○-mono-∗ :  {{Basic R}} →  R ∗ P˂ .! ⊢[< ι ] Q˂ .! →  R ∗ ○ P˂ ⊢[ ι ] ○ Q˂
  ○-mono-∗ R∗P⊢<Q =  let instance _ = Basic-Pers in
    ∗⇒∧ » ○-mono-∧ λ{ .! → Persˡ-∧⇒∗ » R∗P⊢<Q .! }

  ○-mono :  P˂ .! ⊢[< ι ] Q˂ .! →  ○ P˂ ⊢[ ι ] ○ Q˂
  ○-mono P⊢<Q =  ⊤∧-intro » ○-mono-∧ λ{ .! → ∧-elimʳ » P⊢<Q .! }

  -- Allocation

  □○-alloc-rec :  {{Pers (P˂ .!)}} →  □ ○ P˂ →' P˂ .! ⊢[ ι ]=>> □ ○ P˂
  □○-alloc-rec =  →-mono ∧-elimˡ ∧⊤-intro » □○-alloc-mutrec ᵘ» ∧-elimˡ

  □○-alloc :  {{Pers (P˂ .!)}} →  P˂ .! ⊢[ ι ]=>> □ ○ P˂
  □○-alloc =  →-const » □○-alloc-rec
