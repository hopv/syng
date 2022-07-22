--------------------------------------------------------------------------------
-- Proof rules on the exclusive/persistent save token
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Shog.Logic.Save where

open import Base.Size using (Size; ∞)
open import Base.Thunk using (!)
open import Base.Func using (it)
open import Base.List using ([_])
open import Shog.Logic.Prop using (Prop'; Prop˂; _∧_; _∗_; □_; Saveˣ; Save□;
  Basic; ⊤-Basic)
open import Shog.Logic.Core using (_⊢[_]_; _⊢[<_]_; Pers; Pers-⇒□; ⊢-refl; _»_;
  ∧-elimʳ; ⊤∧-intro; ∗⇒∧; ∗-monoʳ; ∗-elimˡ; ∗⊤-intro; -∗-const; Basic-Pers;
  Persˡ-∧⇒∗)
open import Shog.Logic.Supd using (|=>>_; _⊢[_]=>>_; _ᵘ»_)

-- Import and re-export
open import Shog.Logic.Judg public using (Save□-□;
  Saveˣ-mono-∧; Save□-mono-∧; Saveˣ-alloc; Save□-alloc-rec; Saveˣ-use;
  Save□-use)

private variable
  ι :  Size
  P˂ Q˂ :  Prop˂ ∞
  R :  Prop' ∞

abstract

  instance
    -- Save□ P˂ is persistent
    Save□-Pers :  Pers (Save□ P˂)
    Save□-Pers .Pers-⇒□ =  Save□-□

  -- Variants of Saveˣ/□-mono-∧

  Saveˣ-mono-∗ :  {{Basic R}} →
    R ∗ P˂ .! ⊢[< ι ] Q˂ .! →  R ∗ Saveˣ P˂ ⊢[ ι ] Saveˣ Q˂
  Saveˣ-mono-∗ {R = R} R∗P⊢<Q =
    let instance _ = Basic-Pers in
    ∗⇒∧ » Saveˣ-mono-∧ λ{ .! → Persˡ-∧⇒∗ » R∗P⊢<Q .! }

  Save□-mono-∗ :  {{Basic R}} →
    R ∗ P˂ .! ⊢[< ι ] Q˂ .! →  R ∗ Save□ P˂ ⊢[ ι ] Save□ Q˂
  Save□-mono-∗ {R = R} R∗P⊢<Q =
    let instance _ = Basic-Pers in
    ∗⇒∧ » Save□-mono-∧ λ{ .! → Persˡ-∧⇒∗ » R∗P⊢<Q .! }

  Saveˣ-mono :  P˂ .! ⊢[< ι ] Q˂ .! →  Saveˣ P˂ ⊢[ ι ] Saveˣ Q˂
  Saveˣ-mono P⊢<Q =  ⊤∧-intro » Saveˣ-mono-∧ λ{ .! → ∧-elimʳ » P⊢<Q .! }

  Save□-mono :  P˂ .! ⊢[< ι ] Q˂ .! →  Save□ P˂ ⊢[ ι ] Save□ Q˂
  Save□-mono P⊢<Q =  ⊤∧-intro » Save□-mono-∧ λ{ .! → ∧-elimʳ » P⊢<Q .! }

  -- Allocating Save□, without recursion

  Save□-alloc :  □ P˂ .! ⊢[ ι ]=>> Save□ P˂
  Save□-alloc =  ∗⊤-intro » -∗-const » Save□-alloc-rec {P˂s = [ _ ]} ᵘ» ∗-elimˡ
