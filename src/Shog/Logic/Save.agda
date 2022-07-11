--------------------------------------------------------------------------------
-- Proof rules on the exclusive/persistent save token
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Logic.Save (ℓ : Level) where

open import Base.Size using (Size; ∞)
open import Base.Thunk using (!)
open import Base.Func using (it)
open import Base.List using ([_])
open import Shog.Logic.Prop ℓ using (Prop'; Prop˂; _∧_; _∗_; □_; saveˣ; save□;
  Basic; ⊤-Basic)
open import Shog.Logic.Judg ℓ using (_⊢[_]_; _⊢[<_]_; _⊢[_]=>>_; Pers; Pers-⇒□)
open import Shog.Logic.Core ℓ using (⊢-refl; _»_; ∧-elimʳ; ⊤∧-intro; ∗⇒∧;
  ∗-monoʳ; ∗-elimˡ; ∗⊤-intro; -∗-const; Basic-Pers; Persˡ-∧⇒∗)
open import Shog.Logic.Supd ℓ using (_ᵘ»_)

-- Import and re-export the axiomatic rules
open import Shog.Logic.Judg.All ℓ public using (save□-□; saveˣ-mono-∧;
  save□-mono-∧; saveˣ-alloc; save□-alloc-rec; saveˣ-use; save□-use)

private variable
  ι :  Size
  P˂ Q˂ :  Prop˂ ∞
  R :  Prop' ∞

abstract

  instance
    -- save□ P˂ is persistent
    save□-Pers :  Pers (save□ P˂)
    save□-Pers .Pers-⇒□ =  save□-□

  -- Variants of saveˣ/□-mono-∧

  saveˣ-mono-∗ :  {{Basic R}} →
    R ∗ P˂ .! ⊢[< ι ] Q˂ .! →  R ∗ saveˣ P˂ ⊢[ ι ] saveˣ Q˂
  saveˣ-mono-∗ {R = R} R∗P⊢<Q =
    let instance _ = Basic-Pers in
    ∗⇒∧ » saveˣ-mono-∧ λ{ .! → Persˡ-∧⇒∗ » R∗P⊢<Q .! }

  save□-mono-∗ :  {{Basic R}} →
    R ∗ P˂ .! ⊢[< ι ] Q˂ .! →  R ∗ save□ P˂ ⊢[ ι ] save□ Q˂
  save□-mono-∗ {R = R} R∗P⊢<Q =
    let instance _ = Basic-Pers in
    ∗⇒∧ » save□-mono-∧ λ{ .! → Persˡ-∧⇒∗ » R∗P⊢<Q .! }

  saveˣ-mono :  P˂ .! ⊢[< ι ] Q˂ .! →  saveˣ P˂ ⊢[ ι ] saveˣ Q˂
  saveˣ-mono P⊢<Q =  ⊤∧-intro » saveˣ-mono-∧ λ{ .! → ∧-elimʳ » P⊢<Q .! }

  save□-mono :  P˂ .! ⊢[< ι ] Q˂ .! →  save□ P˂ ⊢[ ι ] save□ Q˂
  save□-mono P⊢<Q =  ⊤∧-intro » save□-mono-∧ λ{ .! → ∧-elimʳ » P⊢<Q .! }

  -- Allocating save□, without recursion

  save□-alloc :  □ P˂ .! ⊢[ ι ]=>> save□ P˂
  save□-alloc =  ∗⊤-intro » -∗-const » save□-alloc-rec {P˂s = [ _ ]} ᵘ» ∗-elimˡ
