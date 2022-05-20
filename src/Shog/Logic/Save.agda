--------------------------------------------------------------------------------
-- Proof rules on the exclusive/persistent save token
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Logic.Save (ℓ : Level) where

open import Base.Size using (Size; ∞)
open import Base.Thunk using (!)
open import Base.Bool using (Bool; _≤ᴮ_; ff≤tt; ≤ᴮ-refl)
open import Base.List using ([_])
open import Shog.Logic.Prop ℓ using (Prop'; Prop<; □_; _∗_; Basic; saveˣ; save□)
open import Shog.Logic.Judg ℓ using (_⊢[_]_; _⊢[<_]_; _⊢[_]=>>_; Pers; ⇒□)
open import Shog.Logic.Core ℓ using (refl; _»_; ∗-monoʳ; ∗-elimˡ; ∗⊤-intro;
  -∗-const)
open import Shog.Logic.Supd ℓ using (_ᵘ»_)

-- Import and re-export the axiomatic rules
open import Shog.Logic.Judg.All ℓ public using (saveˣ-mono; save□-mono;
  save□-□; saveˣ-alloc; save□-alloc-rec)

private variable
  ι :  Size
  P^ Q^ :  Prop< ∞
  R :  Prop' ∞
  b b' :  Bool

abstract

  instance
    -- save□ P^ is persistent
    save□-Pers :  Pers (save□ P^)
    save□-Pers .⇒□ =  save□-□

  -- Allocating save□, without recursion

  save□-alloc :  □ P^ .! ⊢[ ι ]=>> save□ P^
  save□-alloc =  ∗⊤-intro » -∗-const » save□-alloc-rec {P^s = [ _ ]} ᵘ» ∗-elimˡ
