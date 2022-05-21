--------------------------------------------------------------------------------
-- Interpreting save tokens
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Model.Save (ℓ : Level) where

open import Base.Size using (∞)
open import Base.Func using (_$_)
open import Base.Nat using (ℕ)
open import Base.Level using (↓ˡ_)
open import Base.Prod using (_,_)
open import Shog.Logic.Prop ℓ using (Prop'; _∗_; Basic)
open import Shog.Logic.Judg ℓ using (_⊢[_]_)
open import Shog.Model.RA using (RA)
open import Shog.Model.RA.Glob ℓ using (Globᴿᴬ; injᴳ; Saveˣ; #ˣᴾ_; injᶠˢˣ;
  Save□; injᶠˢ□; agᴾ; injᴳ-cong; injᴳ-⌞⌟; injᶠˢ□-⌞⌟)
open RA Globᴿᴬ using (_≈_; ⌞_⌟; sym˜; _»˜_)
open import Shog.Model.Prop Globᴿᴬ using (Propᵒ; _⊨_; ∃^-syntax; _∧ᵒ_; ⌜_⌝^;
  □ᵒ_; own; own-⌞⌟-□')
open import Shog.Model.Basic ℓ using ([|_|]ᴮ; [||]ᴮ-⇒□)

private variable
  P :  Prop' ∞

--------------------------------------------------------------------------------
-- Interpreting exclusive save tokens

lineˢˣ :  ℕ →  Prop' ∞ →  Propᵒ
lineˢˣ i P =  own $ injᴳ 0 $ injᶠˢˣ i $ #ˣᴾ P

saveˣᵒ :  Prop' ∞ →  Propᵒ
saveˣᵒ P =  ∃^ P' , ∃^ B , ∃^ BaB , ∃^ i ,
  ⌜ B ∗ P ⊢[ ∞ ] P' ⌝^  ∧ᵒ  [| B |]ᴮ {{ BaB }}  ∧ᵒ  lineˢˣ (↓ˡ i) P

--------------------------------------------------------------------------------
-- Interpreting persistent save tokens

lineˢ□ :  ℕ →  Prop' ∞ →  Propᵒ
lineˢ□ i P =  own $ injᴳ 1 $ injᶠˢ□ i $ agᴾ P

save□ᵒ :  Prop' ∞ →  Propᵒ
save□ᵒ P =  ∃^ P' , ∃^ B , ∃^ BaB , ∃^ i ,
  ⌜ B ∗ P' ⊢[ ∞ ] P ⌝^  ∧ᵒ  [| B |]ᴮ {{ BaB }}  ∧ᵒ  lineˢ□ (↓ˡ i) P'

abstract

  save□ᵒ-□ :  save□ᵒ P ⊨ □ᵒ save□ᵒ P
  save□ᵒ-□ {✓a = ✓a} (_ , _ , BaB , i , B∗P'⊢P , Ba , line□iP'a) =
    _ , _ , _ , _ , B∗P'⊢P , [||]ᴮ-⇒□ {{BaB}} Ba ,
    own-⌞⌟-□' (injᴳ-⌞⌟ »˜ injᴳ-cong injᶠˢ□-⌞⌟) {✓a = ✓a} line□iP'a
