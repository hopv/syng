--------------------------------------------------------------------------------
-- General super update modality
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Base where

open import Base.Level using (Level; _⊔ᴸ_; 2ᴸ)
open import Base.Func using (_$_; _▷_; _∘_)
open import Base.Prod using (_×_; _,_)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; ∀ᵒ-syntax;
  _∗ᵒ_; _-∗ᵒ_; _⤇ᴱ_; ⊨⇒⊨✓; ∀ᵒ-Mono; ∀ᵒ-mono; ∗ᵒ-mono✓ˡ; -∗ᵒ-Mono; -∗ᵒ-monoʳ;
  ⤇ᴱ-mono✓)
open import Syho.Model.ERA.Glob using (Envᴳ)

private variable
  ł ł' ł'' :  Level
  X :  Set ł
  Pᵒ Qᵒ :  Propᵒ ł
  gsI :  (Envᴳ → X) × (X → Envᴳ → Envᴳ) × (X → Propᵒ ł)
  get get' :  Envᴳ → X
  set set' :  X → Envᴳ → Envᴳ
  Inv Inv' :  X → Propᵒ ł
--------------------------------------------------------------------------------
-- [ ]⇛ᵒ :  General super update modality

infix 8 [_]⇛ᵒ_
[_]⇛ᵒ_ :  ∀{X : Set ł} →  (Envᴳ → X) × (X → Envᴳ → Envᴳ) × (X → Propᵒ ł') →
  Propᵒ ł'' →  Propᵒ (2ᴸ ⊔ᴸ ł ⊔ᴸ ł' ⊔ᴸ ł'')
[ get , set , Inv ]⇛ᵒ Pᵒ =
  ∀ᵒ E , Inv (get E) -∗ᵒ E ⤇ᴱ λ x → set x E , Pᵒ ∗ᵒ Inv x

abstract

  -- Monoᵒ for ⇛ᵒ

  ⇛ᵒ-Mono :  Monoᵒ ([ gsI ]⇛ᵒ Pᵒ)
  ⇛ᵒ-Mono =  ∀ᵒ-Mono λ _ → -∗ᵒ-Mono

  -- Monotonicity of ⇛ᵒ

  ⇛ᵒ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  [ gsI ]⇛ᵒ Pᵒ ⊨ [ gsI ]⇛ᵒ Qᵒ
  ⇛ᵒ-mono✓ P⊨✓Q gsI⇛P E =  (-∗ᵒ-monoʳ $ ⤇ᴱ-mono✓ λ _ → ∗ᵒ-mono✓ˡ P⊨✓Q) $ gsI⇛P E

  ⇛ᵒ-mono :  Pᵒ ⊨ Qᵒ →  [ gsI ]⇛ᵒ Pᵒ ⊨ [ gsI ]⇛ᵒ Qᵒ
  ⇛ᵒ-mono =  ⇛ᵒ-mono✓ ∘ ⊨⇒⊨✓
