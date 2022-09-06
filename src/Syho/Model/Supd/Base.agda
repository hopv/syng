--------------------------------------------------------------------------------
-- General super update modality
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Base where

open import Base.Level using (Level; _⊔ᴸ_; 2ᴸ)
open import Base.Func using (_$_; _▷_; _∘_; _›_)
open import Base.Eq using (_≡_; refl; ◠_; subst₂; _≡˙_)
open import Base.Prod using (_×_; _,_)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; ∀ᵒ-syntax;
  _∗ᵒ_; _-∗ᵒ_; _⤇ᴱ_; ⊨⇒⊨✓; ∀ᵒ-Mono; ∀ᵒ-mono; ∀ᵒ-intro; ∗ᵒ-mono✓ˡ; ∗ᵒ-mono✓ʳ;
  ∗ᵒ-monoˡ; ∗ᵒ-monoʳ; ∗ᵒ-comm; ∗ᵒ-assocˡ; ∗ᵒ-assocʳ; -∗ᵒ-Mono; -∗ᵒ-monoʳ;
  -∗ᵒ-intro; -∗ᵒ-apply; ⤇ᴱ-Mono; ⤇ᴱ-mono✓; ⤇ᴱ-mono; ⤇ᴱ-respᴱ; ⤇ᴱ-param;
  ⤇ᴱ-intro; ⤇ᴱ-join; ⤇ᴱ-eatˡ; ⤇ᴱ-eatʳ)
open import Syho.Model.ERA.Glob using (Envᴳ)

private variable
  ł ł' ł'' :  Level
  X :  Set ł
  Pᵒ Qᵒ :  Propᵒ ł
  gsI :  (Envᴳ → X) × (X → Envᴳ → Envᴳ) × (X → Propᵒ ł)
  get get' :  Envᴳ → X
  set set' :  X → Envᴳ → Envᴳ
  Inv Inv' :  X → Propᵒ ł
  E :  Envᴳ
--------------------------------------------------------------------------------
-- [ ]⇛ᵍ :  General super update modality

-- Parametrized over the getter (get) and setter (set) on the environment and
-- the invariant predicate (Inv)

abstract

  infix 8 [_]⇛ᵍ_
  [_]⇛ᵍ_ :  ∀{X : Set ł} →  (Envᴳ → X) × (X → Envᴳ → Envᴳ) × (X → Propᵒ ł') →
                            Propᵒ ł'' →  Propᵒ (2ᴸ ⊔ᴸ ł ⊔ᴸ ł' ⊔ᴸ ł'')
  [ get , set , Inv ]⇛ᵍ Pᵒ =
    ∀ᵒ E , Inv (get E) -∗ᵒ E ⤇ᴱ λ x → set x E , Pᵒ ∗ᵒ Inv x

  -- Monoᵒ for ⇛ᵍ

  ⇛ᵍ-Mono :  Monoᵒ ([ gsI ]⇛ᵍ Pᵒ)
  ⇛ᵍ-Mono =  ∀ᵒ-Mono λ _ → -∗ᵒ-Mono

  -- Monotonicity of ⇛ᵍ

  ⇛ᵍ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  [ gsI ]⇛ᵍ Pᵒ ⊨ [ gsI ]⇛ᵍ Qᵒ
  ⇛ᵍ-mono✓ P⊨✓Q gsI⇛P E =  (-∗ᵒ-monoʳ $ ⤇ᴱ-mono✓ λ _ → ∗ᵒ-mono✓ˡ P⊨✓Q) $ gsI⇛P E

  ⇛ᵍ-mono :  Pᵒ ⊨ Qᵒ →  [ gsI ]⇛ᵍ Pᵒ ⊨ [ gsI ]⇛ᵍ Qᵒ
  ⇛ᵍ-mono =  ⇛ᵍ-mono✓ ∘ ⊨⇒⊨✓

  -- Utility for making ⇛ᵍ

  ⇛ᵍ-make :  (∀ E → Pᵒ ∗ᵒ Inv (get E) ⊨✓ E ⤇ᴱ λ x → set x E , Qᵒ ∗ᵒ Inv x) →
             Pᵒ ⊨ [ get , set , Inv ]⇛ᵍ Qᵒ
  ⇛ᵍ-make {Pᵒ = Pᵒ} Inv∗P⊨✓⤇Inv∗Q =
    ∀ᵒ-intro {Pᵒ = Pᵒ} λ _ → -∗ᵒ-intro λ ✓∙ → ∗ᵒ-comm › Inv∗P⊨✓⤇Inv∗Q _ ✓∙

  -- Apply ⇛ᵍ

  ⇛ᵍ-apply :  [ get , set , Inv ]⇛ᵍ Pᵒ ∗ᵒ Inv (get E) ⊨✓
                E ⤇ᴱ λ x → set x E , Pᵒ ∗ᵒ Inv x
  ⇛ᵍ-apply ✓∙ =  ∗ᵒ-monoˡ (_$ _) › ∗ᵒ-comm › -∗ᵒ-apply ⤇ᴱ-Mono ✓∙

  -- Introduce ⇛ᵍ

  ⇛ᵍ-intro :  (∀{E} → set (get E) E ≡˙ E) →  Pᵒ ⊨ [ get , set , Inv ]⇛ᵍ Pᵒ
  ⇛ᵍ-intro {Pᵒ = Pᵒ} setget≡ =  ⇛ᵍ-make λ _ _ →
    ⤇ᴱ-intro › ⤇ᴱ-respᴱ setget≡ › ⤇ᴱ-param

  -- Join ⇛ᵍs

  ⇛ᵍ-join :  (∀{E x} → get' (set x E) ≡ get' E) →
    [ get , set , Inv ]⇛ᵍ [ get' , set' , Inv' ]⇛ᵍ Pᵒ  ⊨
      [ (λ E → (get E , get' E)) , (λ (x , y) → set' y ∘ set x) ,
        (λ (x , y) → Inv x ∗ᵒ Inv' y) ]⇛ᵍ Pᵒ
  ⇛ᵍ-join {Inv' = Inv'} get'set≡get' =  ⇛ᵍ-make {Pᵒ = [ _ ]⇛ᵍ _} λ _ ✓∙ →
    ∗ᵒ-assocʳ › ∗ᵒ-mono✓ˡ ⇛ᵍ-apply ✓∙ › ⤇ᴱ-eatʳ › ⤇ᴱ-mono✓ (λ _ ✓∙ →
      ∗ᵒ-assocˡ › ∗ᵒ-monoʳ ∗ᵒ-comm › ∗ᵒ-assocʳ › ∗ᵒ-mono✓ˡ
        (λ ✓∙ → ∗ᵒ-monoʳ (subst₂ Inv' (◠ get'set≡get') refl) › ⇛ᵍ-apply ✓∙) ✓∙ ›
      ⤇ᴱ-eatʳ › ⤇ᴱ-mono λ _ → ∗ᵒ-assocˡ › ∗ᵒ-monoʳ ∗ᵒ-comm) › ⤇ᴱ-join

  -- Let ⇛ᵍ eat a proposition under ∗ᵒ

  ⇛ᵍ-eatˡ :  Pᵒ ∗ᵒ [ gsI ]⇛ᵍ Qᵒ  ⊨  [ gsI ]⇛ᵍ (Pᵒ ∗ᵒ Qᵒ)
  ⇛ᵍ-eatˡ =  ⇛ᵍ-make {Pᵒ = _ ∗ᵒ _} λ _ ✓∙ → ∗ᵒ-assocˡ › ∗ᵒ-mono✓ʳ ⇛ᵍ-apply ✓∙ ›
    ⤇ᴱ-eatˡ › ⤇ᴱ-mono λ _ → ∗ᵒ-assocʳ

  ⇛ᵍ-eatʳ :  [ gsI ]⇛ᵍ Pᵒ ∗ᵒ Qᵒ  ⊨  [ gsI ]⇛ᵍ (Pᵒ ∗ᵒ Qᵒ)
  ⇛ᵍ-eatʳ =  ∗ᵒ-comm › ⇛ᵍ-eatˡ › ⇛ᵍ-mono ∗ᵒ-comm
