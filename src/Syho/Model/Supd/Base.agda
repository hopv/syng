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
-- [ ]⇛ᵒ :  General super update modality

-- Parametrized over the getter (get) and setter (set) on the environment and
-- the invariant predicate (Inv)

abstract

  infix 8 [_]⇛ᵒ_
  [_]⇛ᵒ_ :  ∀{X : Set ł} →  (Envᴳ → X) × (X → Envᴳ → Envᴳ) × (X → Propᵒ ł') →
                            Propᵒ ł'' →  Propᵒ (2ᴸ ⊔ᴸ ł ⊔ᴸ ł' ⊔ᴸ ł'')
  [ get , set , Inv ]⇛ᵒ Pᵒ =
    ∀ᵒ E , Inv (get E) -∗ᵒ E ⤇ᴱ λ x → set x E , Pᵒ ∗ᵒ Inv x

  -- Monoᵒ for ⇛ᵒ

  ⇛ᵒ-Mono :  Monoᵒ ([ gsI ]⇛ᵒ Pᵒ)
  ⇛ᵒ-Mono =  ∀ᵒ-Mono λ _ → -∗ᵒ-Mono

  -- Monotonicity of ⇛ᵒ

  ⇛ᵒ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  [ gsI ]⇛ᵒ Pᵒ ⊨ [ gsI ]⇛ᵒ Qᵒ
  ⇛ᵒ-mono✓ P⊨✓Q gsI⇛P E =  (-∗ᵒ-monoʳ $ ⤇ᴱ-mono✓ λ _ → ∗ᵒ-mono✓ˡ P⊨✓Q) $ gsI⇛P E

  ⇛ᵒ-mono :  Pᵒ ⊨ Qᵒ →  [ gsI ]⇛ᵒ Pᵒ ⊨ [ gsI ]⇛ᵒ Qᵒ
  ⇛ᵒ-mono =  ⇛ᵒ-mono✓ ∘ ⊨⇒⊨✓

  -- Utility for making ⇛ᵒ

  ⇛ᵒ-make :  (∀ E → Pᵒ ∗ᵒ Inv (get E) ⊨✓ E ⤇ᴱ λ x → set x E , Qᵒ ∗ᵒ Inv x) →
             Pᵒ ⊨ [ get , set , Inv ]⇛ᵒ Qᵒ
  ⇛ᵒ-make {Pᵒ = Pᵒ} Inv∗P⊨✓⤇Inv∗Q =
    ∀ᵒ-intro {Pᵒ = Pᵒ} λ _ → -∗ᵒ-intro λ ✓∙ → ∗ᵒ-comm › Inv∗P⊨✓⤇Inv∗Q _ ✓∙

  -- Apply ⇛ᵒ

  ⇛ᵒ-apply :  [ get , set , Inv ]⇛ᵒ Pᵒ ∗ᵒ Inv (get E) ⊨✓
                E ⤇ᴱ λ x → set x E , Pᵒ ∗ᵒ Inv x
  ⇛ᵒ-apply ✓∙ =  ∗ᵒ-monoˡ (_$ _) › ∗ᵒ-comm › -∗ᵒ-apply ⤇ᴱ-Mono ✓∙

  -- Introduce ⇛ᵒ

  ⇛ᵒ-intro :  (∀{E} → set (get E) E ≡˙ E) →  Pᵒ ⊨ [ get , set , Inv ]⇛ᵒ Pᵒ
  ⇛ᵒ-intro {Pᵒ = Pᵒ} setget≡ =  ⇛ᵒ-make λ _ _ →
    ⤇ᴱ-intro › ⤇ᴱ-respᴱ setget≡ › ⤇ᴱ-param

  -- Join ⇛ᵒs

  ⇛ᵒ-join :  (∀{E x} → get' (set x E) ≡ get' E) →
    [ get , set , Inv ]⇛ᵒ [ get' , set' , Inv' ]⇛ᵒ Pᵒ  ⊨
      [ (λ E → (get E , get' E)) , (λ (x , y) → set' y ∘ set x) ,
        (λ (x , y) → Inv x ∗ᵒ Inv' y) ]⇛ᵒ Pᵒ
  ⇛ᵒ-join {Inv' = Inv'} get'set≡get' =  ⇛ᵒ-make {Pᵒ = [ _ ]⇛ᵒ _} λ _ ✓∙ →
    ∗ᵒ-assocʳ › ∗ᵒ-mono✓ˡ ⇛ᵒ-apply ✓∙ › ⤇ᴱ-eatʳ › ⤇ᴱ-mono✓ (λ _ ✓∙ →
      ∗ᵒ-assocˡ › ∗ᵒ-monoʳ ∗ᵒ-comm › ∗ᵒ-assocʳ › ∗ᵒ-mono✓ˡ
        (λ ✓∙ → ∗ᵒ-monoʳ (subst₂ Inv' (◠ get'set≡get') refl) › ⇛ᵒ-apply ✓∙) ✓∙ ›
      ⤇ᴱ-eatʳ › ⤇ᴱ-mono λ _ → ∗ᵒ-assocˡ › ∗ᵒ-monoʳ ∗ᵒ-comm) › ⤇ᴱ-join

  -- Let ⇛ᵒ eat a proposition under ∗ᵒ

  ⇛ᵒ-eatˡ :  Pᵒ ∗ᵒ [ gsI ]⇛ᵒ Qᵒ  ⊨  [ gsI ]⇛ᵒ (Pᵒ ∗ᵒ Qᵒ)
  ⇛ᵒ-eatˡ =  ⇛ᵒ-make {Pᵒ = _ ∗ᵒ _} λ _ ✓∙ → ∗ᵒ-assocˡ › ∗ᵒ-mono✓ʳ ⇛ᵒ-apply ✓∙ ›
    ⤇ᴱ-eatˡ › ⤇ᴱ-mono λ _ → ∗ᵒ-assocʳ

  ⇛ᵒ-eatʳ :  [ gsI ]⇛ᵒ Pᵒ ∗ᵒ Qᵒ  ⊨  [ gsI ]⇛ᵒ (Pᵒ ∗ᵒ Qᵒ)
  ⇛ᵒ-eatʳ =  ∗ᵒ-comm › ⇛ᵒ-eatˡ › ⇛ᵒ-mono ∗ᵒ-comm
