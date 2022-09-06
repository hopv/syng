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
  _∗ᵒ_; _-∗ᵒ_; _⤇ᴱ_; ⊨⇒⊨✓; ∀ᵒ-Mono; ∀ᵒ-mono; ∀ᵒ-intro; ∗ᵒ-mono✓ʳ; ∗ᵒ-monoˡ;
  ∗ᵒ-monoʳ; ∗ᵒ-comm; ∗ᵒ-assocˡ; ∗ᵒ-assocʳ; pullʳˡᵒ; -∗ᵒ-Mono; -∗ᵒ-monoʳ;
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

--------------------------------------------------------------------------------
-- [ ]⇛ᵒ :  General super update modality

-- Parametrized over the getter (get) and setter (set) on the environment and
-- the invariant predicate (Inv)

infix 8 [_]⇛ᵒ_
[_]⇛ᵒ_ :  ∀{X : Set ł} →  (Envᴳ → X) × (X → Envᴳ → Envᴳ) × (X → Propᵒ ł') →
                          Propᵒ ł'' →  Propᵒ (2ᴸ ⊔ᴸ ł ⊔ᴸ ł' ⊔ᴸ ł'')
[ get , set , Inv ]⇛ᵒ Pᵒ =
  ∀ᵒ E , Inv (get E) -∗ᵒ E ⤇ᴱ λ x → set x E , Inv x ∗ᵒ Pᵒ

abstract

  -- Monoᵒ for ⇛ᵒ

  ⇛ᵒ-Mono :  Monoᵒ ([ gsI ]⇛ᵒ Pᵒ)
  ⇛ᵒ-Mono =  ∀ᵒ-Mono λ _ → -∗ᵒ-Mono

  -- Monotonicity of ⇛ᵒ

  ⇛ᵒ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  [ gsI ]⇛ᵒ Pᵒ ⊨ [ gsI ]⇛ᵒ Qᵒ
  ⇛ᵒ-mono✓ P⊨✓Q gsI⇛P E =  (-∗ᵒ-monoʳ $ ⤇ᴱ-mono✓ λ _ → ∗ᵒ-mono✓ʳ P⊨✓Q) $ gsI⇛P E

  ⇛ᵒ-mono :  Pᵒ ⊨ Qᵒ →  [ gsI ]⇛ᵒ Pᵒ ⊨ [ gsI ]⇛ᵒ Qᵒ
  ⇛ᵒ-mono =  ⇛ᵒ-mono✓ ∘ ⊨⇒⊨✓

  -- Introduce ⇛ᵒ

  ⇛ᵒ-intro :  (∀{E} → set (get E) E ≡˙ E) →  Pᵒ ⊨ [ get , set , Inv ]⇛ᵒ Pᵒ
  ⇛ᵒ-intro {Pᵒ = Pᵒ} setget≡ =  ∀ᵒ-intro {Pᵒ = Pᵒ} λ _ → -∗ᵒ-intro λ _ →
    ⤇ᴱ-intro › ⤇ᴱ-respᴱ setget≡ › ⤇ᴱ-param

  -- Join ⇛ᵒs

  ⇛ᵒ-join :  (∀{E x} → get' (set x E) ≡ get' E) →
    [ get , set , Inv ]⇛ᵒ [ get' , set' , Inv' ]⇛ᵒ Pᵒ  ⊨
      [ (λ E → (get E , get' E)) , (λ (x , y) → set' y ∘ set x) ,
        (λ (x , y) → Inv x ∗ᵒ Inv' y) ]⇛ᵒ Pᵒ
  ⇛ᵒ-join {Inv' = Inv'} get'set≡get' =  ∀ᵒ-intro {Pᵒ = [ _ ]⇛ᵒ _} λ _ →
    -∗ᵒ-intro {Qᵒ = [ _ ]⇛ᵒ _} λ ✓∙ → ∗ᵒ-monoˡ ∗ᵒ-comm › ∗ᵒ-assocˡ ›
    ∗ᵒ-mono✓ʳ (λ ✓∙ → ∗ᵒ-monoʳ (_$ _) › -∗ᵒ-apply ⤇ᴱ-Mono ✓∙) ✓∙ › ⤇ᴱ-eatˡ ›
    ⤇ᴱ-mono✓ (λ x ✓∙ → pullʳˡᵒ ›
      ∗ᵒ-mono✓ʳ (λ ✓∙ → ∗ᵒ-monoˡ (subst₂ Inv' (◠ get'set≡get') refl) ›
        ∗ᵒ-monoʳ (_$ _) › -∗ᵒ-apply ⤇ᴱ-Mono ✓∙) ✓∙ ›
      ⤇ᴱ-eatˡ › ⤇ᴱ-mono λ _ → ∗ᵒ-assocʳ) ›
    ⤇ᴱ-join
