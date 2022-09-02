--------------------------------------------------------------------------------
-- Proof rules on ○, ↪⇛, ↪⟨ ⟩ᴾ, and ↪⟨ ⟩ᵀ
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Ind where

open import Base.Level using (Level; ↓_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk; ¡_; !)
open import Base.Func using (_∘_; id; const; _$_)
open import Base.Nat using (ℕ; _≤ᵈ_; ≤ᵈ-refl; ≤ᵈṡ; _≤_; ≤⇒≤ᵈ)
open import Syho.Lang.Expr using (Type; Expr; Val)
open import Syho.Logic.Prop using (Prop'; Prop˂; ∀₀-syntax; _∗_; _-∗_; □_; ○_;
  _↪[_]⇛_; _↪⟨_⟩ᴾ_; _↪⟨_⟩ᵀ[_]_; Basic)
open import Syho.Logic.Core using (_⊢[_]_; _⊢[<_]_; Pers; ⊢-refl; _»_; ∗-comm;
  ∗-elimʳ; ⊤∗-intro; -∗-elim; -∗-const)
open import Syho.Logic.Supd using ([_]⇛_; _⊢[_][_]⇛_; _⊢[<_][_]⇛_; ⊢⇒⊢⇛; _ᵘ»_)

-- Import and re-export
open import Syho.Logic.Judg public using (○-mono; ○-eatˡ; ○-alloc; □○-alloc-rec;
  ○-use; ↪⇛-ṡ; ↪⇛-eatˡ⁻ˡᵘ; ↪⇛-eatˡ⁻ʳ; ↪⇛-monoʳᵘ; ↪⇛-frameˡ; ○⇒↪⇛; ↪⇛-use;
  ↪⟨⟩ᴾ-eatˡ⁻ˡᵘ; ↪⟨⟩ᴾ-eatˡ⁻ʳ; ↪⟨⟩ᴾ-monoʳᵘ; ↪⟨⟩ᴾ-frameˡ; ○⇒↪⟨⟩ᴾ; ↪⟨⟩ᴾ-use;
  ↪⟨⟩ᵀ-ṡ; ↪⟨⟩ᵀ-eatˡ⁻ˡᵘ; ↪⟨⟩ᵀ-eatˡ⁻ʳ; ↪⟨⟩ᵀ-monoʳᵘ; ↪⟨⟩ᵀ-frameˡ; ○⇒↪⟨⟩ᵀ;
  ↪⟨⟩ᵀ-use)

private variable
  ł :  Level
  ι :  Size
  i j :  ℕ
  T :  Type
  P Q R :  Prop' ∞
  P˂ P'˂ Q˂ Q'˂ R˂ :  Prop˂ ∞
  X Y :  Set ł
  x :  X
  Q˙ :  X → Prop' ∞
  P˂˙ Q˂˙ Q'˂˙ :  X → Prop˂ ∞
  Q˂˙˙ :  X → Y → Prop˂ ∞
  e :  Expr ∞ T

abstract

  ------------------------------------------------------------------------------
  -- On ○

  -->  ○-mono :  P˂ .! ⊢[< ι ] Q˂ .! →  ○ P˂ ⊢[ ι ] ○ Q˂

  -->  ○-use :  ○ P˂ ⊢[ ι ][ i ]⇛ P˂ .!

  -- ○ can eat a basic proposition

  -->  ○-eatˡ :  {{Basic Q}} →  Q ∗ ○ P˂ ⊢[ ι ] ○ ¡ (Q ∗ P˂ .!)

  ○-eatʳ :  {{Basic Q}} →  ○ P˂ ∗ Q ⊢[ ι ] ○ ¡ (P˂ .! ∗ Q)
  ○-eatʳ =  ∗-comm » ○-eatˡ » ○-mono $ ¡ ∗-comm

  -- Allocate ○

  -->  ○-alloc :  P˂ .! ⊢[ ι ][ i ]⇛ ○ P˂

  -->  □○-alloc-rec :  □ ○ P˂ -∗ □ P˂ .! ⊢[ ι ][ i ]⇛ □ ○ P˂

  □○-alloc :  □ P˂ .! ⊢[ ι ][ i ]⇛ □ ○ P˂
  □○-alloc =  -∗-const » □○-alloc-rec

  ------------------------------------------------------------------------------
  -- On ↪⇛

  -->  ○⇒↪⇛ :  R˂ .! ∗ P˂ .! ⊢[< ι ][ i ]⇛ Q˂ .! →
  -->          ○ R˂  ⊢[ ι ]  P˂ ↪[ i ]⇛ Q˂

  -->  ↪⇛-use :  P˂ .! ∗ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ][ ṡ i ]⇛  Q˂ .!

  -- Modify ⇛ proof

  -->  ↪⇛-ṡ :  P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P˂ ↪[ ṡ i ]⇛ Q˂

  ↪⇛-≤ᵈ :  i ≤ᵈ j →  P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P˂ ↪[ j ]⇛ Q˂
  ↪⇛-≤ᵈ ≤ᵈ-refl =  ⊢-refl
  ↪⇛-≤ᵈ (≤ᵈṡ i≤ᵈj') =  ↪⇛-≤ᵈ i≤ᵈj' » ↪⇛-ṡ

  ↪⇛-≤ :  i ≤ j →  P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P˂ ↪[ j ]⇛ Q˂
  ↪⇛-≤ =  ↪⇛-≤ᵈ ∘ ≤⇒≤ᵈ

  -->  ↪⇛-eatˡ⁻ˡᵘ :  {{Basic R}} →  R ∗ P'˂ .! ⊢[< ι ][ i ]⇛ P˂ .! →
  -->                R ∗ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ]  P'˂ ↪[ i ]⇛ Q˂

  ↪⇛-monoˡᵘ :  P'˂ .! ⊢[< ι ][ i ]⇛ P˂ .! →
                 P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P'˂ ↪[ i ]⇛ Q˂
  ↪⇛-monoˡᵘ P'⊢⇛P =  ⊤∗-intro » ↪⇛-eatˡ⁻ˡᵘ λ{ .! → ∗-elimʳ » P'⊢⇛P .! }

  ↪⇛-eatˡ⁻ˡ :  {{Basic R}} →
    R ∗ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ]  ¡ (R -∗ P˂ .!) ↪[ i ]⇛ Q˂
  ↪⇛-eatˡ⁻ˡ =  ↪⇛-eatˡ⁻ˡᵘ λ{ .! → ⊢⇒⊢⇛ $ -∗-elim ⊢-refl }

  ↪⇛-monoˡ :  P'˂ .! ⊢[< ι ] P˂ .! →
              P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P'˂ ↪[ i ]⇛ Q˂
  ↪⇛-monoˡ ⊢< =  ↪⇛-monoˡᵘ λ{ .! → ⊢⇒⊢⇛ $ ⊢< .! }

  -->  ↪⇛-eatˡ⁻ʳ :  {{Basic R}} →
  -->    R ∗ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ]  P˂ ↪[ i ]⇛ ¡ (R ∗ Q˂ .!)

  -->  ↪⇛-monoʳᵘ :  Q˂ .! ⊢[< ι ][ i ]⇛ Q'˂ .! →
  -->               P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P˂ ↪[ i ]⇛ Q'˂

  ↪⇛-monoʳ :  Q˂ .! ⊢[< ι ] Q'˂ .! →
                P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P˂ ↪[ i ]⇛ Q'˂
  ↪⇛-monoʳ ⊢< =  ↪⇛-monoʳᵘ λ{ .! → ⊢⇒⊢⇛ $ ⊢< .! }

  -->  ↪⇛-frameˡ :  P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]
  -->                 ¡ (R ∗ P˂ .!) ↪[ i ]⇛ ¡ (R ∗ Q˂ .!)

  ↪⇛-frameʳ :  P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  ¡ (P˂ .! ∗ R) ↪[ i ]⇛ ¡ (Q˂ .! ∗ R)
  ↪⇛-frameʳ =  ↪⇛-frameˡ » ↪⇛-monoˡ (¡ ∗-comm) » ↪⇛-monoʳ (¡ ∗-comm)

  ------------------------------------------------------------------------------
  -- On ↪⟨ ⟩ᴾ

  -->  ○⇒↪⟨⟩ᴾ :  P˂ .! ∗ R˂ .! ⊢[< ι ]⟨ e ⟩ᴾ (λ v → Q˂˙ v .!) →
  -->            ○ R˂  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q˂˙

  -->  ↪⟨⟩ᴾ-use :  P˂ .! ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂˙)  ⊢[ ι ]⟨ ▶ ¡ e ⟩ᴾ  λ v → Q˂˙ v .!

  -- Modify ⟨ ⟩ᴾ proof

  -->  ↪⟨⟩ᴾ-eatˡ⁻ˡᵘ :  {{Basic R}} →  (R ∗ P'˂ .! ⊢[< ι ][ i ]⇛ P˂ .!) →
  -->                  R ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂˙)  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᴾ Q˂˙

  ↪⟨⟩ᴾ-monoˡᵘ :  P'˂ .! ⊢[< ι ][ i ]⇛ P˂ .! →
                 P˂ ↪⟨ e ⟩ᴾ Q˂˙  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᴾ Q˂˙
  ↪⟨⟩ᴾ-monoˡᵘ P'⊢⇛P =  ⊤∗-intro » ↪⟨⟩ᴾ-eatˡ⁻ˡᵘ λ{ .! → ∗-elimʳ » P'⊢⇛P .! }

  ↪⟨⟩ᴾ-eatˡ⁻ˡ :  {{Basic R}} →
    R ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂˙)  ⊢[ ι ]  ¡ (R -∗ P˂ .!) ↪⟨ e ⟩ᴾ Q˂˙
  ↪⟨⟩ᴾ-eatˡ⁻ˡ =  ↪⟨⟩ᴾ-eatˡ⁻ˡᵘ {i = 0} λ{ .! → ⊢⇒⊢⇛ $ -∗-elim ⊢-refl }

  ↪⟨⟩ᴾ-monoˡ :  P'˂ .! ⊢[< ι ] P˂ .! →
                P˂ ↪⟨ e ⟩ᴾ Q˂˙  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᴾ Q˂˙
  ↪⟨⟩ᴾ-monoˡ ⊢< =  ↪⟨⟩ᴾ-monoˡᵘ {i = 0} λ{ .! → ⊢⇒⊢⇛ $ ⊢< .! }

  -->  ↪⟨⟩ᴾ-eatˡ⁻ʳ :  {{Basic R}} →
  -->    R ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂˙)  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ λ v → ¡ (R ∗ Q˂˙ v .!)

  -->  ↪⟨⟩ᴾ-monoʳᵘ :  (∀ v →  Q˂˙ v .! ⊢[< ι ][ i ]⇛ Q'˂˙ v .!) →
  -->                 P˂ ↪⟨ e ⟩ᴾ Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q'˂˙

  ↪⟨⟩ᴾ-monoʳ :  (∀ v →  Q˂˙ v .! ⊢[< ι ] Q'˂˙ v .!) →
                P˂ ↪⟨ e ⟩ᴾ Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q'˂˙
  ↪⟨⟩ᴾ-monoʳ ⊢< =  ↪⟨⟩ᴾ-monoʳᵘ {i = 0} λ{ v .! → ⊢⇒⊢⇛ $ ⊢< v .! }

  -->  ↪⟨⟩ᴾ-frameˡ :  P˂ ↪⟨ e ⟩ᴾ Q˂˙  ⊢[ ι ]
  -->                   ¡ (R ∗ P˂ .!) ↪⟨ e ⟩ᴾ λ v → ¡ (R ∗ Q˂˙ v .!)

  ↪⟨⟩ᴾ-frameʳ :  P˂ ↪⟨ e ⟩ᴾ Q˂˙  ⊢[ ι ]
                   ¡ (P˂ .! ∗ R) ↪⟨ e ⟩ᴾ λ v → ¡ (Q˂˙ v .! ∗ R)
  ↪⟨⟩ᴾ-frameʳ =  ↪⟨⟩ᴾ-frameˡ »
    ↪⟨⟩ᴾ-monoˡ (¡ ∗-comm) » ↪⟨⟩ᴾ-monoʳ (λ _ → ¡ ∗-comm)

  ------------------------------------------------------------------------------
  -- On ↪⟨ ⟩ᵀ

  -->  ○⇒↪⟨⟩ᵀ :  P˂ .! ∗ R˂ .! ⊢[< ι ]⟨ e ⟩ᵀ[ i ] (λ v → Q˂˙ v .!) →
  -->            ○ R˂  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙

  -->  ↪⟨⟩ᵀ-use :  P˂ .! ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙)
  -->                ⊢[ ι ]⟨ ¡ e ⟩ᵀ[ ṡ i ]  λ v → Q˂˙ v .!

  -- Modify ⟨ ⟩ᵀ proof

  -->  ↪⟨⟩ᵀ-ṡ :  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ ṡ i ] Q˂˙

  ↪⟨⟩ᵀ-≤ᵈ :  i ≤ᵈ j →  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ j ] Q˂˙
  ↪⟨⟩ᵀ-≤ᵈ ≤ᵈ-refl =  ⊢-refl
  ↪⟨⟩ᵀ-≤ᵈ (≤ᵈṡ i≤ᵈj') =  ↪⟨⟩ᵀ-≤ᵈ i≤ᵈj' » ↪⟨⟩ᵀ-ṡ

  ↪⟨⟩ᵀ-≤ :  i ≤ j →  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ j ] Q˂˙
  ↪⟨⟩ᵀ-≤ =  ↪⟨⟩ᵀ-≤ᵈ ∘ ≤⇒≤ᵈ

  -->  ↪⟨⟩ᵀ-eatˡ⁻ˡᵘ :  {{Basic R}} →  (R ∗ P'˂ .! ⊢[< ι ][ j ]⇛ P˂ .!) →
  -->                  R ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙)  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙

  ↪⟨⟩ᵀ-monoˡᵘ :  P'˂ .! ⊢[< ι ][ j ]⇛ P˂ .! →
                 P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙
  ↪⟨⟩ᵀ-monoˡᵘ P'⊢⇛P =  ⊤∗-intro » ↪⟨⟩ᵀ-eatˡ⁻ˡᵘ λ{ .! → ∗-elimʳ » P'⊢⇛P .! }

  ↪⟨⟩ᵀ-eatˡ⁻ˡ :  {{Basic R}} →
    R ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙)  ⊢[ ι ]  ¡ (R -∗ P˂ .!) ↪⟨ e ⟩ᵀ[ i ] Q˂˙
  ↪⟨⟩ᵀ-eatˡ⁻ˡ =  ↪⟨⟩ᵀ-eatˡ⁻ˡᵘ {j = 0} λ{ .! → ⊢⇒⊢⇛ $ -∗-elim ⊢-refl }

  ↪⟨⟩ᵀ-monoˡ :  P'˂ .! ⊢[< ι ] P˂ .! →
                P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙
  ↪⟨⟩ᵀ-monoˡ ⊢< =  ↪⟨⟩ᵀ-monoˡᵘ {j = 0} λ{ .! → ⊢⇒⊢⇛ $ ⊢< .! }

  -->  ↪⟨⟩ᵀ-eatˡ⁻ʳ :  {{Basic R}} →  R ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙)  ⊢[ ι ]
  -->                 P˂ ↪⟨ e ⟩ᵀ[ i ] λ v → ¡ (R ∗ Q˂˙ v .!)

  -->  ↪⟨⟩ᵀ-monoʳᵘ :  (∀ v →  Q˂˙ v .! ⊢[< ι ][ j ]⇛ Q'˂˙ v .!) →
  -->                 P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q'˂˙

  ↪⟨⟩ᵀ-monoʳ :  (∀ v →  Q˂˙ v .! ⊢[< ι ] Q'˂˙ v .!) →
                P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q'˂˙
  ↪⟨⟩ᵀ-monoʳ ⊢< =  ↪⟨⟩ᵀ-monoʳᵘ {j = 0} λ{ v .! → ⊢⇒⊢⇛ $ ⊢< v .! }

  -->  ↪⟨⟩ᵀ-frameˡ :  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]
  -->                  ¡ (R ∗ P˂ .!) ↪⟨ e ⟩ᵀ[ i ] λ v → ¡ (R ∗ Q˂˙ v .!)

  ↪⟨⟩ᵀ-frameʳ :  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]
                   ¡ (P˂ .! ∗ R) ↪⟨ e ⟩ᵀ[ i ] λ v → ¡ (Q˂˙ v .! ∗ R)
  ↪⟨⟩ᵀ-frameʳ =  ↪⟨⟩ᵀ-frameˡ »
    ↪⟨⟩ᵀ-monoˡ (¡ ∗-comm) » ↪⟨⟩ᵀ-monoʳ (λ _ → ¡ ∗-comm)
