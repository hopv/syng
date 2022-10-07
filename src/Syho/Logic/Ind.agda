--------------------------------------------------------------------------------
-- Proof rules on the indirection modality and the precursors
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Ind where

open import Base.Func using (_∘_; id; const; _$_)
open import Base.Size using (Size; Thunk; ¡_; !; _$ᵀʰ_)
open import Base.Nat using (ℕ; _≤ᵈ_; ≤ᵈ-refl; ≤ᵈṡ; _≤_; ≤⇒≤ᵈ)
open import Syho.Lang.Expr using (Type; Expr∞)
open import Syho.Lang.Ktxred using (Redex)
open import Syho.Logic.Prop using (WpKind; Prop∞; Prop˂∞; ∀-syntax; _∗_; _-∗_;
  □_; ○_; _↪[_]⇛_; _↪[_]ᵃ⟨_⟩_; _↪⟨_⟩[_]_; _↪⟨_⟩ᴾ_; _↪⟨_⟩ᵀ[_]_; [⊤]ᴺ; Basic)
open import Syho.Logic.Core using (_⊢[_]_; _⊢[<_]_; Pers; ⊢-refl; _»_; ∗-monoˡ;
  ∗-comm; ∗-elimʳ; ⊤∗-intro; -∗-elim; -∗-const)
open import Syho.Logic.Supd using ([_]⇛_; _⊢[_][_]⇛_; _⊢[<_][_]⇛_; _⊢[<_][_]⇛ᴺ_;
  ⊢⇒⊢⇛; _ᵘ»_; ⇛⇒⇛ᴺ)

-- Import and re-export
open import Syho.Logic.Judg public using (○-mono; ○-eatˡ; ○-alloc; □○-alloc-rec;
  ○-use; ↪⇛-ṡ; ↪⇛-eatˡ⁻ˡᵘ; ↪⇛-eatˡ⁻ʳ; ↪⇛-monoʳᵘ; ↪⇛-frameˡ; ○⇒↪⇛; ↪⇛-use;
  ↪ᵃ⟨⟩-ṡ; ↪ᵃ⟨⟩-eatˡ⁻ˡᵘ; ↪ᵃ⟨⟩-eatˡ⁻ʳ; ↪ᵃ⟨⟩-monoʳᵘ; ↪ᵃ⟨⟩-frameˡ; ○⇒↪ᵃ⟨⟩; ↪ᵃ⟨⟩-use;
  ↪⟨⟩ᵀ⇒↪⟨⟩ᴾ; ↪⟨⟩ᵀ-ṡ; ↪⟨⟩-eatˡ⁻ˡᵘᴺ; ↪⟨⟩-eatˡ⁻ʳ; ↪⟨⟩-monoʳᵘᴺ; ↪⟨⟩-frameˡ; ○⇒↪⟨⟩;
  ↪⟨⟩ᴾ-use; ↪⟨⟩ᵀ-use)

private variable
  ι :  Size
  i j :  ℕ
  T :  Type
  P Q R :  Prop∞
  P˂ P'˂ Q˂ Q'˂ R˂ :  Prop˂∞
  X Y :  Set₀
  x :  X
  Q˙ :  X → Prop∞
  P˂˙ Q˂˙ Q'˂˙ :  X → Prop˂∞
  Q˂˙˙ :  X → Y → Prop˂∞
  κ :  WpKind
  red :  Redex T
  e :  Expr∞ T

abstract

  ------------------------------------------------------------------------------
  -- On ○

  -->  ○-mono :  P˂ .! ⊢[< ι ] Q˂ .! →  ○ P˂ ⊢[ ι ] ○ Q˂

  -->  ○-use :  ○ P˂ ⊢[ ι ][ i ]⇛ P˂ .!

  -- ○ can eat a basic proposition

  -->  ○-eatˡ :  {{Basic Q}} →  Q ∗ ○ P˂ ⊢[ ι ] ○ ¡ (Q ∗ P˂ .!)

  ○-eatʳ :  {{Basic Q}} →  ○ P˂ ∗ Q ⊢[ ι ] ○ ¡ (P˂ .! ∗ Q)
  ○-eatʳ =  ∗-comm » ○-eatˡ » ○-mono λ{ .! → ∗-comm }

  -- Get ○

  -->  ○-alloc :  P˂ .! ⊢[ ι ][ i ]⇛ ○ P˂

  -->  □○-alloc-rec :  □ ○ P˂ -∗ □ P˂ .! ⊢[ ι ][ i ]⇛ □ ○ P˂

  □○-alloc :  □ P˂ .! ⊢[ ι ][ i ]⇛ □ ○ P˂
  □○-alloc =  -∗-const » □○-alloc-rec

  ------------------------------------------------------------------------------
  -- On ↪⇛

  -->  ○⇒↪⇛ :  P˂ .!  ∗  R˂ .! ⊢[< ι ][ i ]⇛  Q˂ .!  →
  -->          ○ R˂  ⊢[ ι ]  P˂ ↪[ i ]⇛ Q˂

  -->  ↪⇛-use :  P˂ .!  ∗  (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ][ ṡ i ]⇛  Q˂ .!

  -- Modify ⇛ proof

  -->  ↪⇛-ṡ :  P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P˂ ↪[ ṡ i ]⇛ Q˂

  ↪⇛-≤ᵈ :  i ≤ᵈ j →  P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P˂ ↪[ j ]⇛ Q˂
  ↪⇛-≤ᵈ ≤ᵈ-refl =  ⊢-refl
  ↪⇛-≤ᵈ (≤ᵈṡ i≤ᵈj') =  ↪⇛-≤ᵈ i≤ᵈj' » ↪⇛-ṡ

  ↪⇛-≤ :  i ≤ j →  P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P˂ ↪[ j ]⇛ Q˂
  ↪⇛-≤ =  ↪⇛-≤ᵈ ∘ ≤⇒≤ᵈ

  -->  ↪⇛-eatˡ⁻ˡᵘ :  {{Basic R}} →   R  ∗  P'˂ .!  ⊢[< ι ][ i ]⇛  P˂ .! →
  -->                R  ∗  (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ]  P'˂ ↪[ i ]⇛ Q˂

  ↪⇛-monoˡᵘ :  P'˂ .! ⊢[< ι ][ i ]⇛ P˂ .! →
               P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P'˂ ↪[ i ]⇛ Q˂
  ↪⇛-monoˡᵘ P'⊢⇛P =  ⊤∗-intro » ↪⇛-eatˡ⁻ˡᵘ $ (∗-elimʳ »_) $ᵀʰ P'⊢⇛P

  ↪⇛-eatˡ⁻ˡ :  {{Basic R}} →
    R ∗ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ]  ¡ (R -∗ P˂ .!) ↪[ i ]⇛ Q˂
  ↪⇛-eatˡ⁻ˡ =  ↪⇛-eatˡ⁻ˡᵘ λ{ .! → ⊢⇒⊢⇛ $ -∗-elim ⊢-refl }

  ↪⇛-monoˡ :  P'˂ .! ⊢[< ι ] P˂ .! →
              P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P'˂ ↪[ i ]⇛ Q˂
  ↪⇛-monoˡ P'⊢P =  ↪⇛-monoˡᵘ $ ⊢⇒⊢⇛ $ᵀʰ P'⊢P

  -->  ↪⇛-eatˡ⁻ʳ :  {{Basic R}} →
  -->    R  ∗  (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ]  P˂ ↪[ i ]⇛ ¡ (R ∗ Q˂ .!)

  -->  ↪⇛-monoʳᵘ :  Q˂ .!  ⊢[< ι ][ i ]⇛  Q'˂ .! →
  -->               P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P˂ ↪[ i ]⇛ Q'˂

  ↪⇛-monoʳ :  Q˂ .! ⊢[< ι ] Q'˂ .! →
                P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P˂ ↪[ i ]⇛ Q'˂
  ↪⇛-monoʳ Q⊢Q' =  ↪⇛-monoʳᵘ $ ⊢⇒⊢⇛ $ᵀʰ Q⊢Q'

  -->  ↪⇛-frameˡ :  P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]
  -->                 ¡ (R ∗ P˂ .!) ↪[ i ]⇛ ¡ (R ∗ Q˂ .!)

  ↪⇛-frameʳ :  P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  ¡ (P˂ .! ∗ R) ↪[ i ]⇛ ¡ (Q˂ .! ∗ R)
  ↪⇛-frameʳ =  ↪⇛-frameˡ »
    ↪⇛-monoˡ (λ{ .! → ∗-comm }) » ↪⇛-monoʳ λ{ .! → ∗-comm }

  ------------------------------------------------------------------------------
  -- On ↪ᵃ⟨ ⟩

  -->  ○⇒↪ᵃ⟨⟩ :  (P˂ .!  ∗  R˂ .! ⊢[< ι ][ i ]ᵃ⟨ red ⟩ λ v →  Q˂˙ v .!)  →
  -->            ○ R˂  ⊢[ ι ]  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙

  -->  ↪ᵃ⟨⟩-use :  P˂ .!  ∗  (P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙)
  -->                ⊢[ ι ][ ṡ i ]ᵃ⟨ red ⟩ λ v →  Q˂˙ v .!

  -- Modify ⟨ ⟩ᵀ proof

  -->  ↪ᵃ⟨⟩-ṡ :  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ ṡ i ] Q˂˙

  ↪ᵃ⟨⟩-≤ᵈ :  i ≤ᵈ j →  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]  P˂ ↪[ j ]ᵃ⟨ red ⟩ Q˂˙
  ↪ᵃ⟨⟩-≤ᵈ ≤ᵈ-refl =  ⊢-refl
  ↪ᵃ⟨⟩-≤ᵈ (≤ᵈṡ i≤ᵈj') =  ↪ᵃ⟨⟩-≤ᵈ i≤ᵈj' » ↪ᵃ⟨⟩-ṡ

  ↪ᵃ⟨⟩-≤ :  i ≤ j →  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]  P˂ ↪[ j ]ᵃ⟨ red ⟩ Q˂˙
  ↪ᵃ⟨⟩-≤ =  ↪ᵃ⟨⟩-≤ᵈ ∘ ≤⇒≤ᵈ

  -->  ↪ᵃ⟨⟩-eatˡ⁻ˡᵘ :  {{Basic R}} →  R ∗ P'˂ .! ⊢[< ι ][ j ]⇛ P˂ .! →
  -->    R ∗ (P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙)  ⊢[ ι ]  P'˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙

  ↪ᵃ⟨⟩-monoˡᵘ :  P'˂ .! ⊢[< ι ][ j ]⇛ P˂ .! →
                 P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]  P'˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙
  ↪ᵃ⟨⟩-monoˡᵘ P'⊢⇛P =  ⊤∗-intro » ↪ᵃ⟨⟩-eatˡ⁻ˡᵘ $ (∗-elimʳ »_) $ᵀʰ P'⊢⇛P

  ↪ᵃ⟨⟩-eatˡ⁻ˡ :  {{Basic R}} →
    R ∗ (P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙)  ⊢[ ι ]  ¡ (R -∗ P˂ .!) ↪[ i ]ᵃ⟨ red ⟩ Q˂˙
  ↪ᵃ⟨⟩-eatˡ⁻ˡ =  ↪ᵃ⟨⟩-eatˡ⁻ˡᵘ {j = 0} λ{ .! → ⊢⇒⊢⇛ $ -∗-elim ⊢-refl }

  ↪ᵃ⟨⟩-monoˡ :  P'˂ .! ⊢[< ι ] P˂ .! →
                P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]  P'˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙
  ↪ᵃ⟨⟩-monoˡ P'⊢P =  ↪ᵃ⟨⟩-monoˡᵘ {j = 0} $ ⊢⇒⊢⇛ $ᵀʰ P'⊢P

  -->  ↪ᵃ⟨⟩-eatˡ⁻ʳ :  {{Basic R}} →
  -->    R  ∗  (P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙)  ⊢[ ι ]
  -->      P˂ ↪[ i ]ᵃ⟨ red ⟩ λ v → ¡ (R ∗ Q˂˙ v .!)

  -->  ↪ᵃ⟨⟩-monoʳᵘ :  (∀ v →  Q˂˙ v .!  ⊢[< ι ][ j ]⇛  Q'˂˙ v .!)  →
  -->                 P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q'˂˙

  ↪ᵃ⟨⟩-monoʳ :  (∀ v →  Q˂˙ v .!  ⊢[< ι ]  Q'˂˙ v .!)  →
                P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q'˂˙
  ↪ᵃ⟨⟩-monoʳ Qv⊢Q'v =  ↪ᵃ⟨⟩-monoʳᵘ {j = 0} λ v → ⊢⇒⊢⇛ $ᵀʰ Qv⊢Q'v v

  -->  ↪ᵃ⟨⟩-frameˡ :  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]
  -->                  ¡ (R ∗ P˂ .!) ↪[ i ]ᵃ⟨ red ⟩ λ v → ¡ (R ∗ Q˂˙ v .!)

  ↪ᵃ⟨⟩-frameʳ :  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]
                   ¡ (P˂ .! ∗ R) ↪[ i ]ᵃ⟨ red ⟩ λ v → ¡ (Q˂˙ v .! ∗ R)
  ↪ᵃ⟨⟩-frameʳ =  ↪ᵃ⟨⟩-frameˡ »
    ↪ᵃ⟨⟩-monoˡ (λ{ .! → ∗-comm }) » ↪ᵃ⟨⟩-monoʳ λ{ _ .! → ∗-comm }

  ------------------------------------------------------------------------------
  -- On ↪⟨ ⟩

  -->  ↪⟨⟩ᵀ⇒↪⟨⟩ᴾ :  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q˂˙

  -->  ○⇒↪⟨⟩ :  (P˂ .!  ∗  R˂ .!  ⊢[< ι ]⟨ e ⟩[ κ ] λ v →  Q˂˙ v .!)  →
  -->           ○ R˂  ⊢[ ι ]  P˂ ↪⟨ e ⟩[ κ ] Q˂˙

  -->  ↪⟨⟩ᴾ-use :  e ⇒ᴾ e'  →
  -->    P˂ .!  ∗  (P˂ ↪⟨ e' ⟩ᴾ Q˂˙)  ⊢[ ι ]⟨ e ⟩ᴾ λ v →  Q˂˙ v .!

  -->  ↪⟨⟩ᵀ-use :  P˂ .!  ∗  (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙)
  -->                ⊢[ ι ]⟨ ¡ e ⟩ᵀ[ ṡ i ] λ v →  Q˂˙ v .!

  -- Modify ⟨ ⟩ proof

  -->  ↪⟨⟩ᵀ-ṡ :  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ ṡ i ] Q˂˙

  ↪⟨⟩ᵀ-≤ᵈ :  i ≤ᵈ j →  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ j ] Q˂˙
  ↪⟨⟩ᵀ-≤ᵈ ≤ᵈ-refl =  ⊢-refl
  ↪⟨⟩ᵀ-≤ᵈ (≤ᵈṡ i≤ᵈj') =  ↪⟨⟩ᵀ-≤ᵈ i≤ᵈj' » ↪⟨⟩ᵀ-ṡ

  ↪⟨⟩ᵀ-≤ :  i ≤ j →  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ j ] Q˂˙
  ↪⟨⟩ᵀ-≤ =  ↪⟨⟩ᵀ-≤ᵈ ∘ ≤⇒≤ᵈ

  -->  ↪⟨⟩-eatˡ⁻ˡᵘᴺ :  {{Basic R}}  →   R  ∗  P'˂ .!  ⊢[< ι ][ i ]⇛ᴺ  P˂ .!  →
  -->                  R  ∗  (P˂ ↪⟨ e ⟩[ κ ] Q˂˙)  ⊢[ ι ]  P'˂ ↪⟨ e ⟩[ κ ] Q˂˙

  ↪⟨⟩-eatˡ⁻ˡᵘ :  {{Basic R}}  →   R  ∗  P'˂ .!  ⊢[< ι ][ i ]⇛  P˂ .!  →
                 R  ∗  (P˂ ↪⟨ e ⟩[ κ ] Q˂˙)  ⊢[ ι ]  P'˂ ↪⟨ e ⟩[ κ ] Q˂˙
  ↪⟨⟩-eatˡ⁻ˡᵘ R⊢⇛P' =  ↪⟨⟩-eatˡ⁻ˡᵘᴺ $ ⇛⇒⇛ᴺ $ᵀʰ R⊢⇛P'

  ↪⟨⟩-eatˡ⁻ˡ :  {{Basic R}} →
    R  ∗  (P˂ ↪⟨ e ⟩[ κ ] Q˂˙)  ⊢[ ι ]  ¡ (R -∗ P˂ .!) ↪⟨ e ⟩[ κ ] Q˂˙
  ↪⟨⟩-eatˡ⁻ˡ =  ↪⟨⟩-eatˡ⁻ˡᵘ {i = 0} λ{ .! → ⊢⇒⊢⇛ $ -∗-elim ⊢-refl }

  ↪⟨⟩-monoˡᵘᴺ :  P'˂ .!  ⊢[< ι ][ i ]⇛ᴺ  P˂ .!  →
                 P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ι ]  P'˂ ↪⟨ e ⟩[ κ ] Q˂˙
  ↪⟨⟩-monoˡᵘᴺ P'⊢⇛P =  ⊤∗-intro » ↪⟨⟩-eatˡ⁻ˡᵘᴺ $ (∗-monoˡ ∗-elimʳ »_) $ᵀʰ P'⊢⇛P

  ↪⟨⟩-monoˡᵘ :  P'˂ .!  ⊢[< ι ][ i ]⇛  P˂ .!  →
                P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ι ]  P'˂ ↪⟨ e ⟩[ κ ] Q˂˙
  ↪⟨⟩-monoˡᵘ P'⊢⇛P =  ↪⟨⟩-monoˡᵘᴺ $ ⇛⇒⇛ᴺ $ᵀʰ P'⊢⇛P

  ↪⟨⟩-monoˡ :  P'˂ .! ⊢[< ι ] P˂ .! →
               P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ι ]  P'˂ ↪⟨ e ⟩[ κ ] Q˂˙
  ↪⟨⟩-monoˡ P'⊢P =  ↪⟨⟩-monoˡᵘ {i = 0} $ ⊢⇒⊢⇛ $ᵀʰ P'⊢P

  -->  ↪⟨⟩-eatˡ⁻ʳ :  {{Basic R}} →
  -->    R  ∗  (P˂ ↪⟨ e ⟩[ κ ] Q˂˙)  ⊢[ ι ]
  -->      P˂ ↪⟨ e ⟩[ κ ] λ v → ¡ (R ∗ Q˂˙ v .!)

  -->  ↪⟨⟩-monoʳᵘᴺ :  (∀ v →  Q˂˙ v .!  ⊢[< ι ][ i ]⇛ᴺ  Q'˂˙ v .!)  →
  -->                 P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩[ κ ] Q'˂˙

  ↪⟨⟩-monoʳᵘ :  (∀ v →  Q˂˙ v .!  ⊢[< ι ][ i ]⇛  Q'˂˙ v .!)  →
                P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩[ κ ] Q'˂˙
  ↪⟨⟩-monoʳᵘ Qv⊢⇛Q'v =  ↪⟨⟩-monoʳᵘᴺ λ{ v .! → ⇛⇒⇛ᴺ $ Qv⊢⇛Q'v v .! }

  ↪⟨⟩-monoʳ :  (∀ v →  Q˂˙ v .!  ⊢[< ι ]  Q'˂˙ v .!)  →
               P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩[ κ ] Q'˂˙
  ↪⟨⟩-monoʳ Qv⊢Q'v =  ↪⟨⟩-monoʳᵘ {i = 0} λ v → ⊢⇒⊢⇛ $ᵀʰ Qv⊢Q'v v

  -->  ↪⟨⟩-frameˡ :  P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ι ]
  -->                  ¡ (R ∗ P˂ .!) ↪⟨ e ⟩[ κ ] λ v → ¡ (R ∗ Q˂˙ v .!)

  ↪⟨⟩-frameʳ :  P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ι ]
                  ¡ (P˂ .! ∗ R) ↪⟨ e ⟩[ κ ] λ v → ¡ (Q˂˙ v .! ∗ R)
  ↪⟨⟩-frameʳ =  ↪⟨⟩-frameˡ »
    ↪⟨⟩-monoˡ (λ{ .! → ∗-comm }) » ↪⟨⟩-monoʳ λ{ _ .! → ∗-comm }
