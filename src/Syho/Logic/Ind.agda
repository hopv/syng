--------------------------------------------------------------------------------
-- Proof rules on the indirection modality and the precursors
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Ind where

open import Base.Func using (_$_; _∘_; id; const)
open import Base.Size using (Size; Thunk; ¡_; !; _$ᵀʰ_)
open import Base.Nat using (ℕ)
open import Syho.Lang.Expr using (Type; Expr∞)
open import Syho.Lang.Ktxred using (Redex)
open import Syho.Logic.Prop using (WpKind; Prop∞; Prop˂∞; ¡ᴾ_; ∀-syntax; _∗_;
  _-∗_; □_; ○_; _↪[_]⇛_; _↪[_]ᵃ⟨_⟩_; _↪⟨_⟩[_]_; _↪⟨_⟩ᴾ_; _↪⟨_⟩ᵀ[_]_; _↪[_]⟨_⟩∞;
  Basic)
open import Syho.Logic.Core using (_⊢[_]_; _⊢[<_]_; Pers; ⇒<; ⊢-refl; _»_;
  ∗-comm; ∗-elimʳ; ⊤∗-intro; -∗-elimˡ; -∗-const)
open import Syho.Logic.Supd using ([_]⇛_; _⊢[_][_]⇛_; _⊢[<_][_]⇛_; _⊢[<_][_]⇛ᴺ_;
  ⇒⇛; _ᵘ»_; _»ᵘᴺ_; ⇛⇒⇛ᴺ)

-- Import and re-export
open import Syho.Logic.Judg public using (○-mono; ○-eatˡ; ○-new; □○-new-rec;
  ○-use; ↪⇛-≤; ↪⇛-eatˡ⁻ˡᵘ; ↪⇛-monoʳᵘ; ↪⇛-eatˡ⁻ʳ; ↪⇛-frameˡ; ○⇒↪⇛; ↪⇛-use;
  ↪ᵃ⟨⟩-≤; ↪ᵃ⟨⟩-eatˡ⁻ˡᵘ; ↪ᵃ⟨⟩-monoʳᵘ; ↪ᵃ⟨⟩-eatˡ⁻ʳ; ↪ᵃ⟨⟩-frameˡ; ○⇒↪ᵃ⟨⟩; ↪ᵃ⟨⟩-use;
  ↪⟨⟩ᵀ⇒↪⟨⟩ᴾ; ↪⟨⟩ᵀ-≤; ↪⟨⟩-eatˡ⁻ˡᵘᴺ; ↪⟨⟩-monoʳᵘᴺ; ↪⟨⟩-eatˡ⁻ʳ; ↪⟨⟩-frameˡ; ○⇒↪⟨⟩;
  ↪⟨⟩ᴾ-use; ↪⟨⟩ᵀ-use; ↪⟨⟩∞-≤; ↪⟨⟩∞-eatˡ⁻ᵘᴺ; ○⇒↪⟨⟩∞; ↪⟨⟩∞-use)

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

  -- Let ○ eat a basic proposition

  -->  ○-eatˡ :  {{Basic Q}} →  Q ∗ ○ P˂ ⊢[ ι ] ○ ¡ᴾ (Q ∗ P˂ .!)

  ○-eatʳ :  {{Basic Q}} →  ○ P˂ ∗ Q ⊢[ ι ] ○ ¡ᴾ (P˂ .! ∗ Q)
  ○-eatʳ =  ∗-comm » ○-eatˡ » ○-mono $ ⇒< ∗-comm

  -- Get ○

  -->  ○-new :  P˂ .! ⊢[ ι ][ i ]⇛ ○ P˂

  -->  □○-new-rec :  □ ○ P˂ -∗ □ P˂ .! ⊢[ ι ][ i ]⇛ □ ○ P˂

  □○-new :  □ P˂ .! ⊢[ ι ][ i ]⇛ □ ○ P˂
  □○-new =  -∗-const » □○-new-rec

  ------------------------------------------------------------------------------
  -- On ↪⇛

  -->  ○⇒↪⇛ :  P˂ .!  ∗  R˂ .! ⊢[< ι ][ i ]⇛  Q˂ .!  →
  -->          ○ R˂  ⊢[ ι ]  P˂ ↪[ i ]⇛ Q˂

  -->  ↪⇛-use :  P˂ .!  ∗  (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ][ ṡ i ]⇛  Q˂ .!

  -- Modify ⇛ proof

  -->  ↪⇛-≤ :  i ≤ j  →   P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P˂ ↪[ j ]⇛ Q˂

  -->  ↪⇛-eatˡ⁻ˡᵘ :  {{Basic R}}  →   R  ∗  P'˂ .!  ⊢[< ι ][ i ]⇛  P˂ .! →
  -->                R  ∗  (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ]  P'˂ ↪[ i ]⇛ Q˂

  ↪⇛-monoˡᵘ :  P'˂ .! ⊢[< ι ][ i ]⇛ P˂ .! →
               P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P'˂ ↪[ i ]⇛ Q˂
  ↪⇛-monoˡᵘ P'⊢⇛P =  ⊤∗-intro » ↪⇛-eatˡ⁻ˡᵘ $ (∗-elimʳ »_) $ᵀʰ P'⊢⇛P

  ↪⇛-eatˡ⁻ˡ :  {{Basic R}}  →
    R ∗ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ]  ¡ᴾ (R -∗ P˂ .!) ↪[ i ]⇛ Q˂
  ↪⇛-eatˡ⁻ˡ =  ↪⇛-eatˡ⁻ˡᵘ $ ⇒< $ ⇒⇛ $ -∗-elimˡ ⊢-refl

  ↪⇛-monoˡ :  P'˂ .! ⊢[< ι ] P˂ .! →
              P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P'˂ ↪[ i ]⇛ Q˂
  ↪⇛-monoˡ P'⊢P =  ↪⇛-monoˡᵘ $ ⇒⇛ $ᵀʰ P'⊢P

  -->  ↪⇛-monoʳᵘ :  Q˂ .!  ⊢[< ι ][ i ]⇛  Q'˂ .! →
  -->               P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P˂ ↪[ i ]⇛ Q'˂

  ↪⇛-monoʳ :  Q˂ .!  ⊢[< ι ]  Q'˂ .!  →
              P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P˂ ↪[ i ]⇛ Q'˂
  ↪⇛-monoʳ Q⊢Q' =  ↪⇛-monoʳᵘ $ ⇒⇛ $ᵀʰ Q⊢Q'

  -->  ↪⇛-eatˡ⁻ʳ :  {{Basic R}}  →
  -->    R  ∗  (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ]  P˂ ↪[ i ]⇛ ¡ᴾ (R ∗ Q˂ .!)

  -->  ↪⇛-frameˡ :  P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]
  -->                 ¡ᴾ (R ∗ P˂ .!) ↪[ i ]⇛ ¡ᴾ (R ∗ Q˂ .!)

  ↪⇛-frameʳ :  P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  ¡ᴾ (P˂ .! ∗ R) ↪[ i ]⇛ ¡ᴾ (Q˂ .! ∗ R)
  ↪⇛-frameʳ =  ↪⇛-frameˡ » ↪⇛-monoˡ (⇒< ∗-comm) » ↪⇛-monoʳ $ ⇒< ∗-comm

  ------------------------------------------------------------------------------
  -- On ↪ᵃ⟨ ⟩

  -->  ○⇒↪ᵃ⟨⟩ :  P˂ .!  ∗  R˂ .!  ⊢[< ι ][ i ]ᵃ⟨ red ⟩ (λ v →  Q˂˙ v .!)  →
  -->            ○ R˂  ⊢[ ι ]  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙

  -->  ↪ᵃ⟨⟩-use :  P˂ .!  ∗  (P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙)
  -->                ⊢[ ι ][ ṡ i ]ᵃ⟨ red ⟩ λ v →  Q˂˙ v .!

  -- Modify ⟨ ⟩ᵀ proof

  -->  ↪ᵃ⟨⟩-≤ :  i ≤ j  →   P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]  P˂ ↪[ j ]ᵃ⟨ red ⟩ Q˂˙

  -->  ↪ᵃ⟨⟩-eatˡ⁻ˡᵘ :  {{Basic R}}  →   R  ∗  P'˂ .!  ⊢[< ι ][ j ]⇛  P˂ .!  →
  -->    R ∗ (P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙)  ⊢[ ι ]  P'˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙

  ↪ᵃ⟨⟩-monoˡᵘ :  P'˂ .! ⊢[< ι ][ i ]⇛ P˂ .! →
                 P˂ ↪[ j ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]  P'˂ ↪[ j ]ᵃ⟨ red ⟩ Q˂˙
  ↪ᵃ⟨⟩-monoˡᵘ P'⊢⇛P =  ⊤∗-intro » ↪ᵃ⟨⟩-eatˡ⁻ˡᵘ $ (∗-elimʳ »_) $ᵀʰ P'⊢⇛P

  ↪ᵃ⟨⟩-eatˡ⁻ˡ :  {{Basic R}}  →
    R ∗ (P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙)  ⊢[ ι ]  ¡ᴾ (R -∗ P˂ .!) ↪[ i ]ᵃ⟨ red ⟩ Q˂˙
  ↪ᵃ⟨⟩-eatˡ⁻ˡ =  ↪ᵃ⟨⟩-eatˡ⁻ˡᵘ {i = 0} $ ⇒< $ ⇒⇛ $ -∗-elimˡ ⊢-refl

  ↪ᵃ⟨⟩-monoˡ :  P'˂ .! ⊢[< ι ] P˂ .! →
                P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]  P'˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙
  ↪ᵃ⟨⟩-monoˡ P'⊢P =  ↪ᵃ⟨⟩-monoˡᵘ {i = 0} $ ⇒⇛ $ᵀʰ P'⊢P

  -->  ↪ᵃ⟨⟩-monoʳᵘ :  (∀ v →  Q˂˙ v .!  ⊢[< ι ][ i ]⇛  Q'˂˙ v .!)  →
  -->                 P˂ ↪[ j ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]  P˂ ↪[ j ]ᵃ⟨ red ⟩ Q'˂˙

  ↪ᵃ⟨⟩-monoʳ :  (∀ v →  Q˂˙ v .!  ⊢[< ι ]  Q'˂˙ v .!)  →
                P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q'˂˙
  ↪ᵃ⟨⟩-monoʳ Qv⊢Q'v =  ↪ᵃ⟨⟩-monoʳᵘ {i = 0} λ v → ⇒⇛ $ᵀʰ Qv⊢Q'v v

  -->  ↪ᵃ⟨⟩-eatˡ⁻ʳ :  {{Basic R}}  →
  -->    R  ∗  (P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙)  ⊢[ ι ]
  -->      P˂ ↪[ i ]ᵃ⟨ red ⟩ λ v → ¡ᴾ (R ∗ Q˂˙ v .!)

  -->  ↪ᵃ⟨⟩-frameˡ :  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]
  -->                  ¡ᴾ (R ∗ P˂ .!) ↪[ i ]ᵃ⟨ red ⟩ λ v → ¡ᴾ (R ∗ Q˂˙ v .!)

  ↪ᵃ⟨⟩-frameʳ :  P˂ ↪[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ι ]
                   ¡ᴾ (P˂ .! ∗ R) ↪[ i ]ᵃ⟨ red ⟩ λ v → ¡ᴾ (Q˂˙ v .! ∗ R)
  ↪ᵃ⟨⟩-frameʳ =  ↪ᵃ⟨⟩-frameˡ »
    ↪ᵃ⟨⟩-monoˡ (⇒< ∗-comm) » ↪ᵃ⟨⟩-monoʳ λ _ → ⇒< ∗-comm

  ------------------------------------------------------------------------------
  -- On ↪⟨ ⟩

  -->  ↪⟨⟩ᵀ⇒↪⟨⟩ᴾ :  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q˂˙

  -->  ○⇒↪⟨⟩ :  P˂ .!  ∗  R˂ .!  ⊢[< ι ]⟨ e ⟩[ κ ] (λ v →  Q˂˙ v .!)  →
  -->           ○ R˂  ⊢[ ι ]  P˂ ↪⟨ e ⟩[ κ ] Q˂˙

  -->  ↪⟨⟩ᴾ-use :  e ⇒ᴾ e'  →
  -->    P˂ .!  ∗  (P˂ ↪⟨ e' ⟩ᴾ Q˂˙)  ⊢[ ι ]⟨ e ⟩ᴾ λ v →  Q˂˙ v .!

  -->  ↪⟨⟩ᵀ-use :  P˂ .!  ∗  (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙)
  -->                ⊢[ ι ]⟨ e ⟩ᵀ[ ṡ i ] λ v →  Q˂˙ v .!

  -- Modify ⟨ ⟩ proof

  -->  ↪⟨⟩ᵀ-≤ :  i ≤ j  →   P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ j ] Q˂˙

  -->  ↪⟨⟩-eatˡ⁻ˡᵘᴺ :  {{Basic R}}  →   R  ∗  P'˂ .!  ⊢[< ι ][ i ]⇛ᴺ  P˂ .!  →
  -->                  R  ∗  (P˂ ↪⟨ e ⟩[ κ ] Q˂˙)  ⊢[ ι ]  P'˂ ↪⟨ e ⟩[ κ ] Q˂˙

  ↪⟨⟩-eatˡ⁻ˡᵘ :  {{Basic R}}  →   R  ∗  P'˂ .!  ⊢[< ι ][ i ]⇛  P˂ .!  →
                 R  ∗  (P˂ ↪⟨ e ⟩[ κ ] Q˂˙)  ⊢[ ι ]  P'˂ ↪⟨ e ⟩[ κ ] Q˂˙
  ↪⟨⟩-eatˡ⁻ˡᵘ =  ↪⟨⟩-eatˡ⁻ˡᵘᴺ ∘ (⇛⇒⇛ᴺ $ᵀʰ_)

  ↪⟨⟩-eatˡ⁻ˡ :  {{Basic R}}  →
    R  ∗  (P˂ ↪⟨ e ⟩[ κ ] Q˂˙)  ⊢[ ι ]  ¡ᴾ (R -∗ P˂ .!) ↪⟨ e ⟩[ κ ] Q˂˙
  ↪⟨⟩-eatˡ⁻ˡ =  ↪⟨⟩-eatˡ⁻ˡᵘ {i = 0} $ ⇒< $ ⇒⇛ $ -∗-elimˡ ⊢-refl

  ↪⟨⟩-monoˡᵘᴺ :  P'˂ .!  ⊢[< ι ][ i ]⇛ᴺ  P˂ .!  →
                 P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ι ]  P'˂ ↪⟨ e ⟩[ κ ] Q˂˙
  ↪⟨⟩-monoˡᵘᴺ P'⊢⇛P =  ⊤∗-intro » ↪⟨⟩-eatˡ⁻ˡᵘᴺ $ (∗-elimʳ »ᵘᴺ_) $ᵀʰ P'⊢⇛P

  ↪⟨⟩-monoˡᵘ :  P'˂ .!  ⊢[< ι ][ i ]⇛  P˂ .!  →
                P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ι ]  P'˂ ↪⟨ e ⟩[ κ ] Q˂˙
  ↪⟨⟩-monoˡᵘ =  ↪⟨⟩-monoˡᵘᴺ ∘ (⇛⇒⇛ᴺ $ᵀʰ_)

  ↪⟨⟩-monoˡ :  P'˂ .! ⊢[< ι ] P˂ .! →
               P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ι ]  P'˂ ↪⟨ e ⟩[ κ ] Q˂˙
  ↪⟨⟩-monoˡ =  ↪⟨⟩-monoˡᵘ {i = 0} ∘ (⇒⇛ $ᵀʰ_)

  -->  ↪⟨⟩-monoʳᵘᴺ :  (∀ v →  Q˂˙ v .!  ⊢[< ι ][ i ]⇛ᴺ  Q'˂˙ v .!)  →
  -->                 P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩[ κ ] Q'˂˙

  ↪⟨⟩-monoʳᵘ :  (∀ v →  Q˂˙ v .!  ⊢[< ι ][ i ]⇛  Q'˂˙ v .!)  →
                P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩[ κ ] Q'˂˙
  ↪⟨⟩-monoʳᵘ Qv⊢⇛Q'v =  ↪⟨⟩-monoʳᵘᴺ λ v → ⇛⇒⇛ᴺ $ᵀʰ Qv⊢⇛Q'v v

  ↪⟨⟩-monoʳ :  (∀ v →  Q˂˙ v .!  ⊢[< ι ]  Q'˂˙ v .!)  →
               P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ι ]  P˂ ↪⟨ e ⟩[ κ ] Q'˂˙
  ↪⟨⟩-monoʳ Qv⊢Q'v =  ↪⟨⟩-monoʳᵘ {i = 0} λ v → ⇒⇛ $ᵀʰ Qv⊢Q'v v

  -->  ↪⟨⟩-eatˡ⁻ʳ :  {{Basic R}}  →
  -->    R  ∗  (P˂ ↪⟨ e ⟩[ κ ] Q˂˙)  ⊢[ ι ]
  -->      P˂ ↪⟨ e ⟩[ κ ] λ v → ¡ᴾ (R ∗ Q˂˙ v .!)

  -->  ↪⟨⟩-frameˡ :  P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ι ]
  -->                  ¡ᴾ (R ∗ P˂ .!) ↪⟨ e ⟩[ κ ] λ v → ¡ᴾ (R ∗ Q˂˙ v .!)

  ↪⟨⟩-frameʳ :  P˂ ↪⟨ e ⟩[ κ ] Q˂˙  ⊢[ ι ]
                  ¡ᴾ (P˂ .! ∗ R) ↪⟨ e ⟩[ κ ] λ v → ¡ᴾ (Q˂˙ v .! ∗ R)
  ↪⟨⟩-frameʳ =  ↪⟨⟩-frameˡ » ↪⟨⟩-monoˡ (⇒< ∗-comm) » ↪⟨⟩-monoʳ λ _ → ⇒< ∗-comm

  ------------------------------------------------------------------------------
  -- On ↪⟨ ⟩∞

  -- Modify ⟨ ⟩ proof

  -->  ↪⟨⟩∞-≤ :  i ≤ j  →   P˂ ↪[ i ]⟨ e ⟩∞  ⊢[ ι ]  P˂ ↪[ j ]⟨ e ⟩∞

  -->  ↪⟨⟩∞-eatˡ⁻ᵘᴺ :  {{Basic R}}  →   R  ∗  Q˂ .!  ⊢[< ι ][ i ]⇛ᴺ  P˂ .!  →
  -->                  R  ∗  (P˂ ↪[ j ]⟨ e ⟩∞)  ⊢[ ι ]  Q˂ ↪[ j ]⟨ e ⟩∞

  ↪⟨⟩∞-eatˡ⁻ᵘ :  {{Basic R}}  →   R  ∗  Q˂ .!  ⊢[< ι ][ i ]⇛  P˂ .!  →
                 R  ∗  (P˂ ↪[ j ]⟨ e ⟩∞)  ⊢[ ι ]  Q˂ ↪[ j ]⟨ e ⟩∞
  ↪⟨⟩∞-eatˡ⁻ᵘ =  ↪⟨⟩∞-eatˡ⁻ᵘᴺ ∘ (⇛⇒⇛ᴺ $ᵀʰ_)

  ↪⟨⟩∞-eatˡ :  {{Basic R}}  →
    R  ∗  (P˂ ↪[ i ]⟨ e ⟩∞)  ⊢[ ι ]  ¡ᴾ (R -∗ P˂ .!) ↪[ i ]⟨ e ⟩∞
  ↪⟨⟩∞-eatˡ =  ↪⟨⟩∞-eatˡ⁻ᵘ {i = 0} $ ⇒< $ ⇒⇛ $ -∗-elimˡ ⊢-refl

  ↪⟨⟩∞-monoᵘᴺ :  Q˂ .!  ⊢[< ι ][ i ]⇛ᴺ  P˂ .!  →
                 P˂ ↪[ j ]⟨ e ⟩∞  ⊢[ ι ]  Q˂ ↪[ j ]⟨ e ⟩∞
  ↪⟨⟩∞-monoᵘᴺ Q⊢⇛P =  ⊤∗-intro » ↪⟨⟩∞-eatˡ⁻ᵘᴺ $ (∗-elimʳ »ᵘᴺ_) $ᵀʰ Q⊢⇛P

  ↪⟨⟩∞-monoᵘ :  Q˂ .!  ⊢[< ι ][ i ]⇛  P˂ .!  →
                P˂ ↪[ j ]⟨ e ⟩∞  ⊢[ ι ]  Q˂ ↪[ j ]⟨ e ⟩∞
  ↪⟨⟩∞-monoᵘ =  ↪⟨⟩∞-monoᵘᴺ ∘ (⇛⇒⇛ᴺ $ᵀʰ_)

  ↪⟨⟩∞-mono :  Q˂ .!  ⊢[< ι ]  P˂ .!  →
               P˂ ↪[ i ]⟨ e ⟩∞  ⊢[ ι ]  Q˂ ↪[ i ]⟨ e ⟩∞
  ↪⟨⟩∞-mono =  ↪⟨⟩∞-monoᵘ {i = 0} ∘ (⇒⇛ $ᵀʰ_)
