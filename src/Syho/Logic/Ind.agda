--------------------------------------------------------------------------------
-- Proof rules on ○, ↪=>>, ↪⟨ ⟩ᴾ, and ↪⟨ ⟩ᵀ
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Ind where

open import Base.Level using (Level; ↓_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk; ¡_; !)
open import Base.Func using (_∘_; id; const; _$_)
open import Base.Nat using (ℕ; _≤ᵈ_; ≤ᵈ-refl; ≤ᵈsuc; _≤_; ≤⇒≤ᵈ)
open import Syho.Lang.Expr using (Type; Expr; Val)
open import Syho.Logic.Prop using (Prop'; Prop˂; ∀₀-syntax; _∗_; □_; ○_;
  _↪[_]=>>_; _↪⟨_⟩ᴾ_; _↪⟨_⟩ᵀ[_]_; Basic)
open import Syho.Logic.Core using (_⊢[_]_; _⊢[<_]_; Pers; ⊢-refl; _»_; ∗-comm;
  ∗-elimʳ; ⊤∗-intro; -∗-const)
open import Syho.Logic.Supd using ([_]=>>_; _⊢[_][_]=>>_; _⊢[<_][_]=>>_; ⇒=>>;
  _ᵘ»_)

-- Import and re-export
open import Syho.Logic.Judg public using (○-mono-∗; ○-alloc; □○-alloc-rec;
  ○-use; ↪=>>-monoˡᵘ-∗; ↪=>>-monoʳᵘ-∗; ↪=>>-suc; ↪=>>-frameˡ; ○⇒↪=>>; ↪=>>-use;
  ↪⟨⟩ᴾ-monoˡᵘ-∗; ↪⟨⟩ᴾ-monoʳᵘ-∗; ↪⟨⟩ᴾ-frameˡ; ○⇒↪⟨⟩ᴾ; ↪⟨⟩ᴾ-use; ↪⟨⟩ᵀ-monoˡᵘ-∗;
  ↪⟨⟩ᵀ-monoʳᵘ-∗; ↪⟨⟩ᵀ-suc; ↪⟨⟩ᵀ-frameˡ; ○⇒↪⟨⟩ᵀ; ↪⟨⟩ᵀ-use)

private variable
  ℓ :  Level
  ι :  Size
  i j :  ℕ
  T :  Type
  P Q R :  Prop' ∞
  P˂ P'˂ Q˂ Q'˂ R˂ :  Prop˂ ∞
  X :  Set ℓ
  x :  X
  P˂˙ Q˂˙ :  X → Prop˂ ∞
  Qᵛ :  Val T → Prop' ∞
  Q˂ᵛ Q'˂ᵛ :  Val T → Prop˂ ∞
  Q˂ᵛ˙ :  X → Val T → Prop˂ ∞
  e :  Expr ∞ T

abstract

  ------------------------------------------------------------------------------
  -- On ○

  -->  ○-use :  ○ P˂ ⊢[ ι ][ i ]=>> P˂ .!

  -- Monotonicity of ○

  -->  ○-mono-∗ :  {{Basic R}} →  R ∗ P˂ .! ⊢[< ι ] Q˂ .! →
  -->              R ∗ ○ P˂ ⊢[ ι ] ○ Q˂

  ○-mono :  P˂ .! ⊢[< ι ] Q˂ .! →  ○ P˂ ⊢[ ι ] ○ Q˂
  ○-mono P⊢<Q =  ⊤∗-intro » ○-mono-∗ λ{ .! → ∗-elimʳ » P⊢<Q .! }

  -- Allocate ○

  -->  ○-alloc :  P˂ .! ⊢[ ι ][ i ]=>> ○ P˂

  -->  □○-alloc-rec :  {{Pers (P˂ .!)}} →  □ ○ P˂ -∗ P˂ .! ⊢[ ι ][ i ]=>> □ ○ P˂

  □○-alloc :  {{Pers (P˂ .!)}} →  P˂ .! ⊢[ ι ][ i ]=>> □ ○ P˂
  □○-alloc =  -∗-const » □○-alloc-rec

  ------------------------------------------------------------------------------
  -- On ↪=>>

  -->  ○⇒↪=>> :  R˂ .! ∗ P˂ .! ⊢[< ι ][ i ]=>> Q˂ .! →
  -->            ○ R˂  ⊢[ ι ]  P˂ ↪[ i ]=>> Q˂

  -->  ↪=>>-use :  P˂ .! ∗ (P˂ ↪[ i ]=>> Q˂)  ⊢[ ι ][ suc i ]=>>  Q˂ .!

  -- Monotonicity of ↪=>>

  -->  ↪=>>-monoˡᵘ-∗ :  {{Basic R}} →  R ∗ P'˂ .! ⊢[< ι ][ i ]=>> P˂ .! →
  -->                   R ∗ (P˂ ↪[ i ]=>> Q˂)  ⊢[ ι ]  P'˂ ↪[ i ]=>> Q˂

  -->  ↪=>>-monoʳᵘ-∗ :  {{Basic R}} →  R ∗ Q˂ .! ⊢[< ι ][ i ]=>> Q'˂ .! →
  -->                   R ∗ (P˂ ↪[ i ]=>> Q˂)  ⊢[ ι ]  P˂ ↪[ i ]=>> Q'˂

  -- We don't have ↪=>>-mono rules (which modify both the P and Q sides),
  -- because handling two thunks doesn't work well on the current Agda

  ↪=>>-monoˡᵘ :  P'˂ .! ⊢[< ι ][ i ]=>> P˂ .! →
                 P˂ ↪[ i ]=>> Q˂  ⊢[ ι ]  P'˂ ↪[ i ]=>> Q˂
  ↪=>>-monoˡᵘ P'⊢=>>P =  ⊤∗-intro » ↪=>>-monoˡᵘ-∗ λ{ .! → ∗-elimʳ » P'⊢=>>P .! }

  ↪=>>-monoʳᵘ :  Q˂ .! ⊢[< ι ][ i ]=>> Q'˂ .! →
                 P˂ ↪[ i ]=>> Q˂  ⊢[ ι ]  P˂ ↪[ i ]=>> Q'˂
  ↪=>>-monoʳᵘ Q⊢=>>Q' =  ⊤∗-intro » ↪=>>-monoʳᵘ-∗ λ{ .! → ∗-elimʳ » Q⊢=>>Q' .! }

  ↪=>>-monoˡ-∗ :  {{Basic R}} →  R ∗ P'˂ .! ⊢[< ι ] P˂ .! →
                  R ∗ (P˂ ↪[ i ]=>> Q˂)  ⊢[ ι ]  P'˂ ↪[ i ]=>> Q˂
  ↪=>>-monoˡ-∗ ⊢< =  ↪=>>-monoˡᵘ-∗ $ λ{ .! → ⇒=>> $ ⊢< .! }

  ↪=>>-monoʳ-∗ :  {{Basic R}} →  R ∗ Q˂ .! ⊢[< ι ] Q'˂ .! →
                  R ∗ (P˂ ↪[ i ]=>> Q˂)  ⊢[ ι ]  P˂ ↪[ i ]=>> Q'˂
  ↪=>>-monoʳ-∗ ⊢< =  ↪=>>-monoʳᵘ-∗ $ λ{ .! → ⇒=>> $ ⊢< .! }

  ↪=>>-monoˡ :  P'˂ .! ⊢[< ι ] P˂ .! →
                P˂ ↪[ i ]=>> Q˂  ⊢[ ι ]  P'˂ ↪[ i ]=>> Q˂
  ↪=>>-monoˡ ⊢< =  ↪=>>-monoˡᵘ $ λ{ .! → ⇒=>> $ ⊢< .! }

  ↪=>>-monoʳ :  Q˂ .! ⊢[< ι ] Q'˂ .! →
                P˂ ↪[ i ]=>> Q˂  ⊢[ ι ]  P˂ ↪[ i ]=>> Q'˂
  ↪=>>-monoʳ ⊢< =  ↪=>>-monoʳᵘ $ λ{ .! → ⇒=>> $ ⊢< .! }

  -- Modify =>> proof

  -->  ↪=>>-suc :  P˂ ↪[ i ]=>> Q˂  ⊢[ ι ]  P˂ ↪[ suc i ]=>> Q˂

  ↪=>>-≤ᵈ :  i ≤ᵈ j →  P˂ ↪[ i ]=>> Q˂  ⊢[ ι ]  P˂ ↪[ j ]=>> Q˂
  ↪=>>-≤ᵈ ≤ᵈ-refl =  ⊢-refl
  ↪=>>-≤ᵈ (≤ᵈsuc i≤ᵈj') =  ↪=>>-≤ᵈ i≤ᵈj' » ↪=>>-suc

  ↪=>>-≤ :  i ≤ j →  P˂ ↪[ i ]=>> Q˂  ⊢[ ι ]  P˂ ↪[ j ]=>> Q˂
  ↪=>>-≤ =  ↪=>>-≤ᵈ ∘ ≤⇒≤ᵈ

  -->  ↪=>>-frameˡ :  P˂ ↪[ i ]=>> Q˂  ⊢[ ι ]
  -->                   ¡ (R ∗ P˂ .!) ↪[ i ]=>> ¡ (R ∗ Q˂ .!)

  ↪=>>-frameʳ :  P˂ ↪[ i ]=>> Q˂  ⊢[ ι ]  ¡ (P˂ .! ∗ R) ↪[ i ]=>> ¡ (Q˂ .! ∗ R)
  ↪=>>-frameʳ =  ↪=>>-frameˡ » ↪=>>-monoˡ (¡ ∗-comm) » ↪=>>-monoʳ (¡ ∗-comm)

  ------------------------------------------------------------------------------
  -- On ↪⟨ ⟩ᴾ

  -->  ○⇒↪⟨⟩ᴾ :  P˂ .! ∗ R˂ .! ⊢[< ι ]⟨ e ⟩ᴾ (λ v → Q˂ᵛ v .!) →
  -->            ○ R˂  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ

  -->  ↪⟨⟩ᴾ-use :  P˂ .! ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ)  ⊢[ ι ]⟨ ▶ ¡ e ⟩ᴾ  λ v → Q˂ᵛ v .!

  -- Monotonicity of ↪⟨ ⟩ᴾ

  -->  ↪⟨⟩ᴾ-monoˡᵘ-∗ :  {{Basic R}} →  R ∗ P'˂ .! ⊢[< ι ][ i ]=>> P˂ .! →
  -->                   R ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ)  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᴾ Q˂ᵛ

  -->  ↪⟨⟩ᴾ-monoʳᵘ-∗ :  {{Basic R}} →
  -->    (∀ v →  R ∗ Q˂ᵛ v .! ⊢[< ι ][ i ]=>> Q'˂ᵛ v .!) →
  -->    R ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ)  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q'˂ᵛ

  ↪⟨⟩ᴾ-monoˡᵘ :  P'˂ .! ⊢[< ι ][ i ]=>> P˂ .! →
                 P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᴾ Q˂ᵛ
  ↪⟨⟩ᴾ-monoˡᵘ P'⊢=>>P =  ⊤∗-intro » ↪⟨⟩ᴾ-monoˡᵘ-∗ λ{ .! → ∗-elimʳ » P'⊢=>>P .! }

  ↪⟨⟩ᴾ-monoʳᵘ :  (∀ v →  Q˂ᵛ v .! ⊢[< ι ][ i ]=>> Q'˂ᵛ v .!) →
                 P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q'˂ᵛ
  ↪⟨⟩ᴾ-monoʳᵘ ∀vQ⊢=>>Q' =
    ⊤∗-intro » ↪⟨⟩ᴾ-monoʳᵘ-∗ λ{ v .! → ∗-elimʳ » ∀vQ⊢=>>Q' v .! }

  ↪⟨⟩ᴾ-monoˡ-∗ :  {{Basic R}} →  R ∗ P'˂ .! ⊢[< ι ] P˂ .! →
                  R ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ)  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᴾ Q˂ᵛ
  ↪⟨⟩ᴾ-monoˡ-∗ ⊢< =  ↪⟨⟩ᴾ-monoˡᵘ-∗ {i = 0} $ λ{ .! → ⇒=>> $ ⊢< .! }

  ↪⟨⟩ᴾ-monoʳ-∗ :  {{Basic R}} →  (∀ v →  R ∗ Q˂ᵛ v .! ⊢[< ι ] Q'˂ᵛ v .!) →
                  R ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ)  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q'˂ᵛ
  ↪⟨⟩ᴾ-monoʳ-∗ ⊢< =  ↪⟨⟩ᴾ-monoʳᵘ-∗ {i = 0} $ λ{ v .! → ⇒=>> $ ⊢< v .! }

  ↪⟨⟩ᴾ-monoˡ :  P'˂ .! ⊢[< ι ] P˂ .! →
                P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᴾ Q˂ᵛ
  ↪⟨⟩ᴾ-monoˡ ⊢< =  ↪⟨⟩ᴾ-monoˡᵘ {i = 0} $ λ{ .! → ⇒=>> $ ⊢< .! }

  ↪⟨⟩ᴾ-monoʳ :  (∀ v →  Q˂ᵛ v .! ⊢[< ι ] Q'˂ᵛ v .!) →
                P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q'˂ᵛ
  ↪⟨⟩ᴾ-monoʳ ⊢< =  ↪⟨⟩ᴾ-monoʳᵘ {i = 0} $ λ{ v .! → ⇒=>> $ ⊢< v .! }

  -- Modify ⟨ ⟩ᴾ proof

  -->  ↪⟨⟩ᴾ-frameˡ :  P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ  ⊢[ ι ]
  -->                   ¡ (R ∗ P˂ .!) ↪⟨ e ⟩ᴾ λ v → ¡ (R ∗ Q˂ᵛ v .!)

  ↪⟨⟩ᴾ-frameʳ :  P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ  ⊢[ ι ]
                   ¡ (P˂ .! ∗ R) ↪⟨ e ⟩ᴾ λ v → ¡ (Q˂ᵛ v .! ∗ R)
  ↪⟨⟩ᴾ-frameʳ =  ↪⟨⟩ᴾ-frameˡ »
    ↪⟨⟩ᴾ-monoˡ (¡ ∗-comm) » ↪⟨⟩ᴾ-monoʳ (λ _ → ¡ ∗-comm)

  ------------------------------------------------------------------------------
  -- On ↪⟨ ⟩ᵀ

  -->  ○⇒↪⟨⟩ᵀ :  P˂ .! ∗ R˂ .! ⊢[< ι ]⟨ e ⟩ᵀ[ i ] (λ v → Q˂ᵛ v .!) →
  -->            ○ R˂  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ

  -->  ↪⟨⟩ᵀ-use :  P˂ .! ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ)
  -->                ⊢[ ι ]⟨ ¡ e ⟩ᵀ[ suc i ]  λ v → Q˂ᵛ v .!

  -- Monotonicity of ↪⟨ ⟩ᵀ

  -->  ↪⟨⟩ᵀ-monoˡᵘ-∗ :  {{Basic R}} →  R ∗ P'˂ .! ⊢[< ι ][ j ]=>> P˂ .! →
  -->                   R ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ)  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ

  -->  ↪⟨⟩ᵀ-monoʳᵘ-∗ :  {{Basic R}} →
  -->    (∀ v →  R ∗ Q˂ᵛ v .! ⊢[< ι ][ j ]=>> Q'˂ᵛ v .!) →
  -->    R ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ)  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q'˂ᵛ

  ↪⟨⟩ᵀ-monoˡᵘ :  P'˂ .! ⊢[< ι ][ j ]=>> P˂ .! →
                 P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ
  ↪⟨⟩ᵀ-monoˡᵘ P'⊢=>>P =  ⊤∗-intro » ↪⟨⟩ᵀ-monoˡᵘ-∗ λ{ .! → ∗-elimʳ » P'⊢=>>P .! }

  ↪⟨⟩ᵀ-monoʳᵘ :  (∀ v →  Q˂ᵛ v .! ⊢[< ι ][ j ]=>> Q'˂ᵛ v .!) →
                 P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q'˂ᵛ
  ↪⟨⟩ᵀ-monoʳᵘ ∀vQ⊢=>>Q' =
    ⊤∗-intro » ↪⟨⟩ᵀ-monoʳᵘ-∗ λ{ v .! → ∗-elimʳ » ∀vQ⊢=>>Q' v .! }

  ↪⟨⟩ᵀ-monoˡ-∗ :  {{Basic R}} →  R ∗ P'˂ .! ⊢[< ι ] P˂ .! →
                  R ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ)  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ
  ↪⟨⟩ᵀ-monoˡ-∗ ⊢< =  ↪⟨⟩ᵀ-monoˡᵘ-∗ {j = 0} $ λ{ .! → ⇒=>> $ ⊢< .! }

  ↪⟨⟩ᵀ-monoʳ-∗ :  {{Basic R}} →  (∀ v →  R ∗ Q˂ᵛ v .! ⊢[< ι ] Q'˂ᵛ v .!) →
                  R ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ)  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q'˂ᵛ
  ↪⟨⟩ᵀ-monoʳ-∗ ⊢< =  ↪⟨⟩ᵀ-monoʳᵘ-∗ {j = 0} $ λ{ v .! → ⇒=>> $ ⊢< v .! }

  ↪⟨⟩ᵀ-monoˡ :  P'˂ .! ⊢[< ι ] P˂ .! →
                P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ
  ↪⟨⟩ᵀ-monoˡ ⊢< =  ↪⟨⟩ᵀ-monoˡᵘ {j = 0} $ λ{ .! → ⇒=>> $ ⊢< .! }

  ↪⟨⟩ᵀ-monoʳ :  (∀ v →  Q˂ᵛ v .! ⊢[< ι ] Q'˂ᵛ v .!) →
                P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q'˂ᵛ
  ↪⟨⟩ᵀ-monoʳ ⊢< =  ↪⟨⟩ᵀ-monoʳᵘ {j = 0} $ λ{ v .! → ⇒=>> $ ⊢< v .! }

  -- Modify ⟨ ⟩ᵀ proof

  -->  ↪⟨⟩ᵀ-suc :  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ suc i ] Q˂ᵛ

  ↪⟨⟩ᵀ-≤ᵈ :  i ≤ᵈ j →  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ j ] Q˂ᵛ
  ↪⟨⟩ᵀ-≤ᵈ ≤ᵈ-refl =  ⊢-refl
  ↪⟨⟩ᵀ-≤ᵈ (≤ᵈsuc i≤ᵈj') =  ↪⟨⟩ᵀ-≤ᵈ i≤ᵈj' » ↪⟨⟩ᵀ-suc

  ↪⟨⟩ᵀ-≤ :  i ≤ j →  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ j ] Q˂ᵛ
  ↪⟨⟩ᵀ-≤ =  ↪⟨⟩ᵀ-≤ᵈ ∘ ≤⇒≤ᵈ

  -->  ↪⟨⟩ᵀ-frameˡ :  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ  ⊢[ ι ]
  -->                  ¡ (R ∗ P˂ .!) ↪⟨ e ⟩ᵀ[ i ] λ v → ¡ (R ∗ Q˂ᵛ v .!)

  ↪⟨⟩ᵀ-frameʳ :  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ  ⊢[ ι ]
                   ¡ (P˂ .! ∗ R) ↪⟨ e ⟩ᵀ[ i ] λ v → ¡ (Q˂ᵛ v .! ∗ R)
  ↪⟨⟩ᵀ-frameʳ =  ↪⟨⟩ᵀ-frameˡ »
    ↪⟨⟩ᵀ-monoˡ (¡ ∗-comm) » ↪⟨⟩ᵀ-monoʳ (λ _ → ¡ ∗-comm)
