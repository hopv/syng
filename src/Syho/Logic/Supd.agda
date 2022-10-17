--------------------------------------------------------------------------------
-- Proof rules on the super-update sequent
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Supd where

open import Base.Func using (_$_; _∘_; id)
open import Base.Eq using (refl)
open import Base.Size using (𝕊)
open import Base.Zoi using (Zoi; ✔ᶻ_)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Base.Nat using (ℕ; _<ᵈ_; ≤ᵈ-refl; ≤ᵈṡ; _≤_; _<_; ≤⇒<≡; ≤⇒≤ᵈ)
open import Syho.Logic.Prop using (Name; Prop∞; _∗_; ⤇_; [_]ᴺ)
open import Syho.Logic.Core using (_⊢[_]_; ⇒<; ⊢-refl; _»_; ∗-monoˡ; ∗-comm;
  ∗-assocˡ; ∗-assocʳ; ∗?-comm; -∗-applyˡ; ⤇-intro)
open import Syho.Logic.Names using ([]ᴺ-⊆--∗)

-- Import and re-export
open import Syho.Logic.Judg public using ([_]⇛_; _⊢[_][_]⇛_; _⊢[<_][_]⇛_;
  _⊢[_][_]⇛ᴺ_; _⊢[<_][_]⇛ᴺ_; ⇛-ṡ; ⤇⇒⇛; _ᵘ»ᵘ_; ⇛-frameˡ)

private variable
  ι :  𝕊
  i j :  ℕ
  P Q R S :  Prop∞
  Nm :  Name → Zoi

abstract

  -- Level increment

  -->  ⇛-ṡ :  P ⊢[< ι ][ i ]⇛ Q →  P ⊢[ ι ][ ṡ i ]⇛ Q

  ⇛-<ᵈ :  i <ᵈ j →  P ⊢[< ι ][ i ]⇛ Q →  P ⊢[ ι ][ j ]⇛ Q
  ⇛-<ᵈ ≤ᵈ-refl =  ⇛-ṡ
  ⇛-<ᵈ (≤ᵈṡ i<j') =  ⇛-ṡ ∘ ⇒< ∘ ⇛-<ᵈ i<j'

  ⇛-< :  i < j →  P ⊢[< ι ][ i ]⇛ Q →  P ⊢[ ι ][ j ]⇛ Q
  ⇛-< =  ⇛-<ᵈ ∘ ≤⇒≤ᵈ

  ⇛-≤ :  i ≤ j →  P ⊢[ ι ][ i ]⇛ Q →  P ⊢[ ι ][ j ]⇛ Q
  ⇛-≤ i≤j  with ≤⇒<≡ i≤j
  … | ĩ₀ i<j =  ⇛-< i<j ∘ ⇒<
  … | ĩ₁ refl =  id

  -- Reflexivity of ⇛

  -->  ⤇⇒⇛ :  ⤇ P ⊢[ ι ][ i ]⇛ P

  ⇛-intro :  P ⊢[ ι ][ i ]⇛ P
  ⇛-intro =  ⤇-intro » ⤇⇒⇛

  -- Lift ⊢ into ⊢⇛

  ⇒⇛ :  P ⊢[ ι ] Q →  P ⊢[ ι ][ i ]⇛ Q
  ⇒⇛ P⊢Q =  P⊢Q » ⇛-intro

  -- Compose ⇛

  -->  _ᵘ»ᵘ_ :  P ⊢[ ι ][ i ]⇛ Q →  Q ⊢[ ι ][ i ]⇛ R →  P ⊢[ ι ][ i ]⇛ R

  infixr -1 _ᵘ»_

  _ᵘ»_ :  P ⊢[ ι ][ i ]⇛ Q →  Q ⊢[ ι ] R →  P ⊢[ ι ][ i ]⇛ R
  P⊢⇛Q ᵘ» Q⊢R =  P⊢⇛Q ᵘ»ᵘ ⇒⇛ Q⊢R

  -- Frame for ⇛

  -->  ⇛-frameˡ :  P ⊢[ ι ][ i ]⇛ Q →  R ∗ P ⊢[ ι ][ i ]⇛ R ∗ Q

  ⇛-frameʳ :  P ⊢[ ι ][ i ]⇛ Q →  P ∗ R ⊢[ ι ][ i ]⇛ Q ∗ R
  ⇛-frameʳ P⊢⇛Q =  ∗-comm » ⇛-frameˡ P⊢⇛Q ᵘ» ∗-comm

  ⇛-frameˡʳ :  P ⊢[ ι ][ i ]⇛ Q →  R ∗ P ∗ S ⊢[ ι ][ i ]⇛ R ∗ Q ∗ S
  ⇛-frameˡʳ P⊢⇛Q =  ⇛-frameˡ $ ⇛-frameʳ P⊢⇛Q

  -- ⇛ into ⇛ᴺ

  ⇛⇒⇛ᴺ :  P ⊢[ ι ][ i ]⇛ Q →  P ⊢[ ι ][ i ]⇛ᴺ Q
  ⇛⇒⇛ᴺ =  ⇛-frameˡ

  -- Reflexivity of ⇛ᴺ

  ⇛ᴺ-refl :  P ⊢[ ι ][ i ]⇛ᴺ P
  ⇛ᴺ-refl =  ⇛-intro

  -- Lift a pure sequent into ⇛ᴺ

  ⇒⇛ᴺ :  P ⊢[ ι ] Q →  P ⊢[ ι ][ i ]⇛ᴺ Q
  ⇒⇛ᴺ P⊢Q =  ⇛⇒⇛ᴺ $ ⇒⇛ P⊢Q

  -- Compose with ⇛ᴺ

  infixr -1 _ᵘᴺ»ᵘᴺ_ _ᵘᴺ»_ _»ᵘᴺ_

  _ᵘᴺ»ᵘᴺ_ :  P ⊢[ ι ][ i ]⇛ᴺ Q →  Q ⊢[ ι ][ i ]⇛ᴺ R →  P ⊢[ ι ][ i ]⇛ᴺ R
  _ᵘᴺ»ᵘᴺ_ =  _ᵘ»ᵘ_

  _ᵘᴺ»_ :  P ⊢[ ι ][ i ]⇛ᴺ Q →  Q ⊢[ ι ] R →  P ⊢[ ι ][ i ]⇛ᴺ R
  P⊢⇛Q ᵘᴺ» Q⊢R =  P⊢⇛Q ᵘᴺ»ᵘᴺ ⇒⇛ᴺ Q⊢R

  _»ᵘᴺ_ :  P ⊢[ ι ] Q →  Q ⊢[ ι ][ i ]⇛ᴺ R →  P ⊢[ ι ][ i ]⇛ᴺ R
  P⊢Q »ᵘᴺ Q⊢⇛R =  ⇒⇛ᴺ P⊢Q ᵘᴺ»ᵘᴺ Q⊢⇛R

  -- Frame for ⇛ᴺ

  ⇛ᴺ-frameʳ :  P ⊢[ ι ][ i ]⇛ᴺ Q →  P ∗ R ⊢[ ι ][ i ]⇛ᴺ Q ∗ R
  ⇛ᴺ-frameʳ P⊢⇛Q =  ∗-assocʳ » ⇛-frameʳ P⊢⇛Q ᵘ» ∗-assocˡ

  ⇛ᴺ-frameˡ :  P ⊢[ ι ][ i ]⇛ᴺ Q →  R ∗ P ⊢[ ι ][ i ]⇛ᴺ R ∗ Q
  ⇛ᴺ-frameˡ P⊢⇛Q =  ∗-comm »ᵘᴺ ⇛ᴺ-frameʳ P⊢⇛Q ᵘᴺ» ∗-comm

  -- Turn ⇛ with a valid name set token into ⇛ᴺ

  ⇛✔⇒⇛ᴺ :  ✔ᶻ Nm →  [ Nm ]ᴺ ∗ P ⊢[ ι ][ i ]⇛ [ Nm ]ᴺ ∗ Q →  P ⊢[ ι ][ i ]⇛ᴺ Q
  ⇛✔⇒⇛ᴺ ✔Nm [Nm]∗P⊢⇛[Nm]∗Q =  ∗-monoˡ ([]ᴺ-⊆--∗ ✔Nm) » ∗?-comm »
    ⇛-frameʳ [Nm]∗P⊢⇛[Nm]∗Q ᵘ» ∗?-comm » ∗-monoˡ -∗-applyˡ
