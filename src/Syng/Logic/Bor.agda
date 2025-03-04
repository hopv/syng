--------------------------------------------------------------------------------
-- Proof rules on the borrow
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syng.Logic.Bor where

open import Base.Func using (_$_)
open import Base.Size using (𝕊; !; ¡_; _$ᵀʰ_)
open import Base.Eq using (_≡_; refl)
open import Base.Prod using (_,_; -,_)
open import Base.Sum using (ĩ₁_)
open import Base.Nat using (ℕ)
open import Base.Ratp using (ℚ⁺)
open import Syng.Lang.Expr using (Addr; Type; V⇒E)
open import Syng.Lang.Ktxred using (Ktx; _ᴷ◁_)
open import Syng.Logic.Prop using (Lft; HorKind; SProp∞; SProp˂∞; ¡ᴾ_; ⌜_⌝∧_;
  _∗_; _↦⟨_⟩_; [_]ᴸ⟨_⟩; ⟨†_⟩_; &ᵐ⟨_⟩_; ⅋ᵐ⟨_⟩_; Basic)
open import Syng.Logic.Core using (_⊢[_]_; _⊢[<_]_; Pers; Pers-⇒□; ⇒<; _»_;
  ∗-monoˡ; ∗-monoʳ; ∗-comm; ∗-assocˡ; ∗-assocʳ; ?∗-comm; ∗?-comm; ⊤∗-intro;
  ∗-elimˡ; ∗-elimʳ; -∗-introˡ)
open import Syng.Logic.Fupd using (_⊢[_][_]⇛_; _ᵘ»ᵘ_; _ᵘ»_; ⇛-frameˡ; ⇛-frameʳ)

-- Import and re-export
open import Syng.Logic.Judg public using (&ᵐ-resp-□∗; ⅋ᵐ-respᴿ; ⅋ᵐ-monoᴾ;
  ⅋ᵐ-eatˡ; ⟨†⟩-mono; ⟨†⟩-eatˡ; &ᵐ-new; &ᵐ-open; ⅋ᵐ-close-sub; ⟨†⟩-back)

private variable
  ι :  𝕊
  i :  ℕ
  α :  Lft
  X :  Set₀
  P Q R :  SProp∞
  P˂ Q˂ :  SProp˂∞
  p :  ℚ⁺
  θ :  Addr
  T U :  Type
  v :  X
  K :  Ktx T U
  κ :  HorKind

abstract

  ------------------------------------------------------------------------------
  -- On the borrow

  -->  ⅋ᵐ-respᴿ :  p ≈ᴿ⁺ q  →   ⅋ᵐ⟨ α , p ⟩ P˂  ⊢[ ι ]  ⅋ᵐ⟨ α , q ⟩ P˂

  -->  ⅋ᵐ-monoᴾ :
  -->    Q˂ .!  ⊢[< ι ]  P˂ .!  →  ⅋ᵐ⟨ α , p ⟩ P˂  ⊢[ ι ]  ⅋ᵐ⟨ α , p ⟩ Q˂

  -->  ⅋ᵐ-eatˡ :  {{Basic Q}}  →
  -->    Q  ∗  ⅋ᵐ⟨ α , p ⟩ P˂  ⊢[ ι ]  ⅋ᵐ⟨ α , p ⟩ ¡ᴾ (Q -∗ P˂ .!)

  -->  ⟨†⟩-mono :  P˂ .!  ⊢[< ι ]  Q˂ .!  →   ⟨† α ⟩ P˂  ⊢[ ι ]  ⟨† α ⟩ Q˂

  -->  &ᵐ-new :  P˂ .!  ⊢[ ι ][ i ]⇛  &ᵐ⟨ α ⟩ P˂  ∗  ⟨† α ⟩ P˂

  -->  ⟨†⟩-back :  †ᴸ α  ∗  ⟨† α ⟩ P˂  ⊢[ ι ][ i ]⇛  P˂ .!

  -->  &ᵐ-open :
  -->    [ α ]ᴸ⟨ p ⟩  ∗  &ᵐ⟨ α ⟩ P˂  ⊢[ ι ][ i ]⇛  P˂ .!  ∗  ⅋ᵐ⟨ α , p ⟩ P˂

  -- Modify a mutable borrow token

  -->  &ᵐ-resp-□∗ :  {{Basic R}}  →
  -->    R  ∗  P˂ .!  ⊢[< ι ]  Q˂ .!  →   R  ∗  Q˂ .!  ⊢[< ι ]  P˂ .!  →
  -->    □ R  ∗  &ᵐ⟨ α ⟩ P˂  ⊢[ ι ]  &ᵐ⟨ α ⟩ Q˂

  &ᵐ-resp-∗ :  {{Pers R}}  →   {{Basic R}}  →
    R  ∗  P˂ .!  ⊢[< ι ]  Q˂ .!  →   R  ∗  Q˂ .!  ⊢[< ι ]  P˂ .!  →
    R  ∗  &ᵐ⟨ α ⟩ P˂  ⊢[ ι ]  &ᵐ⟨ α ⟩ Q˂
  &ᵐ-resp-∗ R∗P⊢Q R∗Q⊢P =  ∗-monoˡ Pers-⇒□ » &ᵐ-resp-□∗ R∗P⊢Q R∗Q⊢P

  &ᵐ-resp :  P˂ .!  ⊢[< ι ]  Q˂ .!  →   Q˂ .!  ⊢[< ι ]  P˂ .!  →
             &ᵐ⟨ α ⟩ P˂  ⊢[ ι ]  &ᵐ⟨ α ⟩ Q˂
  &ᵐ-resp P⊢Q Q⊢P =  ⊤∗-intro »
    &ᵐ-resp-∗ ((∗-elimʳ »_) $ᵀʰ P⊢Q) ((∗-elimʳ »_) $ᵀʰ Q⊢P)

  -- Let a lending token eat a basic proposition

  -->  ⟨†⟩-eatˡ :  {{Basic Q}}  →
  -->    Q  ∗  ⟨† α ⟩ P˂  ⊢[ ι ]  ⟨† α ⟩ ¡ᴾ (Q ∗ P˂ .!)

  ⟨†⟩-eatʳ :  {{Basic Q}}  →   ⟨† α ⟩ P˂  ∗  Q  ⊢[ ι ]  ⟨† α ⟩ ¡ᴾ (P˂ .! ∗ Q)
  ⟨†⟩-eatʳ =  ∗-comm » ⟨†⟩-eatˡ » ⟨†⟩-mono $ ⇒< ∗-comm

  -- Close an open mutable borrow token to retrieve a mutable borrow token

  -->  ⅋ᵐ-close-sub :
  -->    Q˂ .!  ∗  (Q˂ .! -∗ P˂ .!)  ∗  ⅋ᵐ⟨ α , p ⟩ P˂  ⊢[ ι ][ i ]⇛
  -->      [ α ]ᴸ⟨ p ⟩  ∗  &ᵐ⟨ α ⟩ Q˂

  ⅋ᵐ-close :  P˂ .!  ∗  ⅋ᵐ⟨ α , p ⟩ P˂  ⊢[ ι ][ i ]⇛  [ α ]ᴸ⟨ p ⟩  ∗  &ᵐ⟨ α ⟩ P˂
  ⅋ᵐ-close =  ∗-monoʳ (⊤∗-intro » ∗-monoˡ $ -∗-introˡ ∗-elimˡ) » ⅋ᵐ-close-sub

  -- Use a mutable borrow token

  &ᵐ-use :  P˂ .!  ∗  Q  ⊢[ ι ][ i ]⇛  P˂ .!  ∗  R  →
    [ α ]ᴸ⟨ p ⟩  ∗  &ᵐ⟨ α ⟩ P˂  ∗  Q  ⊢[ ι ][ i ]⇛
      [ α ]ᴸ⟨ p ⟩  ∗  &ᵐ⟨ α ⟩ P˂  ∗  R
  &ᵐ-use P∗Q⊢⇛P∗R =  ∗-assocˡ » ⇛-frameˡ &ᵐ-open ᵘ»ᵘ ∗?-comm »
    ⇛-frameˡ P∗Q⊢⇛P∗R ᵘ»ᵘ ∗-assocʳ » ?∗-comm » ⇛-frameʳ ⅋ᵐ-close ᵘ» ∗-comm »
    ∗-assocʳ
