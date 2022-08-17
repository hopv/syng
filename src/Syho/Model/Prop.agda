--------------------------------------------------------------------------------
-- Semantic proposition
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop where

open import Base.Prod using (∑-syntax; ∑∈-syntax; _×_; _,_; -,_)
open import Base.Func using (_$_; _▷_)
open import Syho.Model.ERA using (ERA)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ)

open ERA Globᴱᴿᴬ renaming (Res to Glob) using (_⊑_; _✓_; _∙_; ⌞_⌟; ◠˜_; ⊑-respˡ;
  ⊑-refl; ⊑-trans; ≈⇒⊑; ∙-monoˡ; ∙-comm; ∙-assocˡ; ⌞⌟-decr; ⌞⌟-idem)

--------------------------------------------------------------------------------
-- Propᵒ :  Semantic proposition

Propᵒ :  Set₃
Propᵒ =  Glob → Set₂

-- Monoᵒ Pᵒ :  Pᵒ is monotone over the resource

Monoᵒ :  Propᵒ →  Set₂
Monoᵒ Pᵒ =  ∀ {a b} →  a ⊑ b →  Pᵒ a →  Pᵒ b

private variable
  Pᵒ Qᵒ Rᵒ Sᵒ :  Propᵒ
  X₁ :  Set₁

--------------------------------------------------------------------------------
-- ⊨✓, ⊨ :  Entailment, with or without a validity input

infix 1 _⊨✓_ _⊨_
_⊨✓_ _⊨_ :  Propᵒ →  Propᵒ →  Set₂
Pᵒ ⊨✓ Qᵒ =  ∀ {E a} →  E ✓ a →  Pᵒ a →  Qᵒ a
Pᵒ ⊨ Qᵒ =  ∀ {a} →  Pᵒ a →  Qᵒ a

--------------------------------------------------------------------------------
-- Interpret ∀₁, ∃₁, →', ∗, -∗, |=>, □

∀₁ᵒ˙ ∃₁ᵒ˙ ∀₁ᵒ-syntax ∃₁ᵒ-syntax : (X₁ → Propᵒ) →  Propᵒ
∀₁ᵒ˙ Pᵒ˙ a =  ∀ x →  Pᵒ˙ x a
∃₁ᵒ˙ Pᵒ˙ a =  ∑ x ,  Pᵒ˙ x a
∀₁ᵒ-syntax =  ∀₁ᵒ˙
∃₁ᵒ-syntax =  ∃₁ᵒ˙
infix 3 ∀₁ᵒ-syntax ∃₁ᵒ-syntax
syntax ∀₁ᵒ-syntax (λ x → Pᵒ) =  ∀₁ᵒ x , Pᵒ
syntax ∃₁ᵒ-syntax (λ x → Pᵒ) =  ∃₁ᵒ x , Pᵒ

infixr 5 _→ᵒ_
_→ᵒ_ :  Propᵒ → Propᵒ → Propᵒ
(Pᵒ →ᵒ Qᵒ) a =  ∀ {E b} →  a ⊑ b →  E ✓ b →  Pᵒ b →  Qᵒ b

infixr 7 _∗ᵒ_
_∗ᵒ_ :  Propᵒ → Propᵒ → Propᵒ
(Pᵒ ∗ᵒ Qᵒ) a =  ∑ (b , c) ∈ _ × _ ,  b ∙ c ⊑ a  ×  Pᵒ b  ×  Qᵒ c

infixr 5 _-∗ᵒ_
_-∗ᵒ_ :  Propᵒ → Propᵒ → Propᵒ
(Pᵒ -∗ᵒ Qᵒ) a =  ∀ {E b c} →  a ⊑ b →  E ✓ c ∙ b →  Pᵒ c → Qᵒ (c ∙ b)

infix 8 |=>ᵒ_
|=>ᵒ_ :  Propᵒ → Propᵒ
(|=>ᵒ Pᵒ) a =  ∀ {E c} →  E ✓ c ∙ a →  ∑ b ,  E ✓ c ∙ b  ×  Pᵒ b

infix 8 □ᵒ_
□ᵒ_ :  Propᵒ → Propᵒ
(□ᵒ Pᵒ) a =  Pᵒ ⌞ a ⌟

--------------------------------------------------------------------------------
-- Lemmas

abstract

  ------------------------------------------------------------------------------
  -- On ∗ᵒ

  ∗ᵒ-monoˡ :  Pᵒ ⊨ Qᵒ →  Pᵒ ∗ᵒ Rᵒ ⊨ Qᵒ ∗ᵒ Rᵒ
  ∗ᵒ-monoˡ P⊨Q (-, b∙c⊑a , Pb , Rc) =  -, b∙c⊑a , P⊨Q Pb , Rc

  ∗ᵒ-comm :  Pᵒ ∗ᵒ Qᵒ ⊨ Qᵒ ∗ᵒ Pᵒ
  ∗ᵒ-comm (-, b∙c⊑a , Pb , Qc) =  -, ⊑-respˡ ∙-comm b∙c⊑a , Qc , Pb

  ∗ᵒ-monoʳ :  Pᵒ ⊨ Qᵒ →  Rᵒ ∗ᵒ Pᵒ ⊨ Rᵒ ∗ᵒ Qᵒ
  ∗ᵒ-monoʳ P⊨Q proof =  proof ▷ ∗ᵒ-comm ▷ ∗ᵒ-monoˡ P⊨Q ▷ ∗ᵒ-comm

  ∗ᵒ-mono :  Pᵒ ⊨ Qᵒ →  Rᵒ ⊨ Sᵒ →  Pᵒ ∗ᵒ Rᵒ ⊨ Qᵒ ∗ᵒ Sᵒ
  ∗ᵒ-mono P⊨Q R⊨S proof =  proof ▷ ∗ᵒ-monoˡ P⊨Q ▷ ∗ᵒ-monoʳ R⊨S

  ∗ᵒ-assocˡ :  (Pᵒ ∗ᵒ Qᵒ) ∗ᵒ Rᵒ ⊨ Pᵒ ∗ᵒ (Qᵒ ∗ᵒ Rᵒ)
  ∗ᵒ-assocˡ (-, e∙d⊑a , (-, b∙c⊑e , Pb , Qc) , Rd) =
    -, ⊑-respˡ ∙-assocˡ (⊑-trans (∙-monoˡ b∙c⊑e) e∙d⊑a) , Pb ,
    -, ⊑-refl , Qc , Rd

  ∗ᵒ-assocʳ :  Pᵒ ∗ᵒ (Qᵒ ∗ᵒ Rᵒ) ⊨ (Pᵒ ∗ᵒ Qᵒ) ∗ᵒ Rᵒ
  ∗ᵒ-assocʳ proof =  proof ▷
    ∗ᵒ-comm ▷ ∗ᵒ-monoˡ ∗ᵒ-comm ▷ ∗ᵒ-assocˡ ▷ ∗ᵒ-comm ▷ ∗ᵒ-monoˡ ∗ᵒ-comm

  ------------------------------------------------------------------------------
  -- On □

  □ᵒ-mono :  Pᵒ ⊨ Qᵒ →  □ᵒ Pᵒ ⊨ □ᵒ Qᵒ
  □ᵒ-mono P⊨Q =  P⊨Q

  □ᵒ-elim :  Monoᵒ Pᵒ →  □ᵒ Pᵒ ⊨ Pᵒ
  □ᵒ-elim MonoP P⌞a⌟ =  MonoP ⌞⌟-decr P⌞a⌟

  □ᵒ-dup :  Monoᵒ Pᵒ →  □ᵒ Pᵒ ⊨ □ᵒ □ᵒ Pᵒ
  □ᵒ-dup MonoP P⌞a⌟ =  MonoP (≈⇒⊑ $ ◠˜ ⌞⌟-idem) P⌞a⌟
