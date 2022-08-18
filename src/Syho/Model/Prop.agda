--------------------------------------------------------------------------------
-- Semantic proposition
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop where

open import Base.Prod using (∑-syntax; ∑∈-syntax; _×_; _,_; -,_; proj₀; proj₁)
open import Base.Func using (_$_; _▷_; flip)
open import Syho.Model.ERA using (ERA)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ)

open ERA Globᴱᴿᴬ renaming (Res to Glob) using (_⊑_; _✓_; _∙_; ⌞_⌟; ◠˜_; ⊑-respˡ;
  ⊑-refl; ⊑-trans; ≈⇒⊑; ✓-respʳ; ✓-mono; ∙-monoˡ; ∙-monoʳ; ∙-unitˡ; ∙-comm;
  ∙-assocˡ; ∙-assocʳ; ∙-incrˡ; ⌞⌟-decr; ⌞⌟-idem)

--------------------------------------------------------------------------------
-- Propᵒ :  Semantic proposition

Propᵒ :  Set₃
Propᵒ =  Glob →  Set₂

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
-- ∀₁ᵒ, ∃₁ᵒ :  Universal/existential quantification

∀₁ᵒ˙ ∃₁ᵒ˙ ∀₁ᵒ∈-syntax ∃₁ᵒ∈-syntax ∀₁ᵒ-syntax ∃₁ᵒ-syntax :
  (X₁ → Propᵒ) →  Propᵒ
∀₁ᵒ˙ Pᵒ˙ a =  ∀ x →  Pᵒ˙ x a
∃₁ᵒ˙ Pᵒ˙ a =  ∑ x ,  Pᵒ˙ x a
∀₁ᵒ∈-syntax =  ∀₁ᵒ˙
∃₁ᵒ∈-syntax =  ∃₁ᵒ˙
∀₁ᵒ-syntax =  ∀₁ᵒ˙
∃₁ᵒ-syntax =  ∃₁ᵒ˙
infix 3 ∀₁ᵒ∈-syntax ∃₁ᵒ∈-syntax ∀₁ᵒ-syntax ∃₁ᵒ-syntax
syntax ∀₁ᵒ∈-syntax {X₁ = X₁} (λ x → Pᵒ) =  ∀₁ᵒ x ∈ X₁ , Pᵒ
syntax ∃₁ᵒ∈-syntax {X₁ = X₁} (λ x → Pᵒ) =  ∃₁ᵒ x ∈ X₁ , Pᵒ
syntax ∀₁ᵒ-syntax (λ x → Pᵒ) =  ∀₁ᵒ x , Pᵒ
syntax ∃₁ᵒ-syntax (λ x → Pᵒ) =  ∃₁ᵒ x , Pᵒ

--------------------------------------------------------------------------------
-- ×ᵒ :  Conjunction

infix 7 _×ᵒ_
_×ᵒ_ :  Propᵒ →  Propᵒ →  Propᵒ
(Pᵒ ×ᵒ Qᵒ) a =  Pᵒ a × Qᵒ a

--------------------------------------------------------------------------------
-- →ᵒ :  Implication

infixr 5 _→ᵒ_
_→ᵒ_ :  Propᵒ →  Propᵒ →  Propᵒ
(Pᵒ →ᵒ Qᵒ) a =  ∀ {E b} →  a ⊑ b →  E ✓ b →  Pᵒ b →  Qᵒ b

abstract

  →ᵒ-intro :  Monoᵒ Qᵒ →  Pᵒ ×ᵒ Qᵒ ⊨✓ Rᵒ →  Qᵒ ⊨ Pᵒ →ᵒ Rᵒ
  →ᵒ-intro MonoQ P×Q⊨✓R Qa a⊑b E✓b Pb =  P×Q⊨✓R E✓b (Pb , MonoQ a⊑b Qa)

  →ᵒ-elim :  Qᵒ ⊨✓ Pᵒ →ᵒ Rᵒ →  Pᵒ ×ᵒ Qᵒ ⊨✓ Rᵒ
  →ᵒ-elim Q⊨✓P→R E✓a (Pa , Qa) =  Q⊨✓P→R E✓a Qa ⊑-refl E✓a Pa

--------------------------------------------------------------------------------
-- ∗ᵒ :  Separating conjunction

infixr 7 _∗ᵒ_
_∗ᵒ_ :  Propᵒ →  Propᵒ →  Propᵒ
(Pᵒ ∗ᵒ Qᵒ) a =  ∑ (b , c) ∈ _ × _ ,  b ∙ c ⊑ a  ×  Pᵒ b  ×  Qᵒ c

abstract

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

  ∗ᵒ-elimʳ :  Monoᵒ Pᵒ →  Qᵒ ∗ᵒ Pᵒ ⊨ Pᵒ
  ∗ᵒ-elimʳ MonoP (-, b∙c⊑a , -, Pc) =  MonoP (⊑-trans ∙-incrˡ b∙c⊑a) Pc

--------------------------------------------------------------------------------
-- -∗ᵒ :  Magic wand

infixr 5 _-∗ᵒ_
_-∗ᵒ_ :  Propᵒ →  Propᵒ →  Propᵒ
(Pᵒ -∗ᵒ Qᵒ) a =  ∀ {E b c} →  a ⊑ b →  E ✓ c ∙ b →  Pᵒ c → Qᵒ (c ∙ b)

--------------------------------------------------------------------------------
-- ⇑ᵒ :  Update modality

infix 8 ⇑ᵒ_
⇑ᵒ_ :  Propᵒ →  Propᵒ
(⇑ᵒ Pᵒ) a =  ∀ {E c} →  E ✓ c ∙ a →  ∑ b ,  E ✓ c ∙ b  ×  Pᵒ b

abstract

  ⇑ᵒ-mono :  Pᵒ ⊨✓ Qᵒ →  ⇑ᵒ Pᵒ ⊨ ⇑ᵒ Qᵒ
  ⇑ᵒ-mono P⊨✓Q ⇑Pa E✓c∙a  with ⇑Pa E✓c∙a
  ... | -, E✓c∙b , Pb =  -, E✓c∙b , P⊨✓Q (✓-mono ∙-incrˡ E✓c∙b) Pb

  ⇑ᵒ-intro :  Pᵒ ⊨ ⇑ᵒ Pᵒ
  ⇑ᵒ-intro Pa E✓c∙a =  -, E✓c∙a , Pa

  ⇑ᵒ-join :  ⇑ᵒ ⇑ᵒ Pᵒ ⊨ ⇑ᵒ Pᵒ
  ⇑ᵒ-join ⇑⇑Pa E✓d∙a  with ⇑⇑Pa E✓d∙a
  ... | -, E✓d∙b , ⇑Pb  with ⇑Pb E✓d∙b
  ...   | -, E✓d∙c , Pc =  -, E✓d∙c , Pc

  ⇑ᵒ-eatˡ :  Pᵒ ∗ᵒ ⇑ᵒ Qᵒ ⊨ ⇑ᵒ (Pᵒ ∗ᵒ Qᵒ)
  ⇑ᵒ-eatˡ (-, b∙c⊑a , Pb , ⇑Qc) E✓e∙a
    with ⇑Qc $ flip ✓-mono E✓e∙a $ ⊑-respˡ ∙-assocʳ $ ∙-monoʳ b∙c⊑a
  ... | -, E✓eb∙d , Qd =  -, ✓-respʳ ∙-assocˡ E✓eb∙d , -, ⊑-refl , Pb , Qd

  ⇑ᵒ-∃₁ᵒ-out :  ⇑ᵒ (∃₁ᵒ _ ∈ X₁ , Pᵒ) ⊨✓ ∃₁ᵒ _ ∈ X₁ , ⇑ᵒ Pᵒ
  ⇑ᵒ-∃₁ᵒ-out E✓a ⇑∃XP .proj₀ =
    let -, -, x , _ = ⇑∃XP $ ✓-respʳ (◠˜ ∙-unitˡ) E✓a in  x
  ⇑ᵒ-∃₁ᵒ-out _ ⇑∃XP .proj₁ E✓c∙a =
    let -, E✓c∙b , -, Pb = ⇑∃XP E✓c∙a in  -, E✓c∙b , Pb

--------------------------------------------------------------------------------
-- □ᵒ :  Persistence modality

infix 8 □ᵒ_
□ᵒ_ :  Propᵒ →  Propᵒ
(□ᵒ Pᵒ) a =  Pᵒ ⌞ a ⌟

abstract

  □ᵒ-mono :  Pᵒ ⊨✓ Qᵒ →  □ᵒ Pᵒ ⊨✓ □ᵒ Qᵒ
  □ᵒ-mono P⊨✓Q E✓a =  P⊨✓Q (✓-mono ⌞⌟-decr E✓a)

  □ᵒ-elim :  Monoᵒ Pᵒ →  □ᵒ Pᵒ ⊨ Pᵒ
  □ᵒ-elim MonoP P⌞a⌟ =  MonoP ⌞⌟-decr P⌞a⌟

  □ᵒ-dup :  Monoᵒ Pᵒ →  □ᵒ Pᵒ ⊨ □ᵒ □ᵒ Pᵒ
  □ᵒ-dup MonoP P⌞a⌟ =  MonoP (≈⇒⊑ $ ◠˜ ⌞⌟-idem) P⌞a⌟
