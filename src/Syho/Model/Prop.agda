--------------------------------------------------------------------------------
-- Semantic proposition
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop where

open import Base.Prod using (∑-syntax; ∑∈-syntax; _×_; _,_; -,_; proj₀; proj₁)
open import Base.Func using (_$_; _›_; _∘_; flip)
open import Syho.Model.ERA using (ERA)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ)

open ERA Globᴱᴿᴬ using (Res; _⊑_; _✓_; _∙_; ε; ⌞_⌟; ◠˜_; ⊑-respˡ; ⊑-refl;
  ⊑-trans; ≈⇒⊑; ✓-respʳ; ✓-mono; ∙-monoˡ; ∙-monoʳ; ∙-unitˡ; ∙-comm; ∙-assocˡ;
  ∙-assocʳ; ∙-incrˡ; ∙-incrʳ; ⌞⌟-mono; ⌞⌟-decr; ⌞⌟-idem; ⌞⌟-unitˡ)

--------------------------------------------------------------------------------
-- Propᵒ :  Semantic proposition

Propᵒ :  Set₃
Propᵒ =  Res →  Set₂

-- Monoᵒ Pᵒ :  Pᵒ is monotone over the resource

Monoᵒ :  Propᵒ →  Set₂
Monoᵒ Pᵒ =  ∀{a b} →  a ⊑ b →  Pᵒ a →  Pᵒ b

private variable
  Pᵒ P'ᵒ Qᵒ Q'ᵒ Rᵒ Sᵒ :  Propᵒ
  X₁ :  Set₁
  Pᵒ˙ Qᵒ˙ :  X₁ →  Propᵒ
  a :  Res

--------------------------------------------------------------------------------
-- ⊨✓, ⊨ :  Entailment, with or without a validity input

infix 1 _⊨✓_ _⊨_
_⊨✓_ _⊨_ :  Propᵒ →  Propᵒ →  Set₂
Pᵒ ⊨✓ Qᵒ =  ∀{E a} →  E ✓ a →  Pᵒ a →  Qᵒ a
Pᵒ ⊨ Qᵒ =  ∀{a} →  Pᵒ a →  Qᵒ a

abstract

  ⊨⇒⊨✓ :  Pᵒ ⊨ Qᵒ →  Pᵒ ⊨✓ Qᵒ
  ⊨⇒⊨✓ P⊨Q _ =  P⊨Q

--------------------------------------------------------------------------------
-- ∀₁ᵒ, ∃₁ᵒ :  Universal/existential quantification

∀₁ᵒ˙ ∃₁ᵒ˙ ∀₁ᵒ∈-syntax ∃₁ᵒ∈-syntax ∀₁ᵒ-syntax ∃₁ᵒ-syntax :  (X₁ → Propᵒ) →  Propᵒ
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

abstract

  ∀₁ᵒ-Mono :  (∀ x → Monoᵒ (Pᵒ˙ x)) →  Monoᵒ (∀₁ᵒ˙ Pᵒ˙)
  ∀₁ᵒ-Mono ∀MonoP a⊑b ∀Pa x =  ∀MonoP x a⊑b (∀Pa x)

  ∃₁ᵒ-Mono :  (∀ x → Monoᵒ (Pᵒ˙ x)) →  Monoᵒ (∃₁ᵒ˙ Pᵒ˙)
  ∃₁ᵒ-Mono ∀MonoP a⊑b (x , Pa) =  x , ∀MonoP x a⊑b Pa

  ∀₁ᵒ-mono :  (∀ x → Pᵒ˙ x ⊨ Qᵒ˙ x) →  ∀₁ᵒ˙ Pᵒ˙ ⊨ ∀₁ᵒ˙ Qᵒ˙
  ∀₁ᵒ-mono Px⊨Qx ∀Pa x =  Px⊨Qx x (∀Pa x)

  ∃₁ᵒ-mono :  (∀ x → Pᵒ˙ x ⊨ Qᵒ˙ x) →  ∃₁ᵒ˙ Pᵒ˙ ⊨ ∃₁ᵒ˙ Qᵒ˙
  ∃₁ᵒ-mono Px⊨Qx (x , Pxa) =  x , Px⊨Qx x Pxa

--------------------------------------------------------------------------------
-- ×ᵒ :  Conjunction

infix 7 _×ᵒ_
_×ᵒ_ :  Propᵒ →  Propᵒ →  Propᵒ
(Pᵒ ×ᵒ Qᵒ) a =  Pᵒ a × Qᵒ a

--------------------------------------------------------------------------------
-- →ᵒ :  Implication

infixr 5 _→ᵒ_
_→ᵒ_ :  Propᵒ →  Propᵒ →  Propᵒ
(Pᵒ →ᵒ Qᵒ) a =  ∀{E b} →  a ⊑ b →  E ✓ b →  Pᵒ b →  Qᵒ b

abstract

  →ᵒ-Mono :  Monoᵒ (Pᵒ →ᵒ Qᵒ)
  →ᵒ-Mono a⊑a' P→Qa a'⊑b E✓b Pᵒb =  P→Qa (⊑-trans a⊑a' a'⊑b) E✓b Pᵒb

  →ᵒ-mono :  P'ᵒ ⊨ Pᵒ →  Qᵒ ⊨ Q'ᵒ →  (Pᵒ →ᵒ Qᵒ) ⊨ (P'ᵒ →ᵒ Q'ᵒ)
  →ᵒ-mono P'⊨P Q⊨Q' P→Qa a⊑b E✓b P'b =  Q⊨Q' $ P→Qa a⊑b E✓b $ P'⊨P P'b

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

  ∗ᵒ-Mono :  Monoᵒ (Pᵒ ∗ᵒ Qᵒ)
  ∗ᵒ-Mono a⊑a' (-, b∙c⊑a , PbQc) =  -, ⊑-trans b∙c⊑a a⊑a' , PbQc

  ∗ᵒ-mono✓ˡ :  Pᵒ ⊨✓ Qᵒ →  Pᵒ ∗ᵒ Rᵒ ⊨✓ Qᵒ ∗ᵒ Rᵒ
  ∗ᵒ-mono✓ˡ P⊨✓Q E✓a (-, b∙c⊑a , Pb , Rc) =
    -, b∙c⊑a , P⊨✓Q (✓-mono (⊑-trans ∙-incrʳ b∙c⊑a) E✓a) Pb , Rc

  ∗ᵒ-monoˡ :  Pᵒ ⊨ Qᵒ →  Pᵒ ∗ᵒ Rᵒ ⊨ Qᵒ ∗ᵒ Rᵒ
  ∗ᵒ-monoˡ P⊨Q (-, b∙c⊑a , Pb , Rc) =  -, b∙c⊑a , P⊨Q Pb , Rc

  ∗ᵒ-comm :  Pᵒ ∗ᵒ Qᵒ ⊨ Qᵒ ∗ᵒ Pᵒ
  ∗ᵒ-comm (-, b∙c⊑a , Pb , Qc) =  -, ⊑-respˡ ∙-comm b∙c⊑a , Qc , Pb

  ∗ᵒ-monoʳ :  Pᵒ ⊨ Qᵒ →  Rᵒ ∗ᵒ Pᵒ ⊨ Rᵒ ∗ᵒ Qᵒ
  ∗ᵒ-monoʳ P⊨Q =  ∗ᵒ-comm › ∗ᵒ-monoˡ P⊨Q › ∗ᵒ-comm

  ∗ᵒ-mono :  Pᵒ ⊨ Qᵒ →  Rᵒ ⊨ Sᵒ →  Pᵒ ∗ᵒ Rᵒ ⊨ Qᵒ ∗ᵒ Sᵒ
  ∗ᵒ-mono P⊨Q R⊨S =  ∗ᵒ-monoˡ P⊨Q › ∗ᵒ-monoʳ R⊨S

  ∗ᵒ-assocˡ :  (Pᵒ ∗ᵒ Qᵒ) ∗ᵒ Rᵒ ⊨ Pᵒ ∗ᵒ (Qᵒ ∗ᵒ Rᵒ)
  ∗ᵒ-assocˡ (-, e∙d⊑a , (-, b∙c⊑e , Pb , Qc) , Rd) =
    -, ⊑-respˡ ∙-assocˡ (⊑-trans (∙-monoˡ b∙c⊑e) e∙d⊑a) , Pb ,
    -, ⊑-refl , Qc , Rd

  ∗ᵒ-assocʳ :  Pᵒ ∗ᵒ (Qᵒ ∗ᵒ Rᵒ) ⊨ (Pᵒ ∗ᵒ Qᵒ) ∗ᵒ Rᵒ
  ∗ᵒ-assocʳ =
    ∗ᵒ-comm › ∗ᵒ-monoˡ ∗ᵒ-comm › ∗ᵒ-assocˡ › ∗ᵒ-comm › ∗ᵒ-monoˡ ∗ᵒ-comm

  ∗ᵒ-elimʳ :  Monoᵒ Pᵒ →  Qᵒ ∗ᵒ Pᵒ ⊨ Pᵒ
  ∗ᵒ-elimʳ MonoP (-, b∙c⊑a , -, Pc) =  MonoP (⊑-trans ∙-incrˡ b∙c⊑a) Pc

  ∗ᵒ-elimˡ :  Monoᵒ Pᵒ →  Pᵒ ∗ᵒ Qᵒ ⊨ Pᵒ
  ∗ᵒ-elimˡ MonoP =  ∗ᵒ-comm › ∗ᵒ-elimʳ MonoP

  ?∗ᵒ-intro :  Qᵒ ε →  Pᵒ ⊨ Qᵒ ∗ᵒ Pᵒ
  ?∗ᵒ-intro Qε Pa =  -, ≈⇒⊑ ∙-unitˡ , Qε , Pa

  ∗ᵒ?-intro :  Qᵒ ε →  Pᵒ ⊨ Pᵒ ∗ᵒ Qᵒ
  ∗ᵒ?-intro Qε =  ?∗ᵒ-intro Qε › ∗ᵒ-comm

--------------------------------------------------------------------------------
-- -∗ᵒ :  Magic wand

infixr 5 _-∗ᵒ_
_-∗ᵒ_ :  Propᵒ →  Propᵒ →  Propᵒ
(Pᵒ -∗ᵒ Qᵒ) a =  ∀{E b c} →  a ⊑ b →  E ✓ c ∙ b →  Pᵒ c → Qᵒ (c ∙ b)

abstract

  -∗ᵒ-Mono :  Monoᵒ (Pᵒ -∗ᵒ Qᵒ)
  -∗ᵒ-Mono a⊑a' P-∗Qa a'⊑b E✓c∙b Pc =  P-∗Qa (⊑-trans a⊑a' a'⊑b) E✓c∙b Pc

  -∗ᵒ-mono :  P'ᵒ ⊨ Pᵒ →  Qᵒ ⊨ Q'ᵒ →  (Pᵒ -∗ᵒ Qᵒ) ⊨ (P'ᵒ -∗ᵒ Q'ᵒ)
  -∗ᵒ-mono P'⊨P Q⊨Q' P-∗Qa a⊑b E✓c∙b P'c =  Q⊨Q' $ P-∗Qa a⊑b E✓c∙b $ P'⊨P P'c

  -∗ᵒ-intro :  Pᵒ ∗ᵒ Qᵒ ⊨✓ Rᵒ →  Qᵒ ⊨ Pᵒ -∗ᵒ Rᵒ
  -∗ᵒ-intro P∗Q⊨✓R Qa a⊑b E✓c∙b Pc =  P∗Q⊨✓R E✓c∙b $ -, ∙-monoʳ a⊑b , Pc , Qa

  -∗ᵒ-elim :  Monoᵒ Rᵒ →  Qᵒ ⊨✓ Pᵒ -∗ᵒ Rᵒ →  Pᵒ ∗ᵒ Qᵒ ⊨✓ Rᵒ
  -∗ᵒ-elim MonoR Q⊨✓P-∗R E✓a (-, b∙c⊑a , Pb , Qc) =  MonoR b∙c⊑a $
    Q⊨✓P-∗R (✓-mono (⊑-trans ∙-incrˡ b∙c⊑a) E✓a) Qc ⊑-refl (✓-mono b∙c⊑a E✓a) Pb

--------------------------------------------------------------------------------
-- ⤇ᵒ :  Update modality

infix 8 ⤇ᵒ_
⤇ᵒ_ :  Propᵒ →  Propᵒ
(⤇ᵒ Pᵒ) a =  ∀{E c} →  E ✓ c ∙ a →  ∑ b ,  E ✓ c ∙ b  ×  Pᵒ b

abstract

  ⤇ᵒ-Mono :  Monoᵒ (⤇ᵒ Pᵒ)
  ⤇ᵒ-Mono a⊑a' ⤇Pa E✓c∙a' =  ⤇Pa (✓-mono (∙-monoʳ a⊑a') E✓c∙a')

  ⤇ᵒ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  ⤇ᵒ Pᵒ ⊨ ⤇ᵒ Qᵒ
  ⤇ᵒ-mono✓ P⊨✓Q ⤇Pa E✓c∙a  with ⤇Pa E✓c∙a
  ... | -, E✓c∙b , Pb =  -, E✓c∙b , P⊨✓Q (✓-mono ∙-incrˡ E✓c∙b) Pb

  ⤇ᵒ-mono :  Pᵒ ⊨ Qᵒ →  ⤇ᵒ Pᵒ ⊨ ⤇ᵒ Qᵒ
  ⤇ᵒ-mono =  ⤇ᵒ-mono✓ ∘ ⊨⇒⊨✓

  ⤇ᵒ-intro :  Pᵒ ⊨ ⤇ᵒ Pᵒ
  ⤇ᵒ-intro Pa E✓c∙a =  -, E✓c∙a , Pa

  ⤇ᵒ-join :  ⤇ᵒ ⤇ᵒ Pᵒ ⊨ ⤇ᵒ Pᵒ
  ⤇ᵒ-join ⤇⤇Pa E✓d∙a  with ⤇⤇Pa E✓d∙a
  ... | -, E✓d∙b , ⤇Pb  with ⤇Pb E✓d∙b
  ...   | -, E✓d∙c , Pc =  -, E✓d∙c , Pc

  ⤇ᵒ-eatˡ :  Pᵒ ∗ᵒ ⤇ᵒ Qᵒ ⊨ ⤇ᵒ (Pᵒ ∗ᵒ Qᵒ)
  ⤇ᵒ-eatˡ (-, b∙c⊑a , Pb , ⤇Qc) E✓e∙a
    with ⤇Qc $ flip ✓-mono E✓e∙a $ ⊑-respˡ ∙-assocʳ $ ∙-monoʳ b∙c⊑a
  ... | -, E✓eb∙d , Qd =  -, ✓-respʳ ∙-assocˡ E✓eb∙d , -, ⊑-refl , Pb , Qd

  ⤇ᵒ-∃₁ᵒ-out :  ⤇ᵒ (∃₁ᵒ _ ∈ X₁ , Pᵒ) ⊨✓ ∃₁ᵒ _ ∈ X₁ , ⤇ᵒ Pᵒ
  ⤇ᵒ-∃₁ᵒ-out E✓a ⤇∃XP .proj₀ =
    let -, -, x , _ = ⤇∃XP $ ✓-respʳ (◠˜ ∙-unitˡ) E✓a in  x
  ⤇ᵒ-∃₁ᵒ-out _ ⤇∃XP .proj₁ E✓c∙a =
    let -, E✓c∙b , -, Pb = ⤇∃XP E✓c∙a in  -, E✓c∙b , Pb

--------------------------------------------------------------------------------
-- □ᵒ :  Persistence modality

infix 8 □ᵒ_
□ᵒ_ :  Propᵒ →  Propᵒ
(□ᵒ Pᵒ) a =  Pᵒ ⌞ a ⌟

abstract

  □ᵒ-Mono :  Monoᵒ Pᵒ →  Monoᵒ (□ᵒ Pᵒ)
  □ᵒ-Mono MonoP a⊑b P⌞a⌟ =  MonoP (⌞⌟-mono a⊑b) P⌞a⌟

  □ᵒ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  □ᵒ Pᵒ ⊨✓ □ᵒ Qᵒ
  □ᵒ-mono✓ P⊨✓Q E✓a =  P⊨✓Q (✓-mono ⌞⌟-decr E✓a)

  □ᵒ-mono :  Pᵒ ⊨ Qᵒ →  □ᵒ Pᵒ ⊨ □ᵒ Qᵒ
  □ᵒ-mono P⊨Q =  P⊨Q

  □ᵒ-elim :  Monoᵒ Pᵒ →  □ᵒ Pᵒ ⊨ Pᵒ
  □ᵒ-elim MonoP P⌞a⌟ =  MonoP ⌞⌟-decr P⌞a⌟

  □ᵒ-dup :  Monoᵒ Pᵒ →  □ᵒ Pᵒ ⊨ □ᵒ □ᵒ Pᵒ
  □ᵒ-dup MonoP P⌞a⌟ =  MonoP (≈⇒⊑ $ ◠˜ ⌞⌟-idem) P⌞a⌟

  □ᵒˡ-×ᵒ⇒∗ᵒ :  Monoᵒ Pᵒ →  □ᵒ Pᵒ ×ᵒ Qᵒ ⊨ □ᵒ Pᵒ ∗ᵒ Qᵒ
  □ᵒˡ-×ᵒ⇒∗ᵒ MonoP (P⌞a⌟ , Qa) =  -, ≈⇒⊑ ⌞⌟-unitˡ ,
    MonoP (≈⇒⊑ $ ◠˜ ⌞⌟-idem) P⌞a⌟ , Qa

--------------------------------------------------------------------------------
-- Own :  Own a resource

Own :  Res →  Propᵒ
Own a b =  a ⊑ b

abstract

  Own-Mono :  Monoᵒ (Own a)
  Own-Mono b⊑c a⊑b =  ⊑-trans a⊑b b⊑c
