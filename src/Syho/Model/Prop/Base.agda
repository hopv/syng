--------------------------------------------------------------------------------
-- Semantic proposition
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Base where

open import Base.Level using (Level; _⊔ᴸ_; 2ᴸ; sucᴸ)
open import Base.Func using (_$_; _›_; _∘_; flip; const)
open import Base.Few using (⊤; ⊤₀)
open import Base.Prod using (∑-syntax; ∑ᴵ-syntax; _×_; _,_; -,_; -ᴵ,_; proj₀;
  proj₁)
open import Base.Sum using (_⊎_; inj₀; inj₁)
open import Base.Nat using (ℕ)
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ; Globᴱᴿᴬ˙; updᴱᴳ; injᴳ; injᴳ-↝;
  updᴱᴳ-injᴳ-↝; injᴳ-ε)

open ERA Globᴱᴿᴬ using (Env; Res; _≈_; _⊑_; _✓_; _∙_; ε; ⌞_⌟; _↝_; ◠˜_; ⊑-respˡ;
  ⊑-refl; ⊑-trans; ≈⇒⊑; ✓-resp; ✓-mono; ∙-mono; ∙-monoˡ; ∙-monoʳ; ∙-unitˡ;
  ∙-comm; ∙-assocˡ; ∙-assocʳ; ∙-incrˡ; ∙-incrʳ; ε-min; ⌞⌟-mono; ⌞⌟-decr;
  ⌞⌟-idem; ⌞⌟-unitˡ)

private variable
  ł ł' :  Level
  X Y :  Set ł

--------------------------------------------------------------------------------
-- Propᵒ :  Semantic proposition

Propᵒ :  ∀ ł →  Set (2ᴸ ⊔ᴸ sucᴸ ł)
Propᵒ ł =  Res →  Set ł

-- Monoᵒ Pᵒ :  Pᵒ is monotone over the resource

Monoᵒ :  Propᵒ ł →  Set (2ᴸ ⊔ᴸ ł)
Monoᵒ Pᵒ =  ∀{a b} →  a ⊑ b →  Pᵒ a →  Pᵒ b

private variable
  Pᵒ P'ᵒ Qᵒ Q'ᵒ Rᵒ Sᵒ :  Propᵒ ł
  Pᵒ˙ Qᵒ˙ :  X →  Propᵒ ł
  a b :  Res
  b˙ :  X → Res
  E F :  Env
  F˙ :  X →  Env
  FPᵒ˙ FQᵒ˙ GPᵒ˙ :  X →  Env × Propᵒ ł
  f :  Y → X

--------------------------------------------------------------------------------
-- ⊨✓, ⊨ :  Entailment, with or without a validity input

infix 1 _⊨✓_ _⊨_ ⊨_

_⊨✓_ _⊨_ :  Propᵒ ł →  Propᵒ ł' →  Set (2ᴸ ⊔ᴸ ł ⊔ᴸ ł')
Pᵒ ⊨✓ Qᵒ =  ∀{E a} →  E ✓ a →  Pᵒ a →  Qᵒ a
Pᵒ ⊨ Qᵒ =  ∀{a} →  Pᵒ a →  Qᵒ a

-- Tautology

⊨_ :  Propᵒ ł →  Set (2ᴸ ⊔ᴸ ł)
⊨ Pᵒ =  ∀{a} →  Pᵒ a

abstract

  ⊨⇒⊨✓ :  Pᵒ ⊨ Qᵒ →  Pᵒ ⊨✓ Qᵒ
  ⊨⇒⊨✓ P⊨Q _ =  P⊨Q

--------------------------------------------------------------------------------
-- ∀ᵒ, ∃ᵒ, ∃ᴵ :  Universal/existential quantification

∀ᵒ˙ ∃ᵒ˙ ∃ᴵ˙ ∀ᵒ∈-syntax ∃ᵒ∈-syntax ∃ᴵ∈-syntax ∀ᵒ-syntax ∃ᵒ-syntax ∃ᴵ-syntax :
  ∀{X : Set ł} →  (X → Propᵒ ł') →  Propᵒ (ł ⊔ᴸ ł')
∀ᵒ˙ Pᵒ˙ a =  ∀ x →  Pᵒ˙ x a
∃ᵒ˙ Pᵒ˙ a =  ∑ x ,  Pᵒ˙ x a
∃ᴵ˙ Pᵒ˙ a =  ∑ᴵ x ,  Pᵒ˙ x a
∀ᵒ∈-syntax =  ∀ᵒ˙
∃ᵒ∈-syntax =  ∃ᵒ˙
∃ᴵ∈-syntax =  ∃ᴵ˙
∀ᵒ-syntax =  ∀ᵒ˙
∃ᵒ-syntax =  ∃ᵒ˙
∃ᴵ-syntax =  ∃ᴵ˙
infix 3 ∀ᵒ∈-syntax ∃ᵒ∈-syntax ∃ᴵ∈-syntax ∀ᵒ-syntax ∃ᵒ-syntax ∃ᴵ-syntax
syntax ∀ᵒ∈-syntax {X = X} (λ x → Pᵒ) =  ∀ᵒ x ∈ X , Pᵒ
syntax ∃ᵒ∈-syntax {X = X} (λ x → Pᵒ) =  ∃ᵒ x ∈ X , Pᵒ
syntax ∃ᴵ∈-syntax {X = X} (λ x → Pᵒ) =  ∃ᴵ x ∈ X , Pᵒ
syntax ∀ᵒ-syntax (λ x → Pᵒ) =  ∀ᵒ x , Pᵒ
syntax ∃ᵒ-syntax (λ x → Pᵒ) =  ∃ᵒ x , Pᵒ
syntax ∃ᴵ-syntax (λ x → Pᵒ) =  ∃ᴵ x , Pᵒ

abstract

  -- Monoᵒ for ∀ᵒ/∃ᵒ/∃ᴵ

  ∀ᵒ-Mono :  (∀ x → Monoᵒ (Pᵒ˙ x)) →  Monoᵒ (∀ᵒ˙ Pᵒ˙)
  ∀ᵒ-Mono ∀MonoP a⊑b ∀Pa x =  ∀MonoP x a⊑b (∀Pa x)

  ∃ᵒ-Mono :  (∀ x → Monoᵒ (Pᵒ˙ x)) →  Monoᵒ (∃ᵒ˙ Pᵒ˙)
  ∃ᵒ-Mono ∀MonoP a⊑b (x , Pa) =  x , ∀MonoP x a⊑b Pa

  ∃ᴵ-Mono :  (∀{{x}} → Monoᵒ (Pᵒ˙ x)) →  Monoᵒ (∃ᴵ˙ Pᵒ˙)
  ∃ᴵ-Mono ∀MonoP a⊑b (-ᴵ, Pa) =  -ᴵ, ∀MonoP a⊑b Pa

  -- Monotonicity of ∀ᵒ/∃ᵒ/∃ᴵ

  ∀ᵒ-mono :  (∀ x → Pᵒ˙ x ⊨ Qᵒ˙ x) →  ∀ᵒ˙ Pᵒ˙ ⊨ ∀ᵒ˙ Qᵒ˙
  ∀ᵒ-mono Px⊨Qx ∀Pa x =  Px⊨Qx x (∀Pa x)

  ∃ᵒ-mono :  (∀ x → Pᵒ˙ x ⊨ Qᵒ˙ x) →  ∃ᵒ˙ Pᵒ˙ ⊨ ∃ᵒ˙ Qᵒ˙
  ∃ᵒ-mono Px⊨Qx (x , Pxa) =  x , Px⊨Qx x Pxa

  ∃ᴵ-mono :  (∀{{x}} → Pᵒ˙ x ⊨ Qᵒ˙ x) →  ∃ᴵ˙ Pᵒ˙ ⊨ ∃ᴵ˙ Qᵒ˙
  ∃ᴵ-mono Px⊨Qx (-ᴵ, Pxa) =  -ᴵ, Px⊨Qx Pxa

--------------------------------------------------------------------------------
-- ⌜⌝ᵒ :  Set embedding

⌜_⌝ᵒ :  Set ł →  Propᵒ ł
⌜ X ⌝ᵒ _ =  X

--------------------------------------------------------------------------------
-- ×ᵒ :  Conjunction

infixr 7 _×ᵒ_
_×ᵒ_ :  Propᵒ ł →  Propᵒ ł' →  Propᵒ (ł ⊔ᴸ ł')
(Pᵒ ×ᵒ Qᵒ) a =  Pᵒ a × Qᵒ a

--------------------------------------------------------------------------------
-- ⊎ᵒ :  Disjunction

infix 7 _⊎ᵒ_
_⊎ᵒ_ :  Propᵒ ł →  Propᵒ ł' →  Propᵒ (ł ⊔ᴸ ł')
(Pᵒ ⊎ᵒ Qᵒ) a =  Pᵒ a ⊎ Qᵒ a

abstract

  -- Monoᵒ on ⊎ᵒ

  ⊎ᵒ-Mono :  Monoᵒ Pᵒ →  Monoᵒ Qᵒ →  Monoᵒ (Pᵒ ⊎ᵒ Qᵒ)
  ⊎ᵒ-Mono MonoP _ a⊑b (inj₀ Pa) =  inj₀ $ MonoP a⊑b Pa
  ⊎ᵒ-Mono _ MonoQ a⊑b (inj₁ Qa) =  inj₁ $ MonoQ a⊑b Qa

--------------------------------------------------------------------------------
-- ⊤ᵒ :  Truthhood

⊤ᵒ :  Propᵒ ł
⊤ᵒ _ =  ⊤

--------------------------------------------------------------------------------
-- →ᵒ :  Implication

infixr 5 _→ᵒ_
_→ᵒ_ :  Propᵒ ł →  Propᵒ ł' →  Propᵒ (2ᴸ ⊔ᴸ ł ⊔ᴸ ł')
(Pᵒ →ᵒ Qᵒ) a =  ∀{E b} →  a ⊑ b →  E ✓ b →  Pᵒ b →  Qᵒ b

abstract

  -- Monoᵒ for →ᵒ

  →ᵒ-Mono :  Monoᵒ (Pᵒ →ᵒ Qᵒ)
  →ᵒ-Mono a⊑a' P→Qa a'⊑b E✓b Pᵒb =  P→Qa (⊑-trans a⊑a' a'⊑b) E✓b Pᵒb

  -- Monotonicity of →ᵒ

  →ᵒ-mono :  P'ᵒ ⊨ Pᵒ →  Qᵒ ⊨ Q'ᵒ →  (Pᵒ →ᵒ Qᵒ) ⊨ (P'ᵒ →ᵒ Q'ᵒ)
  →ᵒ-mono P⊨P Q⊨Q' P→Qa a⊑b E✓b P'b =  Q⊨Q' $ P→Qa a⊑b E✓b $ P⊨P P'b

  -- Introduce/eliminate →ᵒ

  →ᵒ-intro :  Monoᵒ Qᵒ →  Pᵒ ×ᵒ Qᵒ ⊨✓ Rᵒ →  Qᵒ ⊨ Pᵒ →ᵒ Rᵒ
  →ᵒ-intro MonoQ P×Q⊨✓R Qa a⊑b E✓b Pb =  P×Q⊨✓R E✓b (Pb , MonoQ a⊑b Qa)

  →ᵒ-elim :  Qᵒ ⊨✓ Pᵒ →ᵒ Rᵒ →  Pᵒ ×ᵒ Qᵒ ⊨✓ Rᵒ
  →ᵒ-elim Q⊨✓P→R E✓a (Pa , Qa) =  Q⊨✓P→R E✓a Qa ⊑-refl E✓a Pa

--------------------------------------------------------------------------------
-- ∗ᵒ :  Separating conjunction

infixr 7 _∗ᵒ_
_∗ᵒ_ :  Propᵒ ł →  Propᵒ ł' →  Propᵒ (2ᴸ ⊔ᴸ ł ⊔ᴸ ł')
(Pᵒ ∗ᵒ Qᵒ) a =  ∑ b , ∑ c ,  b ∙ c ⊑ a  ×  Pᵒ b  ×  Qᵒ c

abstract

  -- Monoᵒ for ∗ᵒ

  ∗ᵒ-Mono :  Monoᵒ (Pᵒ ∗ᵒ Qᵒ)
  ∗ᵒ-Mono a⊑a' (-, -, b∙c⊑a , PbQc) =  -, -, ⊑-trans b∙c⊑a a⊑a' , PbQc

  -- ∗ᵒ is commutative

  ∗ᵒ-comm :  Pᵒ ∗ᵒ Qᵒ ⊨ Qᵒ ∗ᵒ Pᵒ
  ∗ᵒ-comm (-, -, b∙c⊑a , Pb , Qc) =  -, -, ⊑-respˡ ∙-comm b∙c⊑a , Qc , Pb

  -- Monotonicity of ∗ᵒ

  ∗ᵒ-mono✓ˡ :  Pᵒ ⊨✓ Qᵒ →  Pᵒ ∗ᵒ Rᵒ ⊨✓ Qᵒ ∗ᵒ Rᵒ
  ∗ᵒ-mono✓ˡ P⊨✓Q E✓a (-, -, b∙c⊑a , Pb , Rc) =
    -, -, b∙c⊑a , P⊨✓Q (✓-mono (⊑-trans ∙-incrʳ b∙c⊑a) E✓a) Pb , Rc

  ∗ᵒ-monoˡ :  Pᵒ ⊨ Qᵒ →  Pᵒ ∗ᵒ Rᵒ ⊨ Qᵒ ∗ᵒ Rᵒ
  ∗ᵒ-monoˡ P⊨Q (-, -, b∙c⊑a , Pb , Rc) =  -, -, b∙c⊑a , P⊨Q Pb , Rc

  ∗ᵒ-monoʳ :  Pᵒ ⊨ Qᵒ →  Rᵒ ∗ᵒ Pᵒ ⊨ Rᵒ ∗ᵒ Qᵒ
  ∗ᵒ-monoʳ P⊨Q =  ∗ᵒ-comm › ∗ᵒ-monoˡ P⊨Q › ∗ᵒ-comm

  ∗ᵒ-mono :  Pᵒ ⊨ Qᵒ →  Rᵒ ⊨ Sᵒ →  Pᵒ ∗ᵒ Rᵒ ⊨ Qᵒ ∗ᵒ Sᵒ
  ∗ᵒ-mono P⊨Q R⊨S =  ∗ᵒ-monoˡ P⊨Q › ∗ᵒ-monoʳ R⊨S

  -- ∗ᵒ is associative

  ∗ᵒ-assocˡ :  (Pᵒ ∗ᵒ Qᵒ) ∗ᵒ Rᵒ ⊨ Pᵒ ∗ᵒ (Qᵒ ∗ᵒ Rᵒ)
  ∗ᵒ-assocˡ (-, -, e∙d⊑a , (-, -, b∙c⊑e , Pb , Qc) , Rd) =
    -, -, ⊑-respˡ ∙-assocˡ $ ⊑-trans (∙-monoˡ b∙c⊑e) e∙d⊑a , Pb ,
    -, -, ⊑-refl , Qc , Rd

  ∗ᵒ-assocʳ :  Pᵒ ∗ᵒ (Qᵒ ∗ᵒ Rᵒ) ⊨ (Pᵒ ∗ᵒ Qᵒ) ∗ᵒ Rᵒ
  ∗ᵒ-assocʳ =
    ∗ᵒ-comm › ∗ᵒ-monoˡ ∗ᵒ-comm › ∗ᵒ-assocˡ › ∗ᵒ-comm › ∗ᵒ-monoˡ ∗ᵒ-comm

  -- Shuffle ∗ᵒ

  pullʳˡᵒ :  Pᵒ ∗ᵒ Qᵒ ∗ᵒ Rᵒ ⊨ Qᵒ ∗ᵒ Pᵒ ∗ᵒ Rᵒ
  pullʳˡᵒ =  ∗ᵒ-assocʳ › ∗ᵒ-monoˡ ∗ᵒ-comm › ∗ᵒ-assocˡ

  -- Eliminate ∗ᵒ

  ∗ᵒ-elimʳ :  Monoᵒ Pᵒ →  Qᵒ ∗ᵒ Pᵒ ⊨ Pᵒ
  ∗ᵒ-elimʳ MonoP (-, -, b∙c⊑a , -, Pc) =  MonoP (⊑-trans ∙-incrˡ b∙c⊑a) Pc

  ∗ᵒ-elimˡ :  Monoᵒ Pᵒ →  Pᵒ ∗ᵒ Qᵒ ⊨ Pᵒ
  ∗ᵒ-elimˡ MonoP =  ∗ᵒ-comm › ∗ᵒ-elimʳ MonoP

  -- Introduce ∗ᵒ with a trivial proposition

  ?∗ᵒ-intro :  ⊨ Qᵒ →  Pᵒ ⊨ Qᵒ ∗ᵒ Pᵒ
  ?∗ᵒ-intro ⊨Q Pa =  -, -, ≈⇒⊑ ∙-unitˡ , ⊨Q , Pa

  ∗ᵒ?-intro :  ⊨ Qᵒ →  Pᵒ ⊨ Pᵒ ∗ᵒ Qᵒ
  ∗ᵒ?-intro ⊨Q =  ?∗ᵒ-intro ⊨Q › ∗ᵒ-comm

--------------------------------------------------------------------------------
-- -∗ᵒ :  Magic wand

infixr 5 _-∗ᵒ_
_-∗ᵒ_ :  Propᵒ ł →  Propᵒ ł' →  Propᵒ (2ᴸ ⊔ᴸ ł ⊔ᴸ ł')
(Pᵒ -∗ᵒ Qᵒ) a =  ∀{E b c} →  a ⊑ b →  E ✓ c ∙ b →  Pᵒ c → Qᵒ (c ∙ b)

abstract

  -- Monoᵒ for -∗ᵒ

  -∗ᵒ-Mono :  Monoᵒ (Pᵒ -∗ᵒ Qᵒ)
  -∗ᵒ-Mono a⊑a' P-∗Qa a'⊑b E✓c∙b Pc =  P-∗Qa (⊑-trans a⊑a' a'⊑b) E✓c∙b Pc

  -- Monotonicity of -∗ᵒ

  -∗ᵒ-mono :  P'ᵒ ⊨ Pᵒ →  Qᵒ ⊨ Q'ᵒ →  (Pᵒ -∗ᵒ Qᵒ) ⊨ (P'ᵒ -∗ᵒ Q'ᵒ)
  -∗ᵒ-mono P⊨P Q⊨Q' P-∗Qa a⊑b E✓c∙b P'c =  Q⊨Q' $ P-∗Qa a⊑b E✓c∙b $ P⊨P P'c

  -- Introduce/eliminate -∗ᵒ

  -∗ᵒ-intro :  Pᵒ ∗ᵒ Qᵒ ⊨✓ Rᵒ →  Qᵒ ⊨ Pᵒ -∗ᵒ Rᵒ
  -∗ᵒ-intro P∗Q⊨✓R Qa a⊑b E✓c∙b Pc =  P∗Q⊨✓R E✓c∙b (-, -, ∙-monoʳ a⊑b , Pc , Qa)

  -∗ᵒ-elim :  Monoᵒ Rᵒ →  Qᵒ ⊨✓ Pᵒ -∗ᵒ Rᵒ →  Pᵒ ∗ᵒ Qᵒ ⊨✓ Rᵒ
  -∗ᵒ-elim MonoR Q⊨✓P-∗R E✓a (-, -, b∙c⊑a , Pb , Qc) =  MonoR b∙c⊑a $
    Q⊨✓P-∗R (✓-mono (⊑-trans ∙-incrˡ b∙c⊑a) E✓a) Qc ⊑-refl (✓-mono b∙c⊑a E✓a) Pb

--------------------------------------------------------------------------------
-- ⤇ᵒ :  Update modality

infix 8 ⤇ᵒ_
⤇ᵒ_ :  Propᵒ ł →  Propᵒ (2ᴸ ⊔ᴸ ł)
(⤇ᵒ Pᵒ) a =  ∀ E c →  E ✓ c ∙ a →  ∑ b ,  E ✓ c ∙ b  ×  Pᵒ b

abstract

  -- Monoᵒ for ⤇ᵒ

  ⤇ᵒ-Mono :  Monoᵒ (⤇ᵒ Pᵒ)
  ⤇ᵒ-Mono a⊑a' ⤇Pa _ _ E✓c∙a' =  ⤇Pa _ _ $ ✓-mono (∙-monoʳ a⊑a') E✓c∙a'

  -- Monotonicity of ⤇ᵒ

  ⤇ᵒ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  ⤇ᵒ Pᵒ ⊨ ⤇ᵒ Qᵒ
  ⤇ᵒ-mono✓ P⊨✓Q ⤇Pa _ _ E✓c∙a  with ⤇Pa _ _ E✓c∙a
  ... | -, E✓c∙b , Pb =  -, E✓c∙b , P⊨✓Q (✓-mono ∙-incrˡ E✓c∙b) Pb

  ⤇ᵒ-mono :  Pᵒ ⊨ Qᵒ →  ⤇ᵒ Pᵒ ⊨ ⤇ᵒ Qᵒ
  ⤇ᵒ-mono =  ⤇ᵒ-mono✓ ∘ ⊨⇒⊨✓

  -- Introduce ⤇ᵒ

  ⤇ᵒ-intro :  Pᵒ ⊨ ⤇ᵒ Pᵒ
  ⤇ᵒ-intro Pa _ _ E✓c∙a =  -, E✓c∙a , Pa

  -- Join ⤇ᵒ ⤇ᵒ into ⤇ᵒ

  ⤇ᵒ-join :  ⤇ᵒ ⤇ᵒ Pᵒ ⊨ ⤇ᵒ Pᵒ
  ⤇ᵒ-join ⤇⤇Pa _ _ E✓d∙a  with ⤇⤇Pa _ _ E✓d∙a
  ... | -, E✓d∙b , ⤇Pb  with ⤇Pb _ _ E✓d∙b
  ...   | -, E✓d∙c , Pc =  -, E✓d∙c , Pc

  -- Let ⤇ᵒ eat a proposition under ∗ᵒ

  ⤇ᵒ-eatˡ :  Pᵒ ∗ᵒ ⤇ᵒ Qᵒ ⊨ ⤇ᵒ (Pᵒ ∗ᵒ Qᵒ)
  ⤇ᵒ-eatˡ (-, -, b∙c⊑a , Pb , ⤇Qc) _ _ E✓e∙a
    with ⤇Qc _ _ $ flip ✓-mono E✓e∙a $ ⊑-respˡ ∙-assocʳ $ ∙-monoʳ b∙c⊑a
  ... | -, E✓eb∙d , Qd =  -, ✓-resp ∙-assocˡ E✓eb∙d , -, -, ⊑-refl , Pb , Qd

  -- Let ∃₁ _ go out of ⤇ᵒ

  ⤇ᵒ-∃ᵒ-out :  ⤇ᵒ (∃ᵒ _ ∈ X , Pᵒ) ⊨✓ ∃ᵒ _ ∈ X , ⤇ᵒ Pᵒ
  ⤇ᵒ-∃ᵒ-out E✓a ⤇∃XP .proj₀ =
    let -, -, x , _ = ⤇∃XP _ _ $ ✓-resp (◠˜ ∙-unitˡ) E✓a in  x
  ⤇ᵒ-∃ᵒ-out _ ⤇∃XP .proj₁ _ _ E✓c∙a =
    let -, E✓c∙b , -, Pb = ⤇∃XP _ _ E✓c∙a in  -, E✓c∙b , Pb

--------------------------------------------------------------------------------
-- ⤇ᴱ :  Environmental update modality

infix 8 _⤇ᴱ_

_⤇ᴱ_ :  ∀{X : Set ł'} →  Env →  (X → Env × Propᵒ ł) →  Propᵒ (2ᴸ ⊔ᴸ ł ⊔ᴸ ł')
(E ⤇ᴱ FPᵒ˙) a =  ∀ c →  E ✓ c ∙ a →  ∑ x , ∑ b ,
  let (F , Pᵒ) = FPᵒ˙ x in  F ✓ c ∙ b  ×  Pᵒ b

abstract

  -- Monoᵒ for ⤇ᴱ

  ⤇ᴱ-Mono :  Monoᵒ (E ⤇ᴱ FPᵒ˙)
  ⤇ᴱ-Mono a⊑a' E⤇FPa _ E✓c∙a' =  E⤇FPa _ (✓-mono (∙-monoʳ a⊑a') E✓c∙a')

  -- Monotonicity of ⤇ᴱ

  ⤇ᴱ-mono✓ :  (∀ x →  Pᵒ˙ x ⊨✓ Qᵒ˙ x) →
              E ⤇ᴱ (λ x → F˙ x , Pᵒ˙ x)  ⊨  E ⤇ᴱ λ x → F˙ x , Qᵒ˙ x
  ⤇ᴱ-mono✓ Px⊨✓Qx E⤇FPa _ E✓c∙a  with E⤇FPa _ E✓c∙a
  ... | -, -, F✓c∙b , Pb =  -, -, F✓c∙b , Px⊨✓Qx _ (✓-mono ∙-incrˡ F✓c∙b) Pb

  ⤇ᴱ-mono :  (∀ x →  Pᵒ˙ x ⊨ Qᵒ˙ x) →
             E ⤇ᴱ (λ x → F˙ x , Pᵒ˙ x)  ⊨  E ⤇ᴱ λ x → F˙ x , Qᵒ˙ x
  ⤇ᴱ-mono =  ⤇ᴱ-mono✓ ∘ (⊨⇒⊨✓ ∘_)

  -- Change parameterization of ⤇ᴱ

  ⤇ᴱ-param :  E ⤇ᴱ FPᵒ˙ ∘ f  ⊨  E ⤇ᴱ FPᵒ˙
  ⤇ᴱ-param E⤇FPf _ E✓c∙a  with E⤇FPf _ E✓c∙a
  ... | -, ∑bF✓c∙b×Pb =  -, ∑bF✓c∙b×Pb

  -- Introduce ⤇ᴱ

  ⤇ᵒ⇒⤇ᴱ :  ⤇ᵒ Pᵒ  ⊨  E ⤇ᴱ λ(_ : ⊤₀) → E , Pᵒ
  ⤇ᵒ⇒⤇ᴱ ⤇ᵒPa _ E✓c∙a  with ⤇ᵒPa _ _ E✓c∙a
  ... | (-, E✓c∙b , Pb) =  -, -, E✓c∙b , Pb

  ⤇ᴱ-intro :  Pᵒ  ⊨  E ⤇ᴱ λ(_ : ⊤₀) → E , Pᵒ
  ⤇ᴱ-intro =  ⤇ᵒ-intro › ⤇ᵒ⇒⤇ᴱ

  -- Join ⤇ᴱ

  ⤇ᴱ-join :  E ⤇ᴱ (λ x → F˙ x , F˙ x ⤇ᴱ GPᵒ˙)  ⊨  E ⤇ᴱ GPᵒ˙
  ⤇ᴱ-join E⤇F,F⤇GP _ E✓d∙a  with E⤇F,F⤇GP _ E✓d∙a
  ... | -, -, F✓d∙b , F⤇GPb  with F⤇GPb _ F✓d∙b
  ...   | -, -, G✓d∙c , Pc =  -, -, G✓d∙c , Pc

  -- Let ⤇ᴱ eat a proposition under ∗ᵒ

  ⤇ᴱ-eatˡ :  Pᵒ  ∗ᵒ  E ⤇ᴱ (λ x → F˙ x , Qᵒ˙ x)  ⊨  E ⤇ᴱ λ x → F˙ x , Pᵒ ∗ᵒ Qᵒ˙ x
  ⤇ᴱ-eatˡ (-, -, b∙c⊑a , Pb , E⤇FQc) _ E✓e∙a
    with E⤇FQc _ $ flip ✓-mono E✓e∙a $ ⊑-respˡ ∙-assocʳ $ ∙-monoʳ b∙c⊑a
  ... | -, -, F✓eb∙d , Qd =
    -, -, ✓-resp ∙-assocˡ F✓eb∙d , -, -, ⊑-refl , Pb , Qd

  ⤇ᴱ-eatʳ :  E ⤇ᴱ (λ x → F˙ x , Pᵒ˙ x)  ∗ᵒ  Qᵒ  ⊨  E ⤇ᴱ λ x → F˙ x , Pᵒ˙ x ∗ᵒ Qᵒ
  ⤇ᴱ-eatʳ =  ∗ᵒ-comm › ⤇ᴱ-eatˡ › ⤇ᴱ-mono $ λ _ → ∗ᵒ-comm

--------------------------------------------------------------------------------
-- □ᵒ :  Persistence modality

infix 8 □ᵒ_
□ᵒ_ :  Propᵒ ł →  Propᵒ ł
(□ᵒ Pᵒ) a =  Pᵒ ⌞ a ⌟

abstract

  -- Monoᵒ for □ᵒ

  □ᵒ-Mono :  Monoᵒ Pᵒ →  Monoᵒ (□ᵒ Pᵒ)
  □ᵒ-Mono MonoP a⊑b P⌞a⌟ =  MonoP (⌞⌟-mono a⊑b) P⌞a⌟

  -- Monotonicity of □ᵒ

  □ᵒ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  □ᵒ Pᵒ ⊨✓ □ᵒ Qᵒ
  □ᵒ-mono✓ P⊨✓Q E✓a =  P⊨✓Q (✓-mono ⌞⌟-decr E✓a)

  □ᵒ-mono :  Pᵒ ⊨ Qᵒ →  □ᵒ Pᵒ ⊨ □ᵒ Qᵒ
  □ᵒ-mono P⊨Q =  P⊨Q

  -- Eliminate □ᵒ

  □ᵒ-elim :  Monoᵒ Pᵒ →  □ᵒ Pᵒ ⊨ Pᵒ
  □ᵒ-elim MonoP P⌞a⌟ =  MonoP ⌞⌟-decr P⌞a⌟

  -- Duplicate □ᵒ

  □ᵒ-dup :  Monoᵒ Pᵒ →  □ᵒ Pᵒ ⊨ □ᵒ □ᵒ Pᵒ
  □ᵒ-dup MonoP P⌞a⌟ =  MonoP (≈⇒⊑ $ ◠˜ ⌞⌟-idem) P⌞a⌟

  -- Change ×ᵒ into ∗ᵒ when one argument is under □ᵒ

  □ᵒˡ-×ᵒ⇒∗ᵒ :  Monoᵒ Pᵒ →  □ᵒ Pᵒ ×ᵒ Qᵒ ⊨ □ᵒ Pᵒ ∗ᵒ Qᵒ
  □ᵒˡ-×ᵒ⇒∗ᵒ MonoP (P⌞a⌟ , Qa) =  -, -, ≈⇒⊑ ⌞⌟-unitˡ ,
    MonoP (≈⇒⊑ $ ◠˜ ⌞⌟-idem) P⌞a⌟ , Qa

--------------------------------------------------------------------------------
-- ● :  ● a resource

infix 8 ●_
●_ :  Res →  Propᵒ 2ᴸ
(● a) b =  a ⊑ b

abstract

  -- Monoᵒ for ●

  ●-Mono :  Monoᵒ (● a)
  ●-Mono b⊑c a⊑b =  ⊑-trans a⊑b b⊑c

  -- Modify the resource of ●

  ●-cong :  a ≈ b →  ● a ⊨ ● b
  ●-cong a≈b a⊑c =  ⊑-respˡ a≈b a⊑c

  ●-mono :  b ⊑ a →  ● a ⊨ ● b
  ●-mono b⊑a a⊑c =  ⊑-trans b⊑a a⊑c

  -- Get ● by reflexivity

  ●-refl :  (● a) a
  ●-refl =  ⊑-refl

  ●-ε :  ⊨ ● ε
  ●-ε =  ε-min

  ●-≈ε :  a ≈ ε →  ⊨ ● a
  ●-≈ε a≈ε =  ●-cong (◠˜ a≈ε) ●-ε

  -- ● (a ∙ b) agrees with ● a ∗ᵒ ● b

  ●-∙⇒∗ᵒ :  ● (a ∙ b) ⊨ ● a ∗ᵒ ● b
  ●-∙⇒∗ᵒ a∙b⊑c =  -, -, a∙b⊑c , ⊑-refl , ⊑-refl

  ●-∗ᵒ⇒∙ :  ● a ∗ᵒ ● b ⊨ ● (a ∙ b)
  ●-∗ᵒ⇒∙ (-, -, a'∙b'⊑c , a⊑a' , b⊑b') =  ⊑-trans (∙-mono a⊑a' b⊑b') a'∙b'⊑c

  -- ● a is persistent when ⌞ a ⌟ agrees with a

  ●-⌞⌟≈-□ᵒ :  ⌞ a ⌟ ≈ a →  ● a ⊨ □ᵒ ● a
  ●-⌞⌟≈-□ᵒ ⌞a⌟≈a a⊑b =  ⊑-respˡ ⌞a⌟≈a $ ⌞⌟-mono a⊑b

  -- ↝ into ⤇ᵒ on ●

  ↝-●-⤇ᵒ-∃ᵒ :  (∀{E} →  (E , a)  ↝  λ x → E , b˙ x) →
               ● a  ⊨  ⤇ᵒ (∃ᵒ x , ● b˙ x)
  ↝-●-⤇ᵒ-∃ᵒ Ea↝Ebx a⊑a' _ _ E✓c∙a'  with Ea↝Ebx _ $ ✓-mono (∙-monoʳ a⊑a') E✓c∙a'
  ... | -, E✓c∙bx =  -, E✓c∙bx , -, ⊑-refl

  -- ↝ into ⤇ᴱ on ●

  ↝-●-⤇ᴱ :  ((E , a)  ↝  λ x → F˙ x , b˙ x) →
            ● a  ⊨  E  ⤇ᴱ  λ x → F˙ x , ● b˙ x
  ↝-●-⤇ᴱ Ea↝Fxbx a⊑a' _ E✓c∙a'  with Ea↝Fxbx _ $ ✓-mono (∙-monoʳ a⊑a') E✓c∙a'
  ... | -, Fx✓c∙bx =  -, -, Fx✓c∙bx , ⊑-refl

-- On an independent ERA

module _ {i : ℕ} where

  open ERA (Globᴱᴿᴬ˙ i) using () renaming (Res to Resⁱ; Env to Envⁱ; ε to εⁱ;
    _↝_ to _↝ⁱ_)

  private variable
    Fⁱ˙ :  X → Envⁱ
    aⁱ bⁱ :  Resⁱ
    aⁱ˙ bⁱ˙ :  X → Resⁱ

  abstract

    -- ↝ⁱ into ⤇ᵒ on ● injᴳ

    ↝-●-injᴳ-⤇ᵒ-∃ᵒ :  (∀{Eⁱ} →  (Eⁱ , aⁱ)  ↝ⁱ  λ x → Eⁱ , bⁱ˙ x) →
                      ● injᴳ i aⁱ  ⊨  ⤇ᵒ (∃ᵒ x , ● injᴳ i (bⁱ˙ x))
    ↝-●-injᴳ-⤇ᵒ-∃ᵒ Ea↝Ebx =  ↝-●-⤇ᵒ-∃ᵒ $ injᴳ-↝ Ea↝Ebx

    ε↝-●-injᴳ-⤇ᵒ-∃ᵒ :  (∀{Eⁱ} →  (Eⁱ , εⁱ)  ↝ⁱ  λ x → Eⁱ , aⁱ˙ x) →
                       ⊨  ⤇ᵒ (∃ᵒ x , ● injᴳ i (aⁱ˙ x))
    ε↝-●-injᴳ-⤇ᵒ-∃ᵒ Eε↝Eax =  ↝-●-injᴳ-⤇ᵒ-∃ᵒ Eε↝Eax $ ●-≈ε $ injᴳ-ε

    ↝-●-injᴳ-⤇ᵒ :  (∀{Eⁱ} →  (Eⁱ , aⁱ)  ↝ⁱ  λ (_ : ⊤₀) → Eⁱ , bⁱ) →
                   ● injᴳ i aⁱ  ⊨  ⤇ᵒ ● injᴳ i bⁱ
    ↝-●-injᴳ-⤇ᵒ Ea↝Eb =  ↝-●-injᴳ-⤇ᵒ-∃ᵒ Ea↝Eb › ⤇ᵒ-mono proj₁

    ε↝-●-injᴳ-⤇ᵒ :  (∀{Eⁱ} →  (Eⁱ , εⁱ)  ↝ⁱ  λ (_ : ⊤₀) → Eⁱ , aⁱ) →
                    ⊨  ⤇ᵒ ● injᴳ i aⁱ
    ε↝-●-injᴳ-⤇ᵒ Eε↝Ea =  ⤇ᵒ-mono proj₁ $ ε↝-●-injᴳ-⤇ᵒ-∃ᵒ Eε↝Ea

    -- ↝ⁱ into ⤇ᴱ on ● injᴳ

    ↝-●-injᴳ-⤇ᴱ :  ((E i , aⁱ)  ↝ⁱ  λ x → Fⁱ˙ x , bⁱ˙ x) →
      ● injᴳ i aⁱ  ⊨  E  ⤇ᴱ  λ x → updᴱᴳ i (Fⁱ˙ x) E , ● injᴳ i (bⁱ˙ x)
    ↝-●-injᴳ-⤇ᴱ Ea↝Fxbx =  ↝-●-⤇ᴱ $ updᴱᴳ-injᴳ-↝ Ea↝Fxbx

    ε↝-●-injᴳ-⤇ᴱ :  ((E i , εⁱ)  ↝ⁱ  λ x → Fⁱ˙ x , aⁱ˙ x) →
                    ⊨  E  ⤇ᴱ  λ x → updᴱᴳ i (Fⁱ˙ x) E , ● injᴳ i (aⁱ˙ x)
    ε↝-●-injᴳ-⤇ᴱ Eε↝Fax =  ↝-●-injᴳ-⤇ᴱ Eε↝Fax $ ●-≈ε $ injᴳ-ε
