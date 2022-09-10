--------------------------------------------------------------------------------
-- Semantic proposition
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Base where

open import Base.Level using (Level; _⊔ᴸ_; ṡᴸ_; 2ᴸ)
open import Base.Func using (_$_; _›_; _∘_; flip; id; const)
open import Base.Few using (⊤; ⊤₀; ⊥)
open import Base.Eq using (_≡_; _≡˙_; ◠˙_)
open import Base.Prod using (∑-syntax; ∑ᴵ-syntax; _×_; _,_; -,_; -ᴵ,_; π₀; π₁;
  uncurry; ∑-case)
open import Base.Sum using (_⊎_; ĩ₀_; ĩ₁_)
open import Base.Dec using (yes; no; upd˙; upd˙-self)
open import Base.Nat using (ℕ)
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ; Globᴱᴿᴬ˙; inj˙; ✓˙-respᴱ;
  inj˙-≈; inj˙-ε; inj˙-⌞⌟; inj˙-↝; upd˙-inj˙-↝)

open ERA Globᴱᴿᴬ using (Env; Res; _≈_; _⊑_; _✓_; _∙_; ε; ⌞_⌟; _↝_; ◠˜_; _◇˜_;
  ⊑-respˡ; ⊑-refl; ⊑-trans; ≈⇒⊑; ✓-resp; ✓-mono; ∙-mono; ∙-monoˡ; ∙-monoʳ;
  ∙-unitˡ; ∙-unitʳ; ∙-comm; ∙-assocˡ; ∙-assocʳ; ∙-incrˡ; ∙-incrʳ; ε-min;
  ⌞⌟-mono; ⌞⌟-decr; ⌞⌟-idem; ⌞⌟-unitˡ; ⌞⌟-∙)

private variable
  ł ł' :  Level
  X Y :  Set ł

--------------------------------------------------------------------------------
-- Propᵒ :  Semantic proposition

Propᵒ :  ∀ ł →  Set (2ᴸ ⊔ᴸ ṡᴸ ł)
Propᵒ ł =  Res →  Set ł

-- Monoᵒ Pᵒ :  Pᵒ is monotone over the resource

Monoᵒ :  Propᵒ ł →  Set (2ᴸ ⊔ᴸ ł)
Monoᵒ Pᵒ =  ∀{a b} →  a ⊑ b →  Pᵒ a →  Pᵒ b

private variable
  Pᵒ Qᵒ Rᵒ Sᵒ :  Propᵒ ł
  Pᵒ˙ Qᵒ˙ :  X →  Propᵒ ł
  a b :  Res
  b˙ :  X → Res
  E F G :  Env
  E˙ F˙ :  X →  Env
  FPᵒ˙ GPᵒ˙ :  X →  Env × Propᵒ ł
  GPᵒ˙˙ :  X →  Y →  Env × Propᵒ ł
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

  -- Introduce ∀ᵒ

  ∀ᵒ-intro :  (∀ x → Pᵒ ⊨ Qᵒ˙ x) →  Pᵒ ⊨ ∀ᵒ˙ Qᵒ˙
  ∀ᵒ-intro P⊨Qx Pa x =  P⊨Qx x Pa

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

  -- Monoᵒ for ⊎ᵒ

  ⊎ᵒ-Mono :  Monoᵒ Pᵒ →  Monoᵒ Qᵒ →  Monoᵒ (Pᵒ ⊎ᵒ Qᵒ)
  ⊎ᵒ-Mono MonoP _ a⊑b (ĩ₀ Pa) =  ĩ₀ (MonoP a⊑b Pa)
  ⊎ᵒ-Mono _ MonoQ a⊑b (ĩ₁ Qa) =  ĩ₁ (MonoQ a⊑b Qa)

--------------------------------------------------------------------------------
-- ⊤ᵒ ⊥ᵒ :  Truth and falsehood

⊤ᵒ ⊥ᵒ :  Propᵒ ł
⊤ᵒ _ =  ⊤
⊥ᵒ _ =  ⊥

--------------------------------------------------------------------------------
-- →ᵒ :  Implication

abstract

  infixr 5 _→ᵒ_
  _→ᵒ_ :  Propᵒ ł →  Propᵒ ł' →  Propᵒ (2ᴸ ⊔ᴸ ł ⊔ᴸ ł')
  (Pᵒ →ᵒ Qᵒ) a =  ∀ E b →  a ⊑ b →  E ✓ b →  Pᵒ b →  Qᵒ b

  -- Monoᵒ for →ᵒ

  →ᵒ-Mono :  Monoᵒ (Pᵒ →ᵒ Qᵒ)
  →ᵒ-Mono a⊑a' P→Qa _ _ a'⊑b E✓b Pᵒb =  P→Qa _ _ (⊑-trans a⊑a' a'⊑b) E✓b Pᵒb

  -- Monotonicity of →ᵒ

  →ᵒ-mono :  Pᵒ ⊨ Qᵒ →  Rᵒ ⊨ Sᵒ →  Qᵒ →ᵒ Rᵒ ⊨ Pᵒ →ᵒ Sᵒ
  →ᵒ-mono P⊨Q R⊨S Q→Ra _ _ a⊑b E✓b =  P⊨Q › Q→Ra _ _ a⊑b E✓b › R⊨S

  -- Introduce/eliminate →ᵒ

  →ᵒ-intro :  Monoᵒ Qᵒ →  Pᵒ ×ᵒ Qᵒ ⊨✓ Rᵒ →  Qᵒ ⊨ Pᵒ →ᵒ Rᵒ
  →ᵒ-intro MonoQ P×Q⊨✓R Qa _ _ a⊑b E✓b Pb =  P×Q⊨✓R E✓b (Pb , MonoQ a⊑b Qa)

  →ᵒ-elim :  Qᵒ ⊨✓ Pᵒ →ᵒ Rᵒ →  Pᵒ ×ᵒ Qᵒ ⊨✓ Rᵒ
  →ᵒ-elim Q⊨✓P→R E✓a (Pa , Qa) =  Q⊨✓P→R E✓a Qa _ _ ⊑-refl E✓a Pa

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

  ∗ᵒ-mono✓ʳ :  Pᵒ ⊨✓ Qᵒ →  Rᵒ ∗ᵒ Pᵒ ⊨✓ Rᵒ ∗ᵒ Qᵒ
  ∗ᵒ-mono✓ʳ P⊨✓Q E✓a =  ∗ᵒ-comm › ∗ᵒ-mono✓ˡ P⊨✓Q E✓a › ∗ᵒ-comm

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

  -- ∃ᵒ/ᴵ and ⊎ commute with ∗ᵒ

  ∃ᵒ∗ᵒ-out :  ∃ᵒ˙ Pᵒ˙ ∗ᵒ Qᵒ ⊨ ∃ᵒ x , Pᵒ˙ x ∗ᵒ Qᵒ
  ∃ᵒ∗ᵒ-out (-, -, b∙c⊑a , (-, Pxb) , Qc) =  -, -, -, b∙c⊑a , Pxb , Qc

  ∗ᵒ∃ᵒ-out :  Pᵒ ∗ᵒ ∃ᵒ˙ Qᵒ˙ ⊨ ∃ᵒ x , Pᵒ ∗ᵒ Qᵒ˙ x
  ∗ᵒ∃ᵒ-out (-, -, b∙c⊑a , Pb , (-, Qxc)) =  -, -, -, b∙c⊑a , Pb , Qxc

  ∃ᴵ∗ᵒ-out :  ∃ᴵ˙ Pᵒ˙ ∗ᵒ Qᵒ ⊨ ∃ᴵ x , Pᵒ˙ x ∗ᵒ Qᵒ
  ∃ᴵ∗ᵒ-out (-, -, b∙c⊑a , (-ᴵ, Pxb) , Qc) =  -ᴵ, -, -, b∙c⊑a , Pxb , Qc

  ∗ᵒ∃ᴵ-out :  Pᵒ ∗ᵒ ∃ᴵ˙ Qᵒ˙ ⊨ ∃ᴵ x , Pᵒ ∗ᵒ Qᵒ˙ x
  ∗ᵒ∃ᴵ-out (-, -, b∙c⊑a , Pb , (-ᴵ, Qxc)) =  -ᴵ, -, -, b∙c⊑a , Pb , Qxc

  ⊎ᵒ∗ᵒ-out :  (Pᵒ ⊎ᵒ Qᵒ) ∗ᵒ Rᵒ ⊨ (Pᵒ ∗ᵒ Rᵒ) ⊎ᵒ (Qᵒ ∗ᵒ Rᵒ)
  ⊎ᵒ∗ᵒ-out (-, -, b∙c⊑a , ĩ₀ Pb , Rc) =  ĩ₀ (-, -, b∙c⊑a , Pb , Rc)
  ⊎ᵒ∗ᵒ-out (-, -, b∙c⊑a , ĩ₁ Qb , Rc) =  ĩ₁ (-, -, b∙c⊑a , Qb , Rc)

  ∗ᵒ⊎ᵒ-out :  Pᵒ ∗ᵒ (Qᵒ ⊎ᵒ Rᵒ) ⊨ (Pᵒ ∗ᵒ Qᵒ) ⊎ᵒ (Pᵒ ∗ᵒ Rᵒ)
  ∗ᵒ⊎ᵒ-out (-, -, b∙c⊑a , Pb , ĩ₀ Qc) =  ĩ₀ (-, -, b∙c⊑a , Pb , Qc)
  ∗ᵒ⊎ᵒ-out (-, -, b∙c⊑a , Pb , ĩ₁ Rc) =  ĩ₁ (-, -, b∙c⊑a , Pb , Rc)

--------------------------------------------------------------------------------
-- -∗ᵒ :  Magic wand

abstract

  infixr 5 _-∗ᵒ_
  _-∗ᵒ_ :  Propᵒ ł →  Propᵒ ł' →  Propᵒ (2ᴸ ⊔ᴸ ł ⊔ᴸ ł')
  (Pᵒ -∗ᵒ Qᵒ) a =  ∀ E b c →  a ⊑ b →  E ✓ c ∙ b →  Pᵒ c →  Qᵒ (c ∙ b)

  -- Monoᵒ for -∗ᵒ

  -∗ᵒ-Mono :  Monoᵒ (Pᵒ -∗ᵒ Qᵒ)
  -∗ᵒ-Mono a⊑a' P-∗Qa _ _ _ a'⊑b E✓c∙b Pc =
    P-∗Qa _ _ _ (⊑-trans a⊑a' a'⊑b) E✓c∙b Pc

  -- Monotonicity of -∗ᵒ

  -∗ᵒ-mono :  Pᵒ ⊨ Qᵒ →  Rᵒ ⊨ Sᵒ →  Qᵒ -∗ᵒ Rᵒ ⊨ Pᵒ -∗ᵒ Sᵒ
  -∗ᵒ-mono P⊨Q R⊨S Q-∗Ra _ _ _ a⊑b E✓c∙b =
    P⊨Q › Q-∗Ra _ _ _ a⊑b E✓c∙b › R⊨S

  -∗ᵒ-monoˡ :  Pᵒ ⊨ Qᵒ →  Qᵒ -∗ᵒ Rᵒ ⊨ Pᵒ -∗ᵒ Rᵒ
  -∗ᵒ-monoˡ {Rᵒ = Rᵒ} P⊨Q =  -∗ᵒ-mono {Rᵒ = Rᵒ} P⊨Q id

  -∗ᵒ-monoʳ :  Pᵒ ⊨ Qᵒ →  Rᵒ -∗ᵒ Pᵒ ⊨ Rᵒ -∗ᵒ Qᵒ
  -∗ᵒ-monoʳ =  -∗ᵒ-mono id

  -- Introduce/eliminate -∗ᵒ

  -∗ᵒ-intro :  Pᵒ ∗ᵒ Qᵒ ⊨✓ Rᵒ →  Qᵒ ⊨ Pᵒ -∗ᵒ Rᵒ
  -∗ᵒ-intro P∗Q⊨✓R Qa _ _ _ a⊑b E✓c∙b Pc =
    P∗Q⊨✓R E✓c∙b (-, -, ∙-monoʳ a⊑b , Pc , Qa)

  -∗ᵒ-elim :  Monoᵒ Rᵒ →  Qᵒ ⊨✓ Pᵒ -∗ᵒ Rᵒ →  Pᵒ ∗ᵒ Qᵒ ⊨✓ Rᵒ
  -∗ᵒ-elim MonoR Q⊨✓P-∗R E✓a (-, -, b∙c⊑a , Pb , Qc) =  MonoR b∙c⊑a $ Q⊨✓P-∗R
    (✓-mono (⊑-trans ∙-incrˡ b∙c⊑a) E✓a) Qc _ _ _ ⊑-refl (✓-mono b∙c⊑a E✓a) Pb

  -∗ᵒ-apply :  Monoᵒ Qᵒ →  Pᵒ ∗ᵒ (Pᵒ -∗ᵒ Qᵒ) ⊨✓ Qᵒ
  -∗ᵒ-apply MonoQ =  -∗ᵒ-elim MonoQ λ _ → id

--------------------------------------------------------------------------------
-- ⤇ᵒ :  Update modality

abstract

  infix 8 ⤇ᵒ_
  ⤇ᵒ_ :  Propᵒ ł →  Propᵒ (2ᴸ ⊔ᴸ ł)
  (⤇ᵒ Pᵒ) a =  ∀ E c →  E ✓ a ∙ c →  ∑ b ,  E ✓ b ∙ c  ×  Pᵒ b

  -- Monoᵒ for ⤇ᵒ

  ⤇ᵒ-Mono :  Monoᵒ (⤇ᵒ Pᵒ)
  ⤇ᵒ-Mono a⊑a' ⤇Pa _ _ E✓a'∙c =  ⤇Pa _ _ $ ✓-mono (∙-monoˡ a⊑a') E✓a'∙c

  -- Monotonicity of ⤇ᵒ

  ⤇ᵒ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  ⤇ᵒ Pᵒ ⊨ ⤇ᵒ Qᵒ
  ⤇ᵒ-mono✓ P⊨✓Q ⤇Pa _ _ E✓a∙c  with ⤇Pa _ _ E✓a∙c
  … | -, E✓b∙c , Pb =  -, E✓b∙c , P⊨✓Q (✓-mono ∙-incrʳ E✓b∙c) Pb

  ⤇ᵒ-mono :  Pᵒ ⊨ Qᵒ →  ⤇ᵒ Pᵒ ⊨ ⤇ᵒ Qᵒ
  ⤇ᵒ-mono =  ⤇ᵒ-mono✓ ∘ ⊨⇒⊨✓

  -- Introduce ⤇ᵒ

  ⤇ᵒ-intro :  Pᵒ ⊨ ⤇ᵒ Pᵒ
  ⤇ᵒ-intro Pa _ _ E✓a∙c =  -, E✓a∙c , Pa

  -- Join ⤇ᵒs

  ⤇ᵒ-join :  ⤇ᵒ ⤇ᵒ Pᵒ ⊨ ⤇ᵒ Pᵒ
  ⤇ᵒ-join ⤇⤇Pa _ _ E✓a∙d  with ⤇⤇Pa _ _ E✓a∙d
  … | -, E✓b∙d , ⤇Pb  with ⤇Pb _ _ E✓b∙d
  …   | -, E✓c∙d , Pc =  -, E✓c∙d , Pc

  -- Let ⤇ᵒ eat a proposition under ∗ᵒ

  ⤇ᵒ-eatʳ :  ⤇ᵒ Pᵒ ∗ᵒ Qᵒ ⊨ ⤇ᵒ (Pᵒ ∗ᵒ Qᵒ)
  ⤇ᵒ-eatʳ (-, -, b∙c⊑a , ⤇Pb , Qc) _ _ E✓a∙e
    with ⤇Pb _ _ $ flip ✓-mono E✓a∙e $ ⊑-respˡ ∙-assocˡ $ ∙-monoˡ b∙c⊑a
  … | -, E✓d∙ce , Pd =  -, ✓-resp ∙-assocʳ E✓d∙ce , -, -, ⊑-refl , Pd , Qc

  ⤇ᵒ-eatˡ :  Pᵒ ∗ᵒ ⤇ᵒ Qᵒ ⊨ ⤇ᵒ (Pᵒ ∗ᵒ Qᵒ)
  ⤇ᵒ-eatˡ =  ∗ᵒ-comm › ⤇ᵒ-eatʳ › ⤇ᵒ-mono ∗ᵒ-comm

  -- Let ∃₁ _ go out of ⤇ᵒ

  ⤇ᵒ-∃ᵒ-out :  ⤇ᵒ (∃ᵒ _ ∈ X , Pᵒ) ⊨✓ ∃ᵒ _ ∈ X , ⤇ᵒ Pᵒ
  ⤇ᵒ-∃ᵒ-out E✓a ⤇∃XP .π₀ =
    let -, -, x , _ = ⤇∃XP _ _ $ ✓-resp (◠˜ ∙-unitʳ) E✓a in  x
  ⤇ᵒ-∃ᵒ-out _ ⤇∃XP .π₁ _ _ E✓a∙c =
    let -, E✓b∙c , -, Pb = ⤇∃XP _ _ E✓a∙c in  -, E✓b∙c , Pb

--------------------------------------------------------------------------------
-- ⤇ᴱ :  Environmental update modality

abstract

  infix 8 _⤇ᴱ_
  _⤇ᴱ_ :  ∀{X : Set ł'} →  Env →  (X → Env × Propᵒ ł) →  Propᵒ (2ᴸ ⊔ᴸ ł ⊔ᴸ ł')
  (E ⤇ᴱ FPᵒ˙) a =  ∀ c →  E ✓ a ∙ c →  ∑ x , ∑ b ,
    let (F , Pᵒ) = FPᵒ˙ x in  F ✓ b ∙ c  ×  Pᵒ b

  -- Monoᵒ for ⤇ᴱ

  ⤇ᴱ-Mono :  Monoᵒ (E ⤇ᴱ FPᵒ˙)
  ⤇ᴱ-Mono a⊑a' E⤇FPa _ E✓a'∙c =  E⤇FPa _ (✓-mono (∙-monoˡ a⊑a') E✓a'∙c)

  -- Monotonicity of ⤇ᴱ

  ⤇ᴱ-mono✓ :  (∀ x →  Pᵒ˙ x ⊨✓ Qᵒ˙ x) →
              E ⤇ᴱ (λ x → F˙ x , Pᵒ˙ x)  ⊨  E ⤇ᴱ λ x → F˙ x , Qᵒ˙ x
  ⤇ᴱ-mono✓ Px⊨✓Qx E⤇FPa _ E✓a∙c  with E⤇FPa _ E✓a∙c
  … | -, -, F✓b∙c , Pb =  -, -, F✓b∙c , Px⊨✓Qx _ (✓-mono ∙-incrʳ F✓b∙c) Pb

  ⤇ᴱ-mono :  (∀ x →  Pᵒ˙ x ⊨ Qᵒ˙ x) →
             E ⤇ᴱ (λ x → F˙ x , Pᵒ˙ x)  ⊨  E ⤇ᴱ λ x → F˙ x , Qᵒ˙ x
  ⤇ᴱ-mono =  ⤇ᴱ-mono✓ ∘ (⊨⇒⊨✓ ∘_)

  -- Update the environment of ⤇ᴱ

  ⤇ᴱ-respᴱˡ :  E ≡˙ F →  E ⤇ᴱ GPᵒ˙ ⊨ F ⤇ᴱ GPᵒ˙
  ⤇ᴱ-respᴱˡ E≡F E⤇GP _ F✓a∙c =  E⤇GP _ (✓˙-respᴱ (◠˙ E≡F) F✓a∙c)

  ⤇ᴱ-respᴱʳ :  (∀{x} → E˙ x ≡˙ F˙ x) →
               G ⤇ᴱ (λ x → E˙ x , Pᵒ˙ x) ⊨ G ⤇ᴱ (λ x → F˙ x , Pᵒ˙ x)
  ⤇ᴱ-respᴱʳ Ex≡Fx G⤇EP _ G✓a∙c  with G⤇EP _ G✓a∙c
  … | -, -, E✓b∙c , Pb =  -, -, ✓˙-respᴱ Ex≡Fx E✓b∙c , Pb

  -- Change parameterization of ⤇ᴱ

  ⤇ᴱ-param :  E ⤇ᴱ FPᵒ˙ ∘ f  ⊨  E ⤇ᴱ FPᵒ˙
  ⤇ᴱ-param E⤇FPf _ E✓a∙c  with E⤇FPf _ E✓a∙c
  … | -, b,F✓b,Pb∙c =  -, b,F✓b,Pb∙c

  -- Introduce ⤇ᴱ

  ⤇ᵒ⇒⤇ᴱ :  ⤇ᵒ Pᵒ  ⊨  E ⤇ᴱ λ(_ : ⊤₀) → E , Pᵒ
  ⤇ᵒ⇒⤇ᴱ ⤇ᵒPa _ E✓a∙c  with ⤇ᵒPa _ _ E✓a∙c
  … | (-, E✓b∙c , Pb) =  -, -, E✓b∙c , Pb

  ⤇ᴱ-intro :  Pᵒ  ⊨  E ⤇ᴱ λ(_ : ⊤₀) → E , Pᵒ
  ⤇ᴱ-intro =  ⤇ᵒ-intro › ⤇ᵒ⇒⤇ᴱ

  -- Join ⤇ᴱs

  ⤇ᴱ-join :  E ⤇ᴱ (λ x → F˙ x , F˙ x ⤇ᴱ GPᵒ˙˙ x)  ⊨  E ⤇ᴱ uncurry GPᵒ˙˙
  ⤇ᴱ-join E⤇F,F⤇GPx _ E✓a∙d  with E⤇F,F⤇GPx _ E✓a∙d
  … | -, -, F✓b∙d , F⤇GPxb  with F⤇GPxb _ F✓b∙d
  …   | -, -, Gxy✓c∙d , Pxyc =  -, -, Gxy✓c∙d , Pxyc

  -- Let ⤇ᴱ eat a proposition under ∗ᵒ

  ⤇ᴱ-eatʳ :  E ⤇ᴱ (λ x → F˙ x , Pᵒ˙ x)  ∗ᵒ  Qᵒ  ⊨  E ⤇ᴱ λ x → F˙ x , Pᵒ˙ x ∗ᵒ Qᵒ
  ⤇ᴱ-eatʳ (-, -, b∙c⊑a , E⤇FPb , Qc) _ E✓a∙e
    with E⤇FPb _ $ flip ✓-mono E✓a∙e $ ⊑-respˡ ∙-assocˡ $ ∙-monoˡ b∙c⊑a
  … | -, -, F✓d∙ce , Pd =
    -, -, ✓-resp ∙-assocʳ F✓d∙ce , -, -, ⊑-refl , Pd , Qc

  ⤇ᴱ-eatˡ :  Pᵒ  ∗ᵒ  E ⤇ᴱ (λ x → F˙ x , Qᵒ˙ x)  ⊨  E ⤇ᴱ λ x → F˙ x , Pᵒ ∗ᵒ Qᵒ˙ x
  ⤇ᴱ-eatˡ =  ∗ᵒ-comm › ⤇ᴱ-eatʳ › ⤇ᴱ-mono λ _ → ∗ᵒ-comm

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

  -- Duplicate □ᵒ Pᵒ

  dup-□ᵒ :  Monoᵒ Pᵒ →  □ᵒ Pᵒ ⊨ □ᵒ Pᵒ ∗ᵒ □ᵒ Pᵒ
  dup-□ᵒ MonoP =  (λ Pa → Pa , Pa) › □ᵒˡ-×ᵒ⇒∗ᵒ MonoP

  -- □ᵒ commutes with ∗ᵒ

  □ᵒ-∗ᵒ-out :  Monoᵒ Pᵒ →  Monoᵒ Qᵒ → □ᵒ (Pᵒ ∗ᵒ Qᵒ) ⊨ □ᵒ Pᵒ ∗ᵒ □ᵒ Qᵒ
  □ᵒ-∗ᵒ-out MonoP MonoQ (-, -, b∙c⊑⌞a⌟ , Pb , Qc) =  □ᵒˡ-×ᵒ⇒∗ᵒ MonoP
    (MonoP (⊑-trans ∙-incrʳ b∙c⊑⌞a⌟) Pb , MonoQ (⊑-trans ∙-incrˡ b∙c⊑⌞a⌟) Qc)

  □ᵒ-∗ᵒ-in :  □ᵒ Pᵒ ∗ᵒ □ᵒ Qᵒ ⊨ □ᵒ (Pᵒ ∗ᵒ Qᵒ)
  □ᵒ-∗ᵒ-in(-, -, b∙c⊑a , P⌞b⌟ , Q⌞c⌟) =
    -, -, ⊑-trans ⌞⌟-∙ (⌞⌟-mono b∙c⊑a) , P⌞b⌟ , Q⌞c⌟

--------------------------------------------------------------------------------
-- ◎ :  Own a resource

abstract

  infix 8 ◎_
  ◎_ :  Res →  Propᵒ 2ᴸ
  (◎ a) b =  a ⊑ b

  -- Monoᵒ for ◎

  ◎-Mono :  Monoᵒ (◎ a)
  ◎-Mono b⊑c a⊑b =  ⊑-trans a⊑b b⊑c

  -- Modify the resource of ◎

  ◎-cong :  a ≈ b →  ◎ a ⊨ ◎ b
  ◎-cong a≈b a⊑c =  ⊑-respˡ a≈b a⊑c

  ◎-mono :  b ⊑ a →  ◎ a ⊨ ◎ b
  ◎-mono b⊑a a⊑c =  ⊑-trans b⊑a a⊑c

  -- Get ◎ ε

  ◎-ε :  ⊨ ◎ ε
  ◎-ε =  ε-min

  ◎-≈ε :  a ≈ ε →  ⊨ ◎ a
  ◎-≈ε a≈ε =  ◎-cong (◠˜ a≈ε) ◎-ε

  -- ◎ (a ∙ b) agrees with ◎ a ∗ᵒ ◎ b

  ◎-∙⇒∗ᵒ :  ◎ (a ∙ b) ⊨ ◎ a ∗ᵒ ◎ b
  ◎-∙⇒∗ᵒ a∙b⊑c =  -, -, a∙b⊑c , ⊑-refl , ⊑-refl

  ◎-∗ᵒ⇒∙ :  ◎ a ∗ᵒ ◎ b ⊨ ◎ (a ∙ b)
  ◎-∗ᵒ⇒∙ (-, -, a'∙b'⊑c , a⊑a' , b⊑b') =  ⊑-trans (∙-mono a⊑a' b⊑b') a'∙b'⊑c

  -- ◎ a is persistent when ⌞ a ⌟ agrees with a

  ◎-⌞⌟≈-□ᵒ :  ⌞ a ⌟ ≈ a →  ◎ a ⊨ □ᵒ ◎ a
  ◎-⌞⌟≈-□ᵒ ⌞a⌟≈a a⊑b =  ⊑-respˡ ⌞a⌟≈a $ ⌞⌟-mono a⊑b

  -- ↝ into ⤇ᵒ on ◎

  ↝-◎-⤇ᵒ-∃ᵒ :  (∀{E} →  (E , a)  ↝  λ x → E , b˙ x) →
               ◎ a  ⊨  ⤇ᵒ (∃ᵒ x , ◎ b˙ x)
  ↝-◎-⤇ᵒ-∃ᵒ Ea↝Ebx a⊑a' _ _ E✓a'∙c  with Ea↝Ebx _ $ ✓-mono (∙-monoˡ a⊑a') E✓a'∙c
  … | -, E✓bx∙c =  -, E✓bx∙c , -, ⊑-refl

  -- ↝ into ⤇ᴱ on ◎

  ↝-◎-⤇ᴱ :  ((E , a)  ↝  λ x → F˙ x , b˙ x) →
            ◎ a  ⊨  E  ⤇ᴱ  λ x → F˙ x , ◎ b˙ x
  ↝-◎-⤇ᴱ Ea↝Fxbx a⊑a' _ E✓a'∙c  with Ea↝Fxbx _ $ ✓-mono (∙-monoˡ a⊑a') E✓a'∙c
  … | -, Fx✓bx∙c =  -, -, Fx✓bx∙c , ⊑-refl

-- On an independent ERA

module _ {i : ℕ} where

  open ERA (Globᴱᴿᴬ˙ i) using () renaming (Res to Resⁱ; Env to Envⁱ;
    _≈_ to _≈ⁱ_; ε to εⁱ; ⌞_⌟ to ⌞_⌟ⁱ; _↝_ to _↝ⁱ_; ≡⇒≈ to ≡⇒≈ⁱ)

  private variable
    Fⁱ˙ :  X → Envⁱ
    aⁱ bⁱ :  Resⁱ
    aⁱ˙ bⁱ˙ :  X → Resⁱ

  abstract

    -- ◎ inj˙ i aⁱ is persistent when ⌞ aⁱ ⌟ agrees with aⁱ

    ◎-inj˙-⌞⌟≈-□ᵒ :  ⌞ aⁱ ⌟ⁱ ≈ⁱ aⁱ →  ◎ inj˙ i aⁱ ⊨ □ᵒ ◎ inj˙ i aⁱ
    ◎-inj˙-⌞⌟≈-□ᵒ ⌞a⌟≈a =  ◎-⌞⌟≈-□ᵒ $ inj˙-⌞⌟ ◇˜ inj˙-≈ ⌞a⌟≈a

    ◎-inj˙-⌞⌟≡-□ᵒ :  ⌞ aⁱ ⌟ⁱ ≡ aⁱ →  ◎ inj˙ i aⁱ ⊨ □ᵒ ◎ inj˙ i aⁱ
    ◎-inj˙-⌞⌟≡-□ᵒ ⌞a⌟≡a =  ◎-inj˙-⌞⌟≈-□ᵒ (≡⇒≈ⁱ ⌞a⌟≡a)

    -- ↝ⁱ into ⤇ᵒ on ◎ inj˙

    ↝-◎-inj˙-⤇ᵒ-∃ᵒ :  (∀{Eⁱ} →  (Eⁱ , aⁱ)  ↝ⁱ  λ x → Eⁱ , bⁱ˙ x) →
                      ◎ inj˙ i aⁱ  ⊨  ⤇ᵒ (∃ᵒ x , ◎ inj˙ i (bⁱ˙ x))
    ↝-◎-inj˙-⤇ᵒ-∃ᵒ Ea↝Ebx =  ↝-◎-⤇ᵒ-∃ᵒ $ inj˙-↝ Ea↝Ebx

    ε↝-◎-inj˙-⤇ᵒ-∃ᵒ :  (∀{Eⁱ} →  (Eⁱ , εⁱ)  ↝ⁱ  λ x → Eⁱ , aⁱ˙ x) →
                       ⊨  ⤇ᵒ (∃ᵒ x , ◎ inj˙ i (aⁱ˙ x))
    ε↝-◎-inj˙-⤇ᵒ-∃ᵒ Eε↝Eax =  ↝-◎-inj˙-⤇ᵒ-∃ᵒ Eε↝Eax $ ◎-≈ε $ inj˙-ε

    ↝-◎-inj˙-⤇ᵒ :  (∀{Eⁱ} →  (Eⁱ , aⁱ)  ↝ⁱ  λ (_ : ⊤₀) → Eⁱ , bⁱ) →
                   ◎ inj˙ i aⁱ  ⊨  ⤇ᵒ ◎ inj˙ i bⁱ
    ↝-◎-inj˙-⤇ᵒ Ea↝Eb =  ↝-◎-inj˙-⤇ᵒ-∃ᵒ Ea↝Eb › ⤇ᵒ-mono π₁

    ε↝-◎-inj˙-⤇ᵒ :  (∀{Eⁱ} →  (Eⁱ , εⁱ)  ↝ⁱ  λ (_ : ⊤₀) → Eⁱ , aⁱ) →
                    ⊨  ⤇ᵒ ◎ inj˙ i aⁱ
    ε↝-◎-inj˙-⤇ᵒ Eε↝Ea =  ⤇ᵒ-mono π₁ $ ε↝-◎-inj˙-⤇ᵒ-∃ᵒ Eε↝Ea

    -- ↝ⁱ into ⤇ᴱ on ◎ inj˙

    ↝-◎-inj˙-⤇ᴱ :  ((E i , aⁱ)  ↝ⁱ  λ x → Fⁱ˙ x , bⁱ˙ x) →
      ◎ inj˙ i aⁱ  ⊨  E  ⤇ᴱ  λ x → upd˙ i (Fⁱ˙ x) E , ◎ inj˙ i (bⁱ˙ x)
    ↝-◎-inj˙-⤇ᴱ Ea↝Fxbx =  ↝-◎-⤇ᴱ $ upd˙-inj˙-↝ Ea↝Fxbx

    ε↝-◎-inj˙-⤇ᴱ :  ((E i , εⁱ)  ↝ⁱ  λ x → Fⁱ˙ x , aⁱ˙ x) →
                    ⊨  E  ⤇ᴱ  λ x → upd˙ i (Fⁱ˙ x) E , ◎ inj˙ i (aⁱ˙ x)
    ε↝-◎-inj˙-⤇ᴱ Eε↝Fax =  ↝-◎-inj˙-⤇ᴱ Eε↝Fax $ ◎-≈ε $ inj˙-ε
