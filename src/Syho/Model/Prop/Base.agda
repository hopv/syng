--------------------------------------------------------------------------------
-- Semantic proposition
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Base where

open import Base.Level using (Level; _⊔ᴸ_; ṡᴸ_; 0ᴸ; 1ᴸ)
open import Base.Func using (_$_; _›_; _∘_; flip; id; const)
open import Base.Few using (⊤; ⊤₀; ⊥)
open import Base.Eq using (_≡_; refl; ◠_; _≡˙_; ◠˙_)
open import Base.Dec using (yes; no; upd˙; upd˙-self)
open import Base.Size using (Size; Size<; Thunk; !; Shrunk; §_)
open import Base.Prod using (∑-syntax; ∑ᴵ-syntax; _×_; _,_; -,_; -ᴵ,_; π₀; π₁;
  curry; uncurry; ∑-case)
open import Base.Sum using (_⨿_; ĩ₀_; ĩ₁_)
open import Base.Nat using (ℕ)
open import Base.List using (List; []; _∷_; _$ᴸ_; _$ⁱᴸ_; _$ⁱᴸ⟨_⟩_)
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ; Globᴱᴿᴬ˙; Envᴳ; Resᴳ; Resᴳ˙;
  inj˙; ✓˙-respᴱ; inj˙-≈; inj˙-∙; inj˙-ε; inj˙-⌞⌟; inj˙-↝; upd˙-inj˙-↝; ✓-inj˙)

open ERA Globᴱᴿᴬ using (_≈_; _⊑_; _✓_; _∙_; ε; ⌞_⌟; _↝_; ◠˜_; _◇˜_;
  ⊑-respˡ; ⊑-refl; ⊑-trans; ≈⇒⊑; ✓-resp; ✓-mono; ∙-mono; ∙-monoˡ; ∙-monoʳ;
  ∙-unitˡ; ∙-unitʳ; ∙-comm; ∙-assocˡ; ∙-assocʳ; ∙-incrˡ; ∙-incrʳ; ε-min;
  ⌞⌟-mono; ⌞⌟-decr; ⌞⌟-idem; ⌞⌟-unitˡ; ⌞⌟-∙)

private variable
  ł ł' :  Level

--------------------------------------------------------------------------------
-- Propᵒ :  Semantic proposition

Propᵒ :  ∀ ł →  Set (1ᴸ ⊔ᴸ ṡᴸ ł)
Propᵒ ł =  Resᴳ →  Set ł

-- Monoᵒ Pᵒ :  Pᵒ is monotone over the resource

Monoᵒ :  Propᵒ ł →  Set (1ᴸ ⊔ᴸ ł)
Monoᵒ Pᵒ =  ∀{a b} →  a ⊑ b →  Pᵒ a →  Pᵒ b

private variable
  X Y :  Set ł
  Pᵒ Qᵒ Rᵒ Sᵒ :  Propᵒ ł
  Pᵒ˙ Qᵒ˙ :  X →  Propᵒ ł
  Pᵒs :  List (Propᵒ ł)
  a b :  Resᴳ
  b˙ :  X → Resᴳ
  E F G :  Envᴳ
  E˙ F˙ :  X →  Envᴳ
  FPᵒ˙ GPᵒ˙ FQᵒ˙ :  X →  Envᴳ × Propᵒ ł
  GPᵒ˙˙ :  X →  Y →  Envᴳ × Propᵒ ł
  f :  Y → X
  x y :  X
  xs ys :  List X
  ι :  Size
  Pᵒᶥ Qᵒᶥ :  Size →  Propᵒ ł

--------------------------------------------------------------------------------
-- ⊨✓, ⊨ :  Entailment

infix 1 _⊨✓_ _⊨_ ⊨_

-- Pᵒ ⊨✓ Qᵒ :  Entailment with a validity input
-- Pᵒ ⊨ Qᵒ :  Entailment

_⊨✓_ _⊨_ :  Propᵒ ł →  Propᵒ ł' →  Set (1ᴸ ⊔ᴸ ł ⊔ᴸ ł')
Pᵒ ⊨✓ Qᵒ =  ∀{E a} →  E ✓ a →  Pᵒ a →  Qᵒ a
Pᵒ ⊨ Qᵒ =  ∀{a} →  Pᵒ a →  Qᵒ a

-- ⊨ Pᵒ :  Tautology

⊨_ :  Propᵒ ł →  Set (1ᴸ ⊔ᴸ ł)
⊨ Pᵒ =  ∀{a} →  Pᵒ a

abstract

  -- ⊨ into ⊨✓

  ⊨⇒⊨✓ :  Pᵒ ⊨ Qᵒ →  Pᵒ ⊨✓ Qᵒ
  ⊨⇒⊨✓ P⊨Q _ =  P⊨Q

  -- Substitute a proposition

  substᵒ :  ∀(Pᵒ˙ : X → Propᵒ ł) →  x ≡ y →  Pᵒ˙ x ⊨ Pᵒ˙ y
  substᵒ Pᵒ˙ refl =  id

--------------------------------------------------------------------------------
-- ∀ᵒ, ∃ᵒ, ∃ᴵ :  Semantic universal/existential quantification

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

  ∀ᵒ-Mono :  (∀ x → Monoᵒ $ Pᵒ˙ x) →  Monoᵒ $ ∀ᵒ˙ Pᵒ˙
  ∀ᵒ-Mono ∀MonoP a⊑b ∀Pa x =  ∀MonoP x a⊑b (∀Pa x)

  ∃ᵒ-Mono :  (∀ x → Monoᵒ $ Pᵒ˙ x) →  Monoᵒ $ ∃ᵒ˙ Pᵒ˙
  ∃ᵒ-Mono ∀MonoP a⊑b (x , Pa) =  x , ∀MonoP x a⊑b Pa

  ∃ᴵ-Mono :  (∀{{x}} → Monoᵒ $ Pᵒ˙ x) →  Monoᵒ $ ∃ᴵ˙ Pᵒ˙
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
-- ⌜ ⌝ᵒ, ⌜ ⌝ᵒ×, ⌜ ⌝ᵒ→ :  Semantic set embedding

⌜_⌝ᵒ :  Set ł →  Propᵒ ł
⌜ X ⌝ᵒ _ =  X

infix 3 ⌜_⌝ᵒ×_ ⌜_⌝ᵒ→_
⌜_⌝ᵒ×_ ⌜_⌝ᵒ→_ :  Set ł →  Propᵒ ł' →  Propᵒ (ł ⊔ᴸ ł')
⌜ X ⌝ᵒ× Pᵒ =  ∃ᵒ _ ∈ X , Pᵒ
⌜ X ⌝ᵒ→ Pᵒ =  ∀ᵒ _ ∈ X , Pᵒ

abstract

  -- Monoᵒ for ⌜ ⌝ᵒ

  ⌜⌝ᵒ-Mono :  Monoᵒ $ ⌜ X ⌝ᵒ
  ⌜⌝ᵒ-Mono _ x =  x

--------------------------------------------------------------------------------
-- ×ᵒ :  Semantic conjunction

infixr 7 _×ᵒ_
_×ᵒ_ :  Propᵒ ł →  Propᵒ ł' →  Propᵒ (ł ⊔ᴸ ł')
(Pᵒ ×ᵒ Qᵒ) a =  Pᵒ a × Qᵒ a

abstract

  -- Monoᵒ for ×ᵒ

  ×ᵒ-Mono :  Monoᵒ Pᵒ →  Monoᵒ Qᵒ →  Monoᵒ $ Pᵒ ×ᵒ Qᵒ
  ×ᵒ-Mono MonoP MonoQ a⊑b (Pa , Qa) =  MonoP a⊑b Pa , MonoQ a⊑b Qa

--------------------------------------------------------------------------------
-- ⨿ᵒ :  Semantic disjunction

infixr 6 _⨿ᵒ_
_⨿ᵒ_ :  Propᵒ ł →  Propᵒ ł' →  Propᵒ (ł ⊔ᴸ ł')
(Pᵒ ⨿ᵒ Qᵒ) a =  Pᵒ a ⨿ Qᵒ a

abstract

  -- Monoᵒ for ⨿ᵒ

  ⨿ᵒ-Mono :  Monoᵒ Pᵒ →  Monoᵒ Qᵒ →  Monoᵒ $ Pᵒ ⨿ᵒ Qᵒ
  ⨿ᵒ-Mono MonoP _ a⊑b (ĩ₀ Pa) =  ĩ₀ MonoP a⊑b Pa
  ⨿ᵒ-Mono _ MonoQ a⊑b (ĩ₁ Qa) =  ĩ₁ MonoQ a⊑b Qa

--------------------------------------------------------------------------------
-- ⊤ᵒ, ⊥ᵒ :  Semantic truth and falsehood

⊤ᵒ ⊥ᵒ :  Propᵒ ł
⊤ᵒ _ =  ⊤
⊥ᵒ _ =  ⊥

-- ⊤ᵒ, ⊥ᵒ of level 0

⊤ᵒ₀ ⊥ᵒ₀ :  Propᵒ 0ᴸ
⊤ᵒ₀ =  ⊤ᵒ
⊥ᵒ₀ =  ⊥ᵒ

--------------------------------------------------------------------------------
-- →ᵒ :  Semantic implication

abstract

  infixr 5 _→ᵒ_
  _→ᵒ_ :  Propᵒ ł →  Propᵒ ł' →  Propᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł')
  (Pᵒ →ᵒ Qᵒ) a =  ∀ E b →  a ⊑ b →  E ✓ b →  Pᵒ b →  Qᵒ b

  -- Monoᵒ for →ᵒ

  →ᵒ-Mono :  Monoᵒ $ Pᵒ →ᵒ Qᵒ
  →ᵒ-Mono a⊑a' P→Qa _ _ a'⊑b E✓b Pᵒb =  P→Qa _ _ (⊑-trans a⊑a' a'⊑b) E✓b Pᵒb

  -- Monotonicity of →ᵒ

  →ᵒ-mono :  Pᵒ ⊨ Qᵒ →  Rᵒ ⊨ Sᵒ →  Qᵒ →ᵒ Rᵒ ⊨ Pᵒ →ᵒ Sᵒ
  →ᵒ-mono P⊨Q R⊨S Q→Ra _ _ a⊑b E✓b =  P⊨Q › Q→Ra _ _ a⊑b E✓b › R⊨S

  -- ⊨✓ →ᵒ into ⊨ →ᵒ

  ⊨✓⇒⊨-→ᵒ :  Pᵒ ⊨✓ Qᵒ →ᵒ Rᵒ →  Pᵒ ⊨ Qᵒ →ᵒ Rᵒ
  ⊨✓⇒⊨-→ᵒ P⊨✓Q→R Pa _ _ a⊑b E✓b =  P⊨✓Q→R (✓-mono a⊑b E✓b) Pa _ _ a⊑b E✓b

  -- Introduce/eliminate →ᵒ

  →ᵒ-intro :  Monoᵒ Qᵒ →  Pᵒ ×ᵒ Qᵒ ⊨✓ Rᵒ →  Qᵒ ⊨ Pᵒ →ᵒ Rᵒ
  →ᵒ-intro MonoQ P×Q⊨✓R Qa _ _ a⊑b E✓b Pb =  P×Q⊨✓R E✓b (Pb , MonoQ a⊑b Qa)

  →ᵒ-elim :  Qᵒ ⊨✓ Pᵒ →ᵒ Rᵒ →  Pᵒ ×ᵒ Qᵒ ⊨✓ Rᵒ
  →ᵒ-elim Q⊨✓P→R E✓a (Pa , Qa) =  Q⊨✓P→R E✓a Qa _ _ ⊑-refl E✓a Pa

--------------------------------------------------------------------------------
-- ∗ᵒ :  Semantic separating conjunction

infixr 7 _∗ᵒ'_ _∗ᵒ_

-- ∗ᵒ' :  Non-abstract version of ∗ᵒ

_∗ᵒ'_ :  Propᵒ ł →  Propᵒ ł' →  Propᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł')
(Pᵒ ∗ᵒ' Qᵒ) a =  ∑ b , ∑ c ,  b ∙ c ⊑ a  ×  Pᵒ b  ×  Qᵒ c

abstract

  -- ∗ᵒ :  Semantic separating conjunction

  _∗ᵒ_ :  Propᵒ ł →  Propᵒ ł' →  Propᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł')
  _∗ᵒ_ =  _∗ᵒ'_

  -- ∗ᵒ equals ∗ᵒ'

  ∗ᵒ≡∗ᵒ' :  _∗ᵒ_ {ł} {ł'} ≡ _∗ᵒ'_
  ∗ᵒ≡∗ᵒ' =  refl

  ∗ᵒ⇒∗ᵒ' :  Pᵒ ∗ᵒ Qᵒ  ⊨  Pᵒ ∗ᵒ' Qᵒ
  ∗ᵒ⇒∗ᵒ' {Pᵒ = Pᵒ} {Qᵒ = Qᵒ} =  substᵒ (λ F → F Pᵒ Qᵒ) ∗ᵒ≡∗ᵒ'

  ∗ᵒ'⇒∗ᵒ :  Pᵒ ∗ᵒ' Qᵒ  ⊨  Pᵒ ∗ᵒ Qᵒ
  ∗ᵒ'⇒∗ᵒ {Pᵒ = Pᵒ} {Qᵒ = Qᵒ} =  substᵒ (λ F → F Pᵒ Qᵒ) $ ◠ ∗ᵒ≡∗ᵒ'

  -- Monoᵒ for ∗ᵒ

  ∗ᵒ-Mono :  Monoᵒ $ Pᵒ ∗ᵒ Qᵒ
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

  -- - ∗ᵒ / ∗ᵒ - is commutative

  ?∗ᵒ-comm :  Pᵒ ∗ᵒ Qᵒ ∗ᵒ Rᵒ ⊨ Qᵒ ∗ᵒ Pᵒ ∗ᵒ Rᵒ
  ?∗ᵒ-comm =  ∗ᵒ-assocʳ › ∗ᵒ-monoˡ ∗ᵒ-comm › ∗ᵒ-assocˡ

  ∗ᵒ?-comm :  (Pᵒ ∗ᵒ Qᵒ) ∗ᵒ Rᵒ ⊨ (Pᵒ ∗ᵒ Rᵒ) ∗ᵒ Qᵒ
  ∗ᵒ?-comm =  ∗ᵒ-assocˡ › ∗ᵒ-monoʳ ∗ᵒ-comm › ∗ᵒ-assocʳ

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

  -- ∃ᵒ/ᴵ and ⨿ commute with ∗ᵒ

  ∃ᵒ∗ᵒ-out :  ∃ᵒ˙ Pᵒ˙ ∗ᵒ Qᵒ  ⊨  ∃ᵒ x , Pᵒ˙ x ∗ᵒ Qᵒ
  ∃ᵒ∗ᵒ-out (-, -, b∙c⊑a , (-, Pxb) , Qc) =  -, -, -, b∙c⊑a , Pxb , Qc

  ∗ᵒ∃ᵒ-out :  Pᵒ ∗ᵒ ∃ᵒ˙ Qᵒ˙  ⊨  ∃ᵒ x , Pᵒ ∗ᵒ Qᵒ˙ x
  ∗ᵒ∃ᵒ-out (-, -, b∙c⊑a , Pb , (-, Qxc)) =  -, -, -, b∙c⊑a , Pb , Qxc

  ∃ᴵ∗ᵒ-out :  ∃ᴵ˙ Pᵒ˙ ∗ᵒ Qᵒ  ⊨  ∃ᴵ x , Pᵒ˙ x ∗ᵒ Qᵒ
  ∃ᴵ∗ᵒ-out (-, -, b∙c⊑a , (-ᴵ, Pxb) , Qc) =  -ᴵ, -, -, b∙c⊑a , Pxb , Qc

  ∗ᵒ∃ᴵ-out :  Pᵒ ∗ᵒ ∃ᴵ˙ Qᵒ˙  ⊨  ∃ᴵ x , Pᵒ ∗ᵒ Qᵒ˙ x
  ∗ᵒ∃ᴵ-out (-, -, b∙c⊑a , Pb , (-ᴵ, Qxc)) =  -ᴵ, -, -, b∙c⊑a , Pb , Qxc

  ⨿ᵒ∗ᵒ-out :  (Pᵒ ⨿ᵒ Qᵒ) ∗ᵒ Rᵒ  ⊨  (Pᵒ ∗ᵒ Rᵒ) ⨿ᵒ (Qᵒ ∗ᵒ Rᵒ)
  ⨿ᵒ∗ᵒ-out (-, -, b∙c⊑a , ĩ₀ Pb , Rc) =  ĩ₀ (-, -, b∙c⊑a , Pb , Rc)
  ⨿ᵒ∗ᵒ-out (-, -, b∙c⊑a , ĩ₁ Qb , Rc) =  ĩ₁ (-, -, b∙c⊑a , Qb , Rc)

  ∗ᵒ⨿ᵒ-out :  Pᵒ ∗ᵒ (Qᵒ ⨿ᵒ Rᵒ)  ⊨  (Pᵒ ∗ᵒ Qᵒ) ⨿ᵒ (Pᵒ ∗ᵒ Rᵒ)
  ∗ᵒ⨿ᵒ-out (-, -, b∙c⊑a , Pb , ĩ₀ Qc) =  ĩ₀ (-, -, b∙c⊑a , Pb , Qc)
  ∗ᵒ⨿ᵒ-out (-, -, b∙c⊑a , Pb , ĩ₁ Rc) =  ĩ₁ (-, -, b∙c⊑a , Pb , Rc)

--------------------------------------------------------------------------------
-- [∗ᵒ] :  Iterated semantic separating conjunction

[∗ᵒ] :  List (Propᵒ ł) →  Propᵒ (1ᴸ ⊔ᴸ ł)
[∗ᵒ] [] =  ⊤ᵒ
[∗ᵒ] (Pᵒ ∷ Pᵒs) =  Pᵒ ∗ᵒ [∗ᵒ] Pᵒs

-- Syntax for [∗ᵒ] $ᴸ / $ⁱᴸ

infix 8 [∗ᵒ∈]-syntax [∗ᵒ∈ⁱ]-syntax [∗ᵒ∈ⁱ⟨⟩]-syntax
[∗ᵒ∈] [∗ᵒ∈]-syntax :  (X → Propᵒ ł) →  List X →  Propᵒ (1ᴸ ⊔ᴸ ł)
[∗ᵒ∈] Pᵒ˙ xs =  [∗ᵒ] $ Pᵒ˙ $ᴸ xs
[∗ᵒ∈]-syntax =  [∗ᵒ∈]
[∗ᵒ∈ⁱ] [∗ᵒ∈ⁱ]-syntax :  (ℕ × X → Propᵒ ł) →  List X →  Propᵒ (1ᴸ ⊔ᴸ ł)
[∗ᵒ∈ⁱ] Pᵒ˙ xs =  [∗ᵒ] $ curry Pᵒ˙ $ⁱᴸ xs
[∗ᵒ∈ⁱ]-syntax =  [∗ᵒ∈ⁱ]
[∗ᵒ∈ⁱ⟨⟩] [∗ᵒ∈ⁱ⟨⟩]-syntax :  (ℕ × X → Propᵒ ł) →  ℕ →  List X →  Propᵒ (1ᴸ ⊔ᴸ ł)
[∗ᵒ∈ⁱ⟨⟩] Pᵒ˙ k xs =  [∗ᵒ] $ curry Pᵒ˙ $ⁱᴸ⟨ k ⟩ xs
[∗ᵒ∈ⁱ⟨⟩]-syntax =  [∗ᵒ∈ⁱ⟨⟩]
syntax [∗ᵒ∈]-syntax (λ x → Pᵒ) xs =  [∗ᵒ x ∈ xs ] Pᵒ
syntax [∗ᵒ∈ⁱ]-syntax (λ ix → Pᵒ) xs =  [∗ᵒ ix ∈ⁱ xs ] Pᵒ
syntax [∗ᵒ∈ⁱ⟨⟩]-syntax (λ ix → Pᵒ) k xs =  [∗ᵒ ix ∈ⁱ⟨ k ⟩ xs ] Pᵒ

abstract

  -- Monoᵒ for [∗ᵒ]

  [∗ᵒ]-Mono :  Monoᵒ $ [∗ᵒ] Pᵒs
  [∗ᵒ]-Mono {Pᵒs = []} =  _
  [∗ᵒ]-Mono {Pᵒs = _ ∷ _} =  ∗ᵒ-Mono

--------------------------------------------------------------------------------
-- [∗ᵒ∈²] :  Iterated separating conjunction over two lists

infix 8 [∗ᵒ∈²]-syntax
[∗ᵒ∈²] [∗ᵒ∈²]-syntax :
  (X × Y →  Propᵒ ł) →  List X →  List Y →  Propᵒ (1ᴸ ⊔ᴸ ł)
[∗ᵒ∈²] Pᵒ˙ (x ∷ xs) (y ∷ ys) =  Pᵒ˙ (x , y) ∗ᵒ [∗ᵒ∈²] Pᵒ˙ xs ys
[∗ᵒ∈²] _ [] [] =  ⊤ᵒ
[∗ᵒ∈²] _ _ _ =  ⊥ᵒ
[∗ᵒ∈²]-syntax =  [∗ᵒ∈²]

syntax [∗ᵒ∈²]-syntax (λ xy → Pᵒ) xs ys =  [∗ᵒ xy ∈² xs , ys ] Pᵒ

abstract

  -- Monoᵒ for [∗ᵒ∈²]

  [∗ᵒ∈²]-Mono :  Monoᵒ $ [∗ᵒ∈²] Pᵒ˙ xs ys
  [∗ᵒ∈²]-Mono {xs = []} {[]} =  _
  [∗ᵒ∈²]-Mono {xs = _ ∷ _} {_ ∷ _} =  ∗ᵒ-Mono

--------------------------------------------------------------------------------
-- -∗ᵒ :  Semantic magic wand

infixr 5 _-∗ᵒ'_ _-∗ᵒ_

-- -∗ᵒ' :  Non-abstract version of -∗ᵒ

_-∗ᵒ'_ :  Propᵒ ł →  Propᵒ ł' →  Propᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł')
(Pᵒ -∗ᵒ' Qᵒ) a =  ∀ E b c →  a ⊑ b →  E ✓ c ∙ b →  Pᵒ c →  Qᵒ (c ∙ b)

abstract

  -- -∗ᵒ :  Semantic magic wand

  _-∗ᵒ_ :  Propᵒ ł →  Propᵒ ł' →  Propᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł')
  _-∗ᵒ_ =  _-∗ᵒ'_

  -- -∗ᵒ equals -∗ᵒ'

  -∗ᵒ≡-∗ᵒ' :  _-∗ᵒ_ {ł} {ł'} ≡ _-∗ᵒ'_
  -∗ᵒ≡-∗ᵒ' =  refl

  -∗ᵒ⇒-∗ᵒ' :  Pᵒ -∗ᵒ Qᵒ  ⊨  Pᵒ -∗ᵒ' Qᵒ
  -∗ᵒ⇒-∗ᵒ' {Pᵒ = Pᵒ} {Qᵒ = Qᵒ} =  substᵒ (λ F → F Pᵒ Qᵒ) -∗ᵒ≡-∗ᵒ'

  -∗ᵒ'⇒-∗ᵒ :  Pᵒ -∗ᵒ' Qᵒ  ⊨  Pᵒ -∗ᵒ Qᵒ
  -∗ᵒ'⇒-∗ᵒ {Pᵒ = Pᵒ} {Qᵒ = Qᵒ} =  substᵒ (λ F → F Pᵒ Qᵒ) $ ◠ -∗ᵒ≡-∗ᵒ'

  -- Monoᵒ for -∗ᵒ

  -∗ᵒ-Mono :  Monoᵒ $ Pᵒ -∗ᵒ Qᵒ
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

  -- ⊨✓ -∗ᵒ into ⊨ -∗ᵒ

  ⊨✓⇒⊨--∗ᵒ :  Pᵒ ⊨✓ Qᵒ -∗ᵒ Rᵒ →  Pᵒ ⊨ Qᵒ -∗ᵒ Rᵒ
  ⊨✓⇒⊨--∗ᵒ P⊨✓Q-∗R Pa _ _ _ a⊑b E✓c∙b =
    P⊨✓Q-∗R (✓-mono (⊑-trans a⊑b ∙-incrˡ) E✓c∙b) Pa _ _ _ a⊑b E✓c∙b

  -- Introduce/eliminate -∗ᵒ

  -∗ᵒ-intro :  Pᵒ ∗ᵒ Qᵒ ⊨✓ Rᵒ →  Qᵒ ⊨ Pᵒ -∗ᵒ Rᵒ
  -∗ᵒ-intro P∗Q⊨✓R Qa _ _ _ a⊑b E✓c∙b Pc =
    P∗Q⊨✓R E✓c∙b (-, -, ∙-monoʳ a⊑b , Pc , Qa)

  -∗ᵒ-intro' :  Monoᵒ Pᵒ →  Pᵒ ⊨✓ Qᵒ →  ⊨ Pᵒ -∗ᵒ Qᵒ
  -∗ᵒ-intro' MonoP P⊨✓Q =
    -∗ᵒ-intro {Qᵒ = ⊤ᵒ₀} (λ ✓∙ → ∗ᵒ-elimˡ MonoP › P⊨✓Q ✓∙) _

  -∗ᵒ-elim :  Monoᵒ Rᵒ →  Qᵒ ⊨✓ Pᵒ -∗ᵒ Rᵒ →  Pᵒ ∗ᵒ Qᵒ ⊨✓ Rᵒ
  -∗ᵒ-elim MonoR Q⊨✓P-∗R E✓a (-, -, b∙c⊑a , Pb , Qc) =  MonoR b∙c⊑a $ Q⊨✓P-∗R
    (✓-mono (⊑-trans ∙-incrˡ b∙c⊑a) E✓a) Qc _ _ _ ⊑-refl (✓-mono b∙c⊑a E✓a) Pb

  -∗ᵒ-applyˡ :  Monoᵒ Qᵒ →  Pᵒ ∗ᵒ (Pᵒ -∗ᵒ Qᵒ) ⊨✓ Qᵒ
  -∗ᵒ-applyˡ MonoQ =  -∗ᵒ-elim MonoQ λ _ → id

  -∗ᵒ-applyʳ :  Monoᵒ Qᵒ →  (Pᵒ -∗ᵒ Qᵒ) ∗ᵒ Pᵒ ⊨✓ Qᵒ
  -∗ᵒ-applyʳ MonoQ ✓∙ =  ∗ᵒ-comm › -∗ᵒ-applyˡ MonoQ ✓∙

  -- Let -∗ᵒ eat a proposition

  -∗ᵒ-eatʳ :  Monoᵒ Qᵒ →  (Pᵒ -∗ᵒ Qᵒ) ∗ᵒ Rᵒ ⊨ Pᵒ -∗ᵒ Qᵒ ∗ᵒ Rᵒ
  -∗ᵒ-eatʳ MonoQ =  -∗ᵒ-intro λ ✓∙ → ∗ᵒ-assocʳ › ∗ᵒ-mono✓ˡ (-∗ᵒ-applyˡ MonoQ) ✓∙

  -∗ᵒ-eatˡ :  Monoᵒ Qᵒ →  Rᵒ ∗ᵒ (Pᵒ -∗ᵒ Qᵒ) ⊨ Pᵒ -∗ᵒ Rᵒ ∗ᵒ Qᵒ
  -∗ᵒ-eatˡ {Qᵒ = Qᵒ} {Rᵒ = Rᵒ} MonoQ =  ∗ᵒ-comm › -∗ᵒ-eatʳ MonoQ ›
    -∗ᵒ-monoʳ λ{a} → ∗ᵒ-comm {Pᵒ = Qᵒ} {Qᵒ = Rᵒ} {a}

--------------------------------------------------------------------------------
-- ⤇ᵒ :  Semantic update modality

abstract

  infix 3 ⤇ᵒ_
  ⤇ᵒ_ :  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
  (⤇ᵒ Pᵒ) a =  ∀ E c →  E ✓ a ∙ c →  ∑ b ,  E ✓ b ∙ c  ×  Pᵒ b

  -- Monoᵒ for ⤇ᵒ

  ⤇ᵒ-Mono :  Monoᵒ $ ⤇ᵒ Pᵒ
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

  ⤇ᵒ-eatʳ :  (⤇ᵒ Pᵒ) ∗ᵒ Qᵒ  ⊨ ⤇ᵒ  Pᵒ ∗ᵒ Qᵒ
  ⤇ᵒ-eatʳ (-, -, b∙c⊑a , ⤇Pb , Qc) _ _ E✓a∙e
    with ⤇Pb _ _ $ flip ✓-mono E✓a∙e $ ⊑-respˡ ∙-assocˡ $ ∙-monoˡ b∙c⊑a
  … | -, E✓d∙ce , Pd =  -, ✓-resp ∙-assocʳ E✓d∙ce , -, -, ⊑-refl , Pd , Qc

  ⤇ᵒ-eatˡ :  Qᵒ ∗ᵒ (⤇ᵒ Pᵒ)  ⊨ ⤇ᵒ  Qᵒ ∗ᵒ Pᵒ
  ⤇ᵒ-eatˡ =  ∗ᵒ-comm › ⤇ᵒ-eatʳ › ⤇ᵒ-mono ∗ᵒ-comm

  -- Let ⌜ ⌝ᵒ× go out of ⤇ᵒ

  ⤇ᵒ-⌜⌝ᵒ×-out :  ⤇ᵒ ⌜ X ⌝ᵒ× Pᵒ  ⊨✓  ⌜ X ⌝ᵒ× ⤇ᵒ Pᵒ
  ⤇ᵒ-⌜⌝ᵒ×-out E✓a ⤇XP .π₀ =
    let -, -, x , _ = ⤇XP _ _ $ ✓-resp (◠˜ ∙-unitʳ) E✓a in  x
  ⤇ᵒ-⌜⌝ᵒ×-out _ ⤇XP .π₁ _ _ E✓a∙c =
    let -, E✓b∙c , -, Pb = ⤇XP _ _ E✓a∙c in  -, E✓b∙c , Pb

  -- ⊨✓ ⤇ᵒ into ⊨ ⤇ᵒ

  ⊨✓⇒⊨-⤇ᵒ :  Pᵒ ⊨✓ ⤇ᵒ Qᵒ →  Pᵒ ⊨ ⤇ᵒ Qᵒ
  ⊨✓⇒⊨-⤇ᵒ P⊨✓⤇Q Pa _ _ E✓a∙c =  P⊨✓⤇Q (✓-mono ∙-incrʳ E✓a∙c) Pa _ _ E✓a∙c

--------------------------------------------------------------------------------
-- ⤇ᴱ :  Environmental update modality

infix 3 _⤇ᴱ'_ _⤇ᴱ_

-- ⤇ᴱ' :  Non-abstract version of ⤇ᴱ

_⤇ᴱ'_ :  ∀{X : Set ł'} →  Envᴳ →  (X → Envᴳ × Propᵒ ł) →  Propᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł')
(E ⤇ᴱ' FPᵒ˙) a =  ∀ c →  E ✓ a ∙ c →  ∑ x , ∑ b ,
  let (F , Pᵒ) = FPᵒ˙ x in  F ✓ b ∙ c  ×  Pᵒ b

abstract

  -- ⤇ᴱ :  Environmental update modality

  _⤇ᴱ_ :  ∀{X : Set ł'} →  Envᴳ →  (X → Envᴳ × Propᵒ ł) →  Propᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł')
  _⤇ᴱ_ =  _⤇ᴱ'_

  -- ⤇ᴱ equals ⤇ᴱ'

  ⤇ᴱ≡⤇ᴱ' :  _⤇ᴱ_ {ł} {ł'} {X} ≡ _⤇ᴱ'_
  ⤇ᴱ≡⤇ᴱ' =  refl

  -- Monoᵒ for ⤇ᴱ

  ⤇ᴱ-Mono :  Monoᵒ $ E ⤇ᴱ FPᵒ˙
  ⤇ᴱ-Mono a⊑a' E⤇FPa _ E✓a'∙c =  E⤇FPa _ $ ✓-mono (∙-monoˡ a⊑a') E✓a'∙c

  -- Monotonicity of ⤇ᴱ

  ⤇ᴱ-mono✓ :  (∀ x →  Pᵒ˙ x ⊨✓ Qᵒ˙ x)  →
              E ⤇ᴱ (λ x → F˙ x , Pᵒ˙ x)  ⊨  E ⤇ᴱ λ x → F˙ x , Qᵒ˙ x
  ⤇ᴱ-mono✓ Px⊨✓Qx E⤇FPa _ E✓a∙c  with E⤇FPa _ E✓a∙c
  … | -, -, F✓b∙c , Pb =  -, -, F✓b∙c , Px⊨✓Qx _ (✓-mono ∙-incrʳ F✓b∙c) Pb

  ⤇ᴱ-mono :  (∀ x →  Pᵒ˙ x ⊨ Qᵒ˙ x)  →
             E ⤇ᴱ (λ x → F˙ x , Pᵒ˙ x)  ⊨  E ⤇ᴱ λ x → F˙ x , Qᵒ˙ x
  ⤇ᴱ-mono =  ⤇ᴱ-mono✓ ∘ (⊨⇒⊨✓ ∘_)

  -- Update the environment of ⤇ᴱ

  ⤇ᴱ-respᴱˡ :  E ≡˙ F →  E ⤇ᴱ GPᵒ˙ ⊨ F ⤇ᴱ GPᵒ˙
  ⤇ᴱ-respᴱˡ E≡F E⤇GP _ F✓a∙c =  E⤇GP _ $ ✓˙-respᴱ (◠˙ E≡F) F✓a∙c

  ⤇ᴱ-respᴱʳ :  (∀{x} → E˙ x ≡˙ F˙ x) →
               G ⤇ᴱ (λ x → E˙ x , Pᵒ˙ x)  ⊨  G ⤇ᴱ λ x → F˙ x , Pᵒ˙ x
  ⤇ᴱ-respᴱʳ Ex≡Fx G⤇EP _ G✓a∙c  with G⤇EP _ G✓a∙c
  … | -, -, E✓b∙c , Pb =  -, -, ✓˙-respᴱ Ex≡Fx E✓b∙c , Pb

  -- Change parameterization of ⤇ᴱ

  ⤇ᴱ-param :  E ⤇ᴱ FPᵒ˙ ∘ f  ⊨  E ⤇ᴱ FPᵒ˙
  ⤇ᴱ-param E⤇FPf _ E✓a∙c  with E⤇FPf _ E✓a∙c
  … | -, b,F✓b,Pb∙c =  -, b,F✓b,Pb∙c

  -- ⊨✓ ⤇ᴱ into ⊨ ⤇ᴱ

  ⊨✓⇒⊨-⤇ᴱ :  Pᵒ ⊨✓ E ⤇ᴱ FQᵒ˙ →  Pᵒ ⊨ E ⤇ᴱ FQᵒ˙
  ⊨✓⇒⊨-⤇ᴱ P⊨✓E⤇FQ Pa _ E✓a∙c =  P⊨✓E⤇FQ (✓-mono ∙-incrʳ E✓a∙c) Pa _ E✓a∙c

  -- Introduce ⤇ᴱ

  ⤇ᵒ⇒⤇ᴱ :  ⤇ᵒ Pᵒ  ⊨  E ⤇ᴱ λ (_ : ⊤₀) → E , Pᵒ
  ⤇ᵒ⇒⤇ᴱ ⤇ᵒPa _ E✓a∙c  with ⤇ᵒPa _ _ E✓a∙c
  … | (-, E✓b∙c , Pb) =  -, -, E✓b∙c , Pb

  ⤇ᴱ-intro :  Pᵒ  ⊨  E ⤇ᴱ λ (_ : ⊤₀) → E , Pᵒ
  ⤇ᴱ-intro =  ⤇ᵒ-intro › ⤇ᵒ⇒⤇ᴱ

  -- Introduce ⤇ᴱ with the validity of E

  ⤇ᴱ-intro-✓ :  Pᵒ  ⊨  E ⤇ᴱ λ (_ : ∑ a , E ✓ a) → E , Pᵒ
  ⤇ᴱ-intro-✓ Pa _ E✓a∙c =  (-, E✓a∙c) , -, E✓a∙c , Pa

  -- Join ⤇ᴱs

  ⤇ᴱ-join :  E ⤇ᴱ (λ x → F˙ x , F˙ x ⤇ᴱ GPᵒ˙˙ x)  ⊨  E ⤇ᴱ uncurry GPᵒ˙˙
  ⤇ᴱ-join E⤇F,F⤇GPx _ E✓a∙d  with E⤇F,F⤇GPx _ E✓a∙d
  … | -, -, F✓b∙d , F⤇GPxb  with F⤇GPxb _ F✓b∙d
  …   | -, -, Gxy✓c∙d , Pxyc =  -, -, Gxy✓c∙d , Pxyc

  -- Let ⤇ᴱ eat a proposition under ∗ᵒ

  ⤇ᴱ-eatʳ :  (E ⤇ᴱ λ x → F˙ x , Pᵒ˙ x)  ∗ᵒ  Qᵒ  ⊨ E ⤇ᴱ λ x → F˙ x ,  Pᵒ˙ x ∗ᵒ Qᵒ
  ⤇ᴱ-eatʳ (-, -, b∙c⊑a , E⤇FPb , Qc) _ E✓a∙e
    with E⤇FPb _ $ flip ✓-mono E✓a∙e $ ⊑-respˡ ∙-assocˡ $ ∙-monoˡ b∙c⊑a
  … | -, -, F✓d∙ce , Pd =
    -, -, ✓-resp ∙-assocʳ F✓d∙ce , -, -, ⊑-refl , Pd , Qc

  ⤇ᴱ-eatˡ :  Qᵒ  ∗ᵒ  (E ⤇ᴱ λ x → F˙ x , Pᵒ˙ x)  ⊨ E ⤇ᴱ λ x → F˙ x ,  Qᵒ ∗ᵒ Pᵒ˙ x
  ⤇ᴱ-eatˡ =  ∗ᵒ-comm › ⤇ᴱ-eatʳ › ⤇ᴱ-mono λ _ → ∗ᵒ-comm

  -- Perform a step by ⤇ᴱ

  ⤇ᴱ-step :  E ✓ a  →  (E ⤇ᴱ λ x → F˙ x , Pᵒ˙ x) a →
             ∑ x , ∑ b ,  F˙ x ✓ b  ×  Pᵒ˙ x b
  ⤇ᴱ-step E✓a E⤇FxPxa  with E⤇FxPxa _ $ ✓-resp (◠˜ ∙-unitʳ) E✓a
  … | -, -, Fx✓b∙ε , Pxb =  -, -, ✓-resp ∙-unitʳ Fx✓b∙ε , Pxb

--------------------------------------------------------------------------------
-- □ᵒ :  Semantic persistence modality

infix 8 □ᵒ_
□ᵒ_ :  Propᵒ ł →  Propᵒ ł
(□ᵒ Pᵒ) a =  Pᵒ ⌞ a ⌟

abstract

  -- Monoᵒ for □ᵒ

  □ᵒ-Mono :  Monoᵒ Pᵒ →  Monoᵒ $ □ᵒ Pᵒ
  □ᵒ-Mono MonoP a⊑b P⌞a⌟ =  MonoP (⌞⌟-mono a⊑b) P⌞a⌟

  -- Monotonicity of □ᵒ

  □ᵒ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  □ᵒ Pᵒ ⊨✓ □ᵒ Qᵒ
  □ᵒ-mono✓ P⊨✓Q E✓a =  P⊨✓Q $ ✓-mono ⌞⌟-decr E✓a

  □ᵒ-mono :  Pᵒ ⊨ Qᵒ →  □ᵒ Pᵒ ⊨ □ᵒ Qᵒ
  □ᵒ-mono P⊨Q =  P⊨Q

  -- Eliminate □ᵒ

  □ᵒ-elim :  Monoᵒ Pᵒ →  □ᵒ Pᵒ ⊨ Pᵒ
  □ᵒ-elim MonoP P⌞a⌟ =  MonoP ⌞⌟-decr P⌞a⌟

  -- Duplicate □ᵒ

  □ᵒ-dup :  Monoᵒ Pᵒ →  □ᵒ Pᵒ ⊨ □ᵒ □ᵒ Pᵒ
  □ᵒ-dup MonoP P⌞a⌟ =  MonoP (≈⇒⊑ $ ◠˜ ⌞⌟-idem) P⌞a⌟

  -- Change ×ᵒ into ∗ᵒ when one argument is under □ᵒ

  □ᵒˡ-×ᵒ⇒∗ᵒ :  Monoᵒ Pᵒ →  □ᵒ Pᵒ ×ᵒ Qᵒ  ⊨  □ᵒ Pᵒ ∗ᵒ Qᵒ
  □ᵒˡ-×ᵒ⇒∗ᵒ MonoP (P⌞a⌟ , Qa) =  -, -, ≈⇒⊑ ⌞⌟-unitˡ ,
    MonoP (≈⇒⊑ $ ◠˜ ⌞⌟-idem) P⌞a⌟ , Qa

  -- Duplicate □ᵒ Pᵒ

  dup-□ᵒ :  Monoᵒ Pᵒ →  □ᵒ Pᵒ  ⊨  □ᵒ Pᵒ ∗ᵒ □ᵒ Pᵒ
  dup-□ᵒ MonoP =  (λ Pa → Pa , Pa) › □ᵒˡ-×ᵒ⇒∗ᵒ MonoP

  -- □ᵒ commutes with ∗ᵒ

  □ᵒ-∗ᵒ-out :  Monoᵒ Pᵒ →  Monoᵒ Qᵒ →  □ᵒ (Pᵒ ∗ᵒ Qᵒ)  ⊨  □ᵒ Pᵒ ∗ᵒ □ᵒ Qᵒ
  □ᵒ-∗ᵒ-out MonoP MonoQ (-, -, b∙c⊑⌞a⌟ , Pb , Qc) =  □ᵒˡ-×ᵒ⇒∗ᵒ MonoP
    (MonoP (⊑-trans ∙-incrʳ b∙c⊑⌞a⌟) Pb , MonoQ (⊑-trans ∙-incrˡ b∙c⊑⌞a⌟) Qc)

  □ᵒ-∗ᵒ-in :  □ᵒ Pᵒ ∗ᵒ □ᵒ Qᵒ  ⊨  □ᵒ (Pᵒ ∗ᵒ Qᵒ)
  □ᵒ-∗ᵒ-in(-, -, b∙c⊑a , P⌞b⌟ , Q⌞c⌟) =
    -, -, ⊑-trans ⌞⌟-∙ (⌞⌟-mono b∙c⊑a) , P⌞b⌟ , Q⌞c⌟

--------------------------------------------------------------------------------
-- ◎ :  Semantically own a resource

abstract

  infix 8 ◎_
  ◎_ :  Resᴳ →  Propᵒ 1ᴸ
  (◎ a) b =  a ⊑ b

  -- Monoᵒ for ◎

  ◎-Mono :  Monoᵒ $ ◎ a
  ◎-Mono b⊑c a⊑b =  ⊑-trans a⊑b b⊑c

  -- Modify the resource of ◎

  ◎-resp :  a ≈ b →  ◎ a ⊨ ◎ b
  ◎-resp a≈b a⊑c =  ⊑-respˡ a≈b a⊑c

  ◎-mono :  b ⊑ a →  ◎ a ⊨ ◎ b
  ◎-mono b⊑a a⊑c =  ⊑-trans b⊑a a⊑c

  -- Get ◎ ε

  ◎-ε :  ⊨ ◎ ε
  ◎-ε =  ε-min

  ◎-≈ε :  a ≈ ε →  ⊨ ◎ a
  ◎-≈ε a≈ε =  ◎-resp (◠˜ a≈ε) ◎-ε

  -- ◎ a ∗ᵒ ◎ b agrees with ◎ (a ∙ b)

  ◎-∗ᵒ⇒∙ :  ◎ a ∗ᵒ ◎ b  ⊨  ◎ (a ∙ b)
  ◎-∗ᵒ⇒∙ (-, -, a'∙b'⊑c , a⊑a' , b⊑b') =  ⊑-trans (∙-mono a⊑a' b⊑b') a'∙b'⊑c

  ◎-∙⇒∗ᵒ :  ◎ (a ∙ b)  ⊨  ◎ a ∗ᵒ ◎ b
  ◎-∙⇒∗ᵒ a∙b⊑c =  -, -, a∙b⊑c , ⊑-refl , ⊑-refl

  -- ◎ a is persistent when ⌞ a ⌟ agrees with a

  ◎-⌞⌟≈-□ᵒ :  ⌞ a ⌟ ≈ a →  ◎ a  ⊨  □ᵒ ◎ a
  ◎-⌞⌟≈-□ᵒ ⌞a⌟≈a a⊑b =  ⊑-respˡ ⌞a⌟≈a $ ⌞⌟-mono a⊑b

  -- ◎ a into ✓ a

  ◎-✓ :  ◎ a  ⊨✓  ⌜ ∑ E , E ✓ a ⌝ᵒ
  ◎-✓ E✓b a⊑b =  -, ✓-mono a⊑b E✓b

  -- Get (◎ a) a

  ◎-just :  (◎ a) a
  ◎-just =  ⊑-refl

  -- ↝ into ⤇ᵒ on ◎

  ↝-◎-⤇ᵒ-∃ᵒ :  (∀{E} →  (E , a)  ↝ λ x →  E , b˙ x) →
               ◎ a  ⊨  ⤇ᵒ (∃ᵒ x , ◎ b˙ x)
  ↝-◎-⤇ᵒ-∃ᵒ Ea↝Ebx a⊑a' _ _ E✓a'∙c  with Ea↝Ebx _ $ ✓-mono (∙-monoˡ a⊑a') E✓a'∙c
  … | -, E✓bx∙c =  -, E✓bx∙c , -, ⊑-refl

  -- ↝ into ⤇ᴱ on ◎

  ↝-◎-⤇ᴱ :  ((E , a)  ↝ λ x →  F˙ x , b˙ x)  →
            ◎ a  ⊨  E  ⤇ᴱ λ x →  F˙ x , ◎ b˙ x
  ↝-◎-⤇ᴱ Ea↝Fxbx a⊑a' _ E✓a'∙c  with Ea↝Fxbx _ $ ✓-mono (∙-monoˡ a⊑a') E✓a'∙c
  … | -, Fx✓bx∙c =  -, -, Fx✓bx∙c , ⊑-refl

  -- Adequacy of ⤇ᴱ
  -- If we have Y under ◎ a and E ⤇ᴱ for a and E such that E ✓ a,
  -- then Y holds purely

  ⤇ᴱ-adeq :  E ✓ a →  ◎ a ⊨ E ⤇ᴱ (λ x → F˙ x , ⌜ Y ⌝ᵒ) →  Y
  ⤇ᴱ-adeq E✓a a⊨E⤇FxY =
    let (-, -, -, y) = a⊨E⤇FxY ⊑-refl _ (✓-resp (◠˜ ∙-unitʳ) E✓a) in y

-- On an component ERA

-- ◎⟨ ⟩ :  Semantically own a resource of a component ERA

infix 8 ◎⟨_⟩_
◎⟨_⟩_ :  ∀ i →  Resᴳ˙ i →  Propᵒ 1ᴸ
◎⟨ i ⟩ aⁱ =  ◎ inj˙ i aⁱ

module _ {i : ℕ} where

  open ERA (Globᴱᴿᴬ˙ i) using () renaming (Res to Resⁱ; Env to Envⁱ;
    _≈_ to _≈ⁱ_; _✓_ to _✓ⁱ_; _∙_ to _∙ⁱ_; ε to εⁱ; ⌞_⌟ to ⌞_⌟ⁱ; _↝_ to _↝ⁱ_;
    ≡⇒≈ to ≡⇒≈ⁱ)

  private variable
    Fⁱ˙ :  X → Envⁱ
    aⁱ bⁱ :  Resⁱ
    aⁱ˙ bⁱ˙ :  X → Resⁱ

  abstract

    ◎⟨⟩-resp :  aⁱ ≈ⁱ bⁱ →  ◎⟨ i ⟩ aⁱ ⊨ ◎⟨ i ⟩ bⁱ
    ◎⟨⟩-resp =  inj˙-≈ › ◎-resp

    -- Get ◎⟨ i ⟩ εⁱ

    ◎⟨⟩-ε :  ⊨  ◎⟨ i ⟩ εⁱ
    ◎⟨⟩-ε =  ◎-≈ε inj˙-ε

    -- ◎⟨ i ⟩ aⁱ ∗ᵒ ◎⟨ i ⟩ bⁱ agrees with ◎⟨ i ⟩ (aⁱ ∙ⁱ bⁱ)

    ◎⟨⟩-∗ᵒ⇒∙ :  ◎⟨ i ⟩ aⁱ  ∗ᵒ  ◎⟨ i ⟩ bⁱ  ⊨  ◎⟨ i ⟩ (aⁱ ∙ⁱ bⁱ)
    ◎⟨⟩-∗ᵒ⇒∙ =  ◎-∗ᵒ⇒∙ › ◎-resp inj˙-∙

    ◎⟨⟩-∙⇒∗ᵒ :  ◎⟨ i ⟩ (aⁱ ∙ⁱ bⁱ)  ⊨  ◎⟨ i ⟩ aⁱ  ∗ᵒ  ◎⟨ i ⟩ bⁱ
    ◎⟨⟩-∙⇒∗ᵒ =  ◎-resp (◠˜ inj˙-∙) › ◎-∙⇒∗ᵒ

    -- ◎⟨ i ⟩ aⁱ is persistent when ⌞ aⁱ ⌟ agrees with aⁱ

    ◎⟨⟩-⌞⌟≈-□ᵒ :  ⌞ aⁱ ⌟ⁱ ≈ⁱ aⁱ →  ◎⟨ i ⟩ aⁱ  ⊨  □ᵒ ◎⟨ i ⟩ aⁱ
    ◎⟨⟩-⌞⌟≈-□ᵒ ⌞a⌟≈a =  ◎-⌞⌟≈-□ᵒ $ inj˙-⌞⌟ ◇˜ inj˙-≈ ⌞a⌟≈a

    ◎⟨⟩-⌞⌟≡-□ᵒ :  ⌞ aⁱ ⌟ⁱ ≡ aⁱ →  ◎⟨ i ⟩ aⁱ  ⊨  □ᵒ ◎⟨ i ⟩ aⁱ
    ◎⟨⟩-⌞⌟≡-□ᵒ ⌞a⌟≡a =  ◎⟨⟩-⌞⌟≈-□ᵒ $ ≡⇒≈ⁱ ⌞a⌟≡a

    -- ◎⟨ i ⟩ aⁱ into ✓ⁱ aⁱ

    ◎⟨⟩-✓ :  ◎⟨ i ⟩ aⁱ  ⊨✓  ⌜ ∑ Eⁱ , Eⁱ ✓ⁱ aⁱ ⌝ᵒ
    ◎⟨⟩-✓ E✓◎ia =  ◎-✓ E✓◎ia › λ (-, E✓ia) → -, ✓-inj˙ E✓ia

    -- ↝ⁱ into ⤇ᵒ on ◎⟨ i ⟩

    ↝-◎⟨⟩-⤇ᵒ-∃ᵒ :  (∀{Eⁱ} →  (Eⁱ , aⁱ)  ↝ⁱ λ x →  Eⁱ , bⁱ˙ x)  →
                   ◎⟨ i ⟩ aⁱ  ⊨  ⤇ᵒ (∃ᵒ x , ◎⟨ i ⟩ bⁱ˙ x)
    ↝-◎⟨⟩-⤇ᵒ-∃ᵒ Ea↝Ebx =  ↝-◎-⤇ᵒ-∃ᵒ $ inj˙-↝ Ea↝Ebx

    ε↝-◎⟨⟩-⤇ᵒ-∃ᵒ :  (∀{Eⁱ} →  (Eⁱ , εⁱ)  ↝ⁱ λ x →  Eⁱ , aⁱ˙ x)  →
                    ⊨  ⤇ᵒ (∃ᵒ x , ◎⟨ i ⟩ aⁱ˙ x)
    ε↝-◎⟨⟩-⤇ᵒ-∃ᵒ Eε↝Eax =  ↝-◎⟨⟩-⤇ᵒ-∃ᵒ Eε↝Eax ◎⟨⟩-ε

    ↝-◎⟨⟩-⤇ᵒ :  (∀{Eⁱ} →  (Eⁱ , aⁱ)  ↝ⁱ λ (_ : ⊤₀) →  Eⁱ , bⁱ)  →
                ◎⟨ i ⟩ aⁱ  ⊨  ⤇ᵒ ◎⟨ i ⟩ bⁱ
    ↝-◎⟨⟩-⤇ᵒ Ea↝Eb =  ↝-◎⟨⟩-⤇ᵒ-∃ᵒ Ea↝Eb › ⤇ᵒ-mono π₁

    ε↝-◎⟨⟩-⤇ᵒ :  (∀{Eⁱ} →  (Eⁱ , εⁱ)  ↝ⁱ λ (_ : ⊤₀) →  Eⁱ , aⁱ)  →
                 ⊨  ⤇ᵒ ◎⟨ i ⟩ aⁱ
    ε↝-◎⟨⟩-⤇ᵒ Eε↝Ea =  ⤇ᵒ-mono π₁ $ ε↝-◎⟨⟩-⤇ᵒ-∃ᵒ Eε↝Ea

    -- ↝ⁱ into ⤇ᴱ on ◎⟨ i ⟩

    ↝-◎⟨⟩-⤇ᴱ :  ((E i , aⁱ)  ↝ⁱ λ x →  Fⁱ˙ x , bⁱ˙ x)  →
                ◎⟨ i ⟩ aⁱ  ⊨  E  ⤇ᴱ λ x →  upd˙ i (Fⁱ˙ x) E , ◎⟨ i ⟩ bⁱ˙ x
    ↝-◎⟨⟩-⤇ᴱ Ea↝Fxbx =  ↝-◎-⤇ᴱ $ upd˙-inj˙-↝ Ea↝Fxbx

    ε↝-◎⟨⟩-⤇ᴱ :  ((E i , εⁱ)  ↝ⁱ λ x →  Fⁱ˙ x , aⁱ˙ x)  →
                 ⊨  E  ⤇ᴱ λ x →  upd˙ i (Fⁱ˙ x) E , ◎⟨ i ⟩ aⁱ˙ x
    ε↝-◎⟨⟩-⤇ᴱ Eε↝Fax =  ↝-◎⟨⟩-⤇ᴱ Eε↝Fax ◎⟨⟩-ε

--------------------------------------------------------------------------------
-- Thunkᵒ, Shrunkᵒ :  Sized proposition under Thunk / Shrunk

Thunkᵒ Shrunkᵒ :  (Size →  Propᵒ ł) →  Size →  Propᵒ ł
Thunkᵒ Pᵒᶥ ι a =  Thunk (λ ι' → Pᵒᶥ ι' a) ι
Shrunkᵒ Pᵒᶥ ι a =  Shrunk (λ ι' → Pᵒᶥ ι' a) ι

abstract

  -- Monoᵒ for Thunkᵒ/Shrunkᵒ

  Thunkᵒ-Mono :  (∀{ι} → Monoᵒ $ Pᵒᶥ ι) →  Monoᵒ $ Thunkᵒ Pᵒᶥ ι
  Thunkᵒ-Mono MonoP a⊑b TPa .! =  MonoP a⊑b $ TPa .!

  Shrunkᵒ-Mono :  (∀{ι} → Monoᵒ $ Pᵒᶥ ι) →  Monoᵒ $ Shrunkᵒ Pᵒᶥ ι
  Shrunkᵒ-Mono MonoP a⊑b (§ Pa) =  § MonoP a⊑b Pa

  -- Monotonicity of Thunkᵒ/Shrunkᵒ

  Thunkᵒ-mono :  (∀{ι} → Pᵒᶥ ι ⊨ Qᵒᶥ ι) →  Thunkᵒ Pᵒᶥ ι ⊨ Thunkᵒ Qᵒᶥ ι
  Thunkᵒ-mono Pι⊨Qι TPa .! =  Pι⊨Qι $ TPa .!

  Thunkᵒ-mono✓ :  (∀{ι} → Pᵒᶥ ι ⊨✓ Qᵒᶥ ι) →  Thunkᵒ Pᵒᶥ ι ⊨✓ Thunkᵒ Qᵒᶥ ι
  Thunkᵒ-mono✓ Pι⊨✓Qι E✓a TPa .! =  Pι⊨✓Qι E✓a $ TPa .!

  Shrunkᵒ-mono :  (∀{ι} → Pᵒᶥ ι ⊨ Qᵒᶥ ι) →  Shrunkᵒ Pᵒᶥ ι ⊨ Shrunkᵒ Qᵒᶥ ι
  Shrunkᵒ-mono Pι⊨Qι (§ Pa) =  § Pι⊨Qι Pa

  Shrunkᵒ-mono✓ :  (∀{ι} → Pᵒᶥ ι ⊨✓ Qᵒᶥ ι) →  Shrunkᵒ Pᵒᶥ ι ⊨✓ Shrunkᵒ Qᵒᶥ ι
  Shrunkᵒ-mono✓ Pι⊨✓Qι E✓a (§ Pa) =  § Pι⊨✓Qι E✓a Pa

  -- Pull Thunkᵒ/Shrunkᵒ out of ∗ᵒ

  ∗ᵒThunkᵒ-out :  Pᵒ ∗ᵒ Thunkᵒ Qᵒᶥ ι  ⊨  Thunkᵒ (λ ι → Pᵒ ∗ᵒ Qᵒᶥ ι) ι
  ∗ᵒThunkᵒ-out (-, -, b∙c⊑a , Pa , TQa) .! =  -, -, b∙c⊑a , Pa , TQa .!

  Thunkᵒ∗ᵒ-out :  Thunkᵒ Pᵒᶥ ι ∗ᵒ Qᵒ  ⊨  Thunkᵒ (λ ι → Pᵒᶥ ι ∗ᵒ Qᵒ) ι
  Thunkᵒ∗ᵒ-out =  ∗ᵒ-comm › ∗ᵒThunkᵒ-out › λ{ TPQa .! → ∗ᵒ-comm $ TPQa .! }

  ∗ᵒShrunkᵒ-out :  Pᵒ ∗ᵒ Shrunkᵒ Qᵒᶥ ι  ⊨  Shrunkᵒ (λ ι → Pᵒ ∗ᵒ Qᵒᶥ ι) ι
  ∗ᵒShrunkᵒ-out (-, -, b∙c⊑a , Pa , § Qa) =  § (-, -, b∙c⊑a , Pa , Qa)

  Shrunkᵒ∗ᵒ-out :  Shrunkᵒ Pᵒᶥ ι ∗ᵒ Qᵒ  ⊨  Shrunkᵒ (λ ι → Pᵒᶥ ι ∗ᵒ Qᵒ) ι
  Shrunkᵒ∗ᵒ-out =  ∗ᵒ-comm › ∗ᵒShrunkᵒ-out › λ{ (§ PQa) → § ∗ᵒ-comm PQa }
