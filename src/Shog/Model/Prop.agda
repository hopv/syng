--------------------------------------------------------------------------------
-- Semantic proposition
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level; ^_; ○)
open import Shog.Model.RA using (RA)
-- Parametric over the global RA
module Shog.Model.Prop (GlobRA : RA (^ ^ ○) (^ ^ ○) (^ ^ ○)) where

open import Base.Few using (⊤; ⊥)
open import Base.Func using (_$_; _▷_; flip; _∈_)
open import Base.Prod using (∑-syntax; _×_; _,_)
open import Base.Sum using (_⊎_; inj₀; inj₁)
open import Base.List using (List; _∷_; []; map)

open RA GlobRA renaming (Car to Glob) using (_≈_; _⊑_; ✓_; _∙_; ε; ⌞_⌟; _↝_;
  _↝ˢ_; ◠˜_; _◇˜_; ≈⇒⊑; ⊑-refl; ⊑-trans; ⊑-respˡ; ⊑-respʳ; ✓-resp; ✓-mono;
  ∙-congʳ; ∙-monoˡ; ∙-monoʳ; ∙-mono; ∙-incrˡ; ∙-incrʳ; ∙-comm; ∙-assocˡ;
  ∙-assocʳ; ε-min; ⌞⌟-idem; ⌞⌟-mono; ✓-⌞⌟)

--------------------------------------------------------------------------------
-- Propᵒ: Semantic proposition

-- Monoᵒ F :  F is monotone over the resource, ignoring the validity data
Monoᵒ :  (∀ a → ✓ a → Set (^ ^ ○)) →  Set (^ ^ ○)
Monoᵒ F =  ∀ {a b ✓a ✓b} →  a ⊑ b →  F a ✓a →  F b ✓b

record  Propᵒ :  Set (^ ^ ^ ○)  where
  field
    -- Predicate, parametrized over a resource a that is valid
    !ᵒ :  ∀ (a : Glob) →  ✓ a →  Set (^ ^ ○)
    -- !ᵒ is monotone over the resource, ignoring the validity data
    monoᵒ :  Monoᵒ !ᵒ

  abstract
    -- Change the validity of !ᵒ
    renewᵒ :  ∀ {a ✓a ✓a'} →  !ᵒ a ✓a →  !ᵒ a ✓a'
    renewᵒ =  monoᵒ ⊑-refl
    -- Change the resource of !ᵒ into an equivalent one
    congᵒ :  ∀ {a b ✓a ✓b} →  a ≈ b →  !ᵒ a ✓a →  !ᵒ b ✓b
    congᵒ a≈b =  monoᵒ (≈⇒⊑ a≈b)
    -- congᵒ with the validity predicate specified
    congᵒ' :  ∀ {a b ✓b} a≈b →  !ᵒ a (✓-resp (◠˜ a≈b) ✓b) →  !ᵒ b ✓b
    congᵒ' a≈b =  congᵒ a≈b

open Propᵒ public

private variable
  ℓB :  Level
  X :  Set (^ ○)
  X^ :  Set (^ ^ ○)
  Pᵒ Qᵒ Rᵒ :  Propᵒ
  a b c :  Glob
  B :  Glob → Set ℓB

--------------------------------------------------------------------------------
-- ⊨: Entailment

infix 1 _⊨_
_⊨_ :  Propᵒ →  Propᵒ →  Set (^ ^ ○)
Pᵒ ⊨ Qᵒ =  ∀ {a ✓a} →  Pᵒ .!ᵒ a ✓a →  Qᵒ .!ᵒ a ✓a

abstract

  -- ⊨ is reflexive and transitive

  reflᵒ :  Pᵒ ⊨ Pᵒ
  reflᵒ Pa =  Pa

  infixr -1 _◇ᵒ_
  _◇ᵒ_ :  Pᵒ ⊨ Qᵒ →  Qᵒ ⊨ Rᵒ →  Pᵒ ⊨ Rᵒ
  (P⊨Q ◇ᵒ Q⊨R) Pa =  Pa ▷ P⊨Q ▷ Q⊨R

--------------------------------------------------------------------------------
-- ∀ᵒ˙, ∃ᵒ˙, ∀ᵒ˙', ∃ᵒ˙': Universal/existential quantification

-- For Set (^ ○)

∀ᵒ˙ ∃ᵒ˙ : (X → Propᵒ) →  Propᵒ
∀ᵒ˙ Pᵒ˙ .!ᵒ a ✓a =  ∀ x →  Pᵒ˙ x .!ᵒ a ✓a
∀ᵒ˙ Pᵒ˙ .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ ∀ᵒ˙ Pᵒ˙ .!ᵒ
  proof a⊑b ∀xPxa x =  Pᵒ˙ x .monoᵒ a⊑b (∀xPxa x)
∃ᵒ˙ Pᵒ˙ .!ᵒ a ✓a =  ∑ x ,  Pᵒ˙ x .!ᵒ a ✓a
∃ᵒ˙ Pᵒ˙ .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ ∃ᵒ˙ Pᵒ˙ .!ᵒ
  proof a⊑b (x , Pxa) =  x ,  Pᵒ˙ x .monoᵒ a⊑b Pxa

-- For Set (^ ^ ○)

∀^˙ ∃^˙ :  (X^ → Propᵒ) →  Propᵒ
∀^˙ Pᵒ˙ .!ᵒ a ✓a =  ∀ x →  Pᵒ˙ x .!ᵒ a ✓a
∀^˙ Pᵒ˙ .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ ∀^˙ Pᵒ˙ .!ᵒ
  proof a⊑b ∀xPxa x =  Pᵒ˙ x .monoᵒ a⊑b (∀xPxa x)
∃^˙ Pᵒ˙ .!ᵒ a ✓a =  ∑ x ,  Pᵒ˙ x .!ᵒ a ✓a
∃^˙ Pᵒ˙ .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ ∃^˙ Pᵒ˙ .!ᵒ
  proof a⊑b (x , Pxa) =  x ,  Pᵒ˙ x .monoᵒ a⊑b Pxa

∀ᵒ∈-syntax ∃ᵒ∈-syntax ∀ᵒ-syntax ∃ᵒ-syntax :  (X → Propᵒ) →  Propᵒ
∀ᵒ∈-syntax =  ∀ᵒ˙
∃ᵒ∈-syntax =  ∃ᵒ˙
∀ᵒ-syntax =  ∀ᵒ˙
∃ᵒ-syntax =  ∃ᵒ˙
∀^∈-syntax ∃^∈-syntax ∀^-syntax ∃^-syntax :  (X^ → Propᵒ) →  Propᵒ
∀^∈-syntax =  ∀^˙
∃^∈-syntax =  ∃^˙
∀^-syntax =  ∀^˙
∃^-syntax =  ∃^˙

infix 3 ∀ᵒ∈-syntax ∃ᵒ∈-syntax ∀ᵒ-syntax ∃ᵒ-syntax
  ∀^∈-syntax ∃^∈-syntax ∀^-syntax ∃^-syntax
syntax ∀ᵒ∈-syntax {X = X} (λ x → Pᵒ) =  ∀ᵒ x ∈ X , Pᵒ
syntax ∃ᵒ∈-syntax {X = X} (λ x → Pᵒ) =  ∃ᵒ x ∈ X , Pᵒ
syntax ∀ᵒ-syntax (λ x → Pᵒ) =  ∀ᵒ x , Pᵒ
syntax ∃ᵒ-syntax (λ x → Pᵒ) =  ∃ᵒ x , Pᵒ
syntax ∀^∈-syntax {X^ = X^} (λ x → Pᵒ) =  ∀^ x ∈ X^ , Pᵒ
syntax ∃^∈-syntax {X^ = X^} (λ x → Pᵒ) =  ∃^ x ∈ X^ , Pᵒ
syntax ∀^-syntax (λ x → Pᵒ) =  ∀^ x , Pᵒ
syntax ∃^-syntax (λ x → Pᵒ) =  ∃^ x , Pᵒ

--------------------------------------------------------------------------------
-- ∧ᵒ: Conjunction
-- ∨ᵒ: Disjunction

infixr 7 _∧ᵒ_
infixr 6 _∨ᵒ_

_∧ᵒ_ _∨ᵒ_ :  Propᵒ →  Propᵒ →  Propᵒ
(Pᵒ ∧ᵒ Qᵒ) .!ᵒ a ✓a =  Pᵒ .!ᵒ a ✓a  ×  Qᵒ .!ᵒ a ✓a
(Pᵒ ∧ᵒ Qᵒ) .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ (Pᵒ ∧ᵒ Qᵒ) .!ᵒ
  proof a⊑b (Pa , Qa) =  Pᵒ .monoᵒ a⊑b Pa , Qᵒ .monoᵒ a⊑b Qa
(Pᵒ ∨ᵒ Qᵒ) .!ᵒ a ✓a =  Pᵒ .!ᵒ a ✓a  ⊎  Qᵒ .!ᵒ a ✓a
(Pᵒ ∨ᵒ Qᵒ) .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ (Pᵒ ∨ᵒ Qᵒ) .!ᵒ
  proof a⊑b (inj₀ Pa) =  inj₀ $ Pᵒ .monoᵒ a⊑b Pa
  proof a⊑b (inj₁ Qa) =  inj₁ $ Qᵒ .monoᵒ a⊑b Qa

--------------------------------------------------------------------------------
-- ⊤ᵒ: Truth
-- ⊥ᵒ: Falsehood

⊤ᵒ ⊥ᵒ :  Propᵒ
⊤ᵒ .!ᵒ _ _ =  ⊤
⊤ᵒ .monoᵒ _ _ =  _
⊥ᵒ .!ᵒ _ _ =  ⊥
⊥ᵒ .monoᵒ _ ()

--------------------------------------------------------------------------------
-- ⌜ ⌝^: Set embedding

⌜_⌝^ :  Set (^ ^ ○) →  Propᵒ
⌜ X ⌝^ .!ᵒ _ _ =  X
⌜ _ ⌝^ .monoᵒ _ x =  x

--------------------------------------------------------------------------------
-- →ᵒ: Implication

infixr 5 _→ᵒ_
_→ᵒ_ :  Propᵒ → Propᵒ → Propᵒ
(Pᵒ →ᵒ Qᵒ) .!ᵒ a _ =  ∀ {b ✓b} →  a ⊑ b →  Pᵒ .!ᵒ b ✓b →  Qᵒ .!ᵒ b ✓b
(Pᵒ →ᵒ Qᵒ) .monoᵒ {✓a = ✓a} {✓b} =  proof {✓a = ✓a} {✓b}
 where abstract
  proof :  Monoᵒ $ (Pᵒ →ᵒ Qᵒ) .!ᵒ
  proof a⊑b P→Qa b⊑c =  P→Qa (⊑-trans a⊑b b⊑c)

--------------------------------------------------------------------------------
-- ∗ᵒ: Separating conjunction

abstract

  ∙⊑-✓ˡ :  b ∙ c ⊑ a →  ✓ a →  ✓ b
  ∙⊑-✓ˡ b∙c⊑a ✓a =  ✓-mono (⊑-trans ∙-incrʳ b∙c⊑a) ✓a

  ∙⊑-✓ʳ :  b ∙ c ⊑ a →  ✓ a →  ✓ c
  ∙⊑-✓ʳ b∙c⊑a ✓a =  ✓-mono (⊑-trans ∙-incrˡ b∙c⊑a) ✓a

infixr 7 _∗ᵒ_
_∗ᵒ_ :  Propᵒ → Propᵒ → Propᵒ
(Pᵒ ∗ᵒ Qᵒ) .!ᵒ a ✓a =  ∑ b , ∑ c , ∑ b∙c⊑a ,
  Pᵒ .!ᵒ b (∙⊑-✓ˡ b∙c⊑a ✓a)  ×  Qᵒ .!ᵒ c (∙⊑-✓ʳ b∙c⊑a ✓a)
(Pᵒ ∗ᵒ Qᵒ) .monoᵒ {✓a = ✓a} {✓b} =  proof {✓a = ✓a} {✓b}
 where abstract
  proof :  Monoᵒ $ (Pᵒ ∗ᵒ Qᵒ) .!ᵒ
  proof a⊑a' (b , c , b∙c⊑a , Pd , Qe) =
    b , c , ⊑-trans b∙c⊑a a⊑a' , renewᵒ Pᵒ Pd , renewᵒ Qᵒ Qe

--------------------------------------------------------------------------------
-- -∗ᵒ: Magic wand

infixr 5 _-∗ᵒ_
_-∗ᵒ_ :  Propᵒ → Propᵒ → Propᵒ
(Pᵒ -∗ᵒ Qᵒ) .!ᵒ a _ =  ∀ {b c ✓c ✓c∙b} →  a ⊑ b →
  Pᵒ .!ᵒ c ✓c → Qᵒ .!ᵒ (c ∙ b) ✓c∙b
(Pᵒ -∗ᵒ Qᵒ) .monoᵒ {✓a = ✓a} {✓b} =  proof {✓a = ✓a} {✓b}
 where abstract
  proof :  Monoᵒ $ (Pᵒ -∗ᵒ Qᵒ) .!ᵒ
  proof a⊑b P-∗Qa b⊑c Pc =  P-∗Qa (⊑-trans a⊑b b⊑c) Pc

--------------------------------------------------------------------------------
-- |=>ᵒ: Update modality

abstract

  ✓-remˡ :  ✓ a ∙ b →  ✓ b
  ✓-remˡ ✓a∙b =  ✓-mono ∙-incrˡ ✓a∙b

infix 8 |=>ᵒ_
|=>ᵒ_ :  Propᵒ → Propᵒ
(|=>ᵒ Pᵒ) .!ᵒ a _ =  ∀ c →  ✓ c ∙ a →  ∑ b , ∑ ✓c∙b ,
  Pᵒ .!ᵒ b (✓-remˡ {c} {b} ✓c∙b)
(|=>ᵒ Pᵒ) .monoᵒ {✓a = ✓a} {✓b} =  proof {✓a = ✓a} {✓b}
 where abstract
  proof :  Monoᵒ $ (|=>ᵒ Pᵒ) .!ᵒ
  proof (d , d∙a≈b) |=>Pa e ✓e∙b  with
    |=>Pa (e ∙ d) $ flip ✓-resp ✓e∙b $ ∙-congʳ (◠˜ d∙a≈b) ◇˜ ∙-assocʳ
  ... | (c , ✓ed∙c , Pc) =  c , flip ✓-mono ✓ed∙c (∙-monoˡ ∙-incrʳ) ,
    renewᵒ Pᵒ Pc

--------------------------------------------------------------------------------
-- □ᵒ: Persistence modality

infix 8 □ᵒ_
□ᵒ_ :  Propᵒ → Propᵒ
(□ᵒ Pᵒ) .!ᵒ a ✓a =  Pᵒ .!ᵒ ⌞ a ⌟ (✓-⌞⌟ ✓a)
(□ᵒ Pᵒ) .monoᵒ {✓a = ✓a} {✓b} =  proof {✓a = ✓a} {✓b}
 where abstract
  proof :  Monoᵒ $ (□ᵒ Pᵒ) .!ᵒ
  proof a⊑b P⌞a⌟ =  Pᵒ .monoᵒ (⌞⌟-mono a⊑b) P⌞a⌟

--------------------------------------------------------------------------------
-- Own: Owning a resource

Own :  Glob →  Propᵒ
Own a .!ᵒ b _ =  a ⊑ b
Own a .monoᵒ {✓a = ✓a} {✓b} =  proof {✓a = ✓a} {✓b}
 where abstract
  proof :  Monoᵒ $ Own a .!ᵒ
  proof b⊑c a⊑b =  ⊑-trans a⊑b b⊑c

abstract

  Own-resp :  a ≈ b →  Own a ⊨ Own b
  Own-resp a≈b a⊑c =  ⊑-respˡ a≈b a⊑c

  Own-mono :  a ⊑ b →  Own b ⊨ Own a
  Own-mono a⊑b b⊑c =  ⊑-trans a⊑b b⊑c

  Own-∙⇒∗ :  Own (a ∙ b) ⊨ Own a ∗ᵒ Own b
  Own-∙⇒∗ a∙b⊑c =  _ , _ , a∙b⊑c , ⊑-refl , ⊑-refl

  Own-∗⇒∙ :  Own a ∗ᵒ Own b ⊨ Own (a ∙ b)
  Own-∗⇒∙ (_ , _ , a'∙b'⊑c , a⊑a' , b⊑b') =
    ⊑-trans (∙-mono a⊑a' b⊑b') a'∙b'⊑c

  Own-ε-intro :  Pᵒ ⊨ Own ε
  Own-ε-intro _ =  ε-min

  Own-⌞⌟-□ :  Own ⌞ a ⌟ ⊨ □ᵒ Own ⌞ a ⌟
  Own-⌞⌟-□ ⌞a⌟⊑b =  ⊑-respˡ ⌞⌟-idem $ ⌞⌟-mono ⌞a⌟⊑b

  Own-⌞⌟-□' :  ⌞ a ⌟ ≈ a →  Own a ⊨ □ᵒ Own a
  Own-⌞⌟-□' ⌞a⌟≈a a⊑b =  ⊑-respˡ ⌞a⌟≈a $ ⌞⌟-mono a⊑b

  Own⇒✓ :  Own a ⊨ ⌜ ✓ a ⌝^
  Own⇒✓ {✓a = ✓b} a⊑b =  ✓-mono a⊑b ✓b

  Own-↝ :  a ↝ b →  Own a ⊨ |=>ᵒ Own b
  Own-↝ {b = b} a↝b (c , c∙a≈a') d ✓d∙a' =  b , ✓d∙b , ⊑-refl
   where
    ✓d∙b :  ✓ d ∙ b
    ✓d∙b =  ✓-mono (∙-monoˡ ∙-incrʳ) $ a↝b (d ∙ c) $ flip ✓-resp ✓d∙a' $
      ∙-congʳ (◠˜ c∙a≈a') ◇˜ ∙-assocʳ

  Own-↝ˢ :  a ↝ˢ B →  Own a ⊨ |=>ᵒ (∃^ b , ⌜ b ∈ B ⌝^ ∧ᵒ Own b)
  Own-↝ˢ a↝B {✓a = ✓a'} (c , c∙a≈a') d ✓d∙a'  with a↝B (d ∙ c) $
    flip ✓-resp ✓d∙a' $ ∙-congʳ (◠˜ c∙a≈a') ◇˜ ∙-assocʳ
  ... | b , b∈B , ✓d∙cb =  b , ✓-mono (∙-monoˡ ∙-incrʳ) ✓d∙cb , b , b∈B , ⊑-refl
