--------------------------------------------------------------------------------
-- Semantic proposition
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level; 2ᴸ)
open import Shog.Model.RA using (RA)
-- Parametric over the global RA
module Shog.Model.Prop (GlobRA : RA 2ᴸ 2ᴸ 2ᴸ) where

open import Base.Few using (⊤; ⊥)
open import Base.Func using (_$_; _▷_; flip; _∈_)
open import Base.Prod using (∑-syntax; _×_; _,_)
open import Base.Sum using (_⊎_; inj₀; inj₁)
open import Base.List using (List; _∷_; []; map)

open RA GlobRA renaming (Car to Glob) using (_≈_; _⊑_; ✓_; _∙_; ε; ⌞_⌟; _↝_;
  _↝ˢ_; ◠˜_; _◇˜_; ≈⇒⊑; ⊑-refl; ⊑-trans; ⊑-respˡ; ⊑-respʳ; ✓-resp; ✓-mono;
  ∙-congʳ; ∙-monoˡ; ∙-monoʳ; ∙-mono; ∙-incrʳ; ∙-comm; ∙-assocˡ; ∙-assocʳ; ε-min;
  ⌞⌟-idem; ⌞⌟-mono; ✓-⌞⌟)

--------------------------------------------------------------------------------
-- Propᵒ: Semantic proposition

-- Monoᵒ !ᵒ :  !ᵒ is monotone over the resource
Monoᵒ :  (Glob → Set₂) →  Set₂
Monoᵒ !ᵒ =  ∀ {a b} →  a ⊑ b →  !ᵒ a →  !ᵒ b

record  Propᵒ :  Set₃  where
  field
    -- Predicate, parametrized over a resource a that is valid
    !ᵒ :  Glob →  Set₂
    -- !ᵒ is monotone over the resource
    monoᵒ :  Monoᵒ !ᵒ

  abstract
    -- Change the resource of !ᵒ into an equivalent one
    congᵒ :  ∀ {a b} →  a ≈ b →  !ᵒ a →  !ᵒ b
    congᵒ a≈b =  monoᵒ (≈⇒⊑ a≈b)

open Propᵒ public

private variable
  ℓB :  Level
  X₀ :  Set₀
  X₁ :  Set₁
  X₂ :  Set₂
  Pᵒ Qᵒ Rᵒ :  Propᵒ
  a b c :  Glob
  B :  Glob → Set ℓB

--------------------------------------------------------------------------------
-- ⊨: Entailment

infix 1 _⊨_ _⊨'_
_⊨_ _⊨'_ :  Propᵒ →  Propᵒ →  Set₂
Pᵒ ⊨ Qᵒ =  ∀ {a} →  ✓ a →  Pᵒ .!ᵒ a →  Qᵒ .!ᵒ a
Pᵒ ⊨' Qᵒ =  ∀ {a} →  Pᵒ .!ᵒ a →  Qᵒ .!ᵒ a

--------------------------------------------------------------------------------
-- Universal/existential quantification

-- For Set₀

∀₀˙ ∃₀˙ :  (X₀ → Propᵒ) →  Propᵒ
∀₀˙ Pᵒ˙ .!ᵒ a =  ∀ x →  Pᵒ˙ x .!ᵒ a
∀₀˙ Pᵒ˙ .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ ∀₀˙ Pᵒ˙ .!ᵒ
  proof a⊑b ∀xPxa x =  Pᵒ˙ x .monoᵒ a⊑b (∀xPxa x)
∃₀˙ Pᵒ˙ .!ᵒ a =  ∑ x ,  Pᵒ˙ x .!ᵒ a
∃₀˙ Pᵒ˙ .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ ∃₀˙ Pᵒ˙ .!ᵒ
  proof a⊑b (x , Pxa) =  x ,  Pᵒ˙ x .monoᵒ a⊑b Pxa

-- For Set₁

∀₁˙ ∃₁˙ : (X₁ → Propᵒ) →  Propᵒ
∀₁˙ Pᵒ˙ .!ᵒ a =  ∀ x →  Pᵒ˙ x .!ᵒ a
∀₁˙ Pᵒ˙ .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ ∀₁˙ Pᵒ˙ .!ᵒ
  proof a⊑b ∀xPxa x =  Pᵒ˙ x .monoᵒ a⊑b (∀xPxa x)
∃₁˙ Pᵒ˙ .!ᵒ a =  ∑ x ,  Pᵒ˙ x .!ᵒ a
∃₁˙ Pᵒ˙ .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ ∃₁˙ Pᵒ˙ .!ᵒ
  proof a⊑b (x , Pxa) =  x ,  Pᵒ˙ x .monoᵒ a⊑b Pxa

-- For Set₂

∀₂˙ ∃₂˙ :  (X₂ → Propᵒ) →  Propᵒ
∀₂˙ Pᵒ˙ .!ᵒ a =  ∀ x →  Pᵒ˙ x .!ᵒ a
∀₂˙ Pᵒ˙ .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ ∀₂˙ Pᵒ˙ .!ᵒ
  proof a⊑b ∀xPxa x =  Pᵒ˙ x .monoᵒ a⊑b (∀xPxa x)
∃₂˙ Pᵒ˙ .!ᵒ a =  ∑ x ,  Pᵒ˙ x .!ᵒ a
∃₂˙ Pᵒ˙ .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ ∃₂˙ Pᵒ˙ .!ᵒ
  proof a⊑b (x , Pxa) =  x ,  Pᵒ˙ x .monoᵒ a⊑b Pxa

∀₀∈-syntax ∃₀∈-syntax ∀₀-syntax ∃₀-syntax :  (X₀ → Propᵒ) →  Propᵒ
∀₀∈-syntax =  ∀₀˙
∃₀∈-syntax =  ∃₀˙
∀₀-syntax =  ∀₀˙
∃₀-syntax =  ∃₀˙
∀₁∈-syntax ∃₁∈-syntax ∀₁-syntax ∃₁-syntax :  (X₁ → Propᵒ) →  Propᵒ
∀₁∈-syntax =  ∀₁˙
∃₁∈-syntax =  ∃₁˙
∀₁-syntax =  ∀₁˙
∃₁-syntax =  ∃₁˙
∀₂∈-syntax ∃₂∈-syntax ∀₂-syntax ∃₂-syntax :  (X₂ → Propᵒ) →  Propᵒ
∀₂∈-syntax =  ∀₂˙
∃₂∈-syntax =  ∃₂˙
∀₂-syntax =  ∀₂˙
∃₂-syntax =  ∃₂˙

infix 3 ∀₁∈-syntax ∃₁∈-syntax ∀₁-syntax ∃₁-syntax
  ∀₀∈-syntax ∃₀∈-syntax ∀₀-syntax ∃₀-syntax
  ∀₂∈-syntax ∃₂∈-syntax ∀₂-syntax ∃₂-syntax
syntax ∀₀∈-syntax {X₀ = X₀} (λ x → Pᵒ) =  ∀₀ x ∈ X₀ , Pᵒ
syntax ∃₀∈-syntax {X₀ = X₀} (λ x → Pᵒ) =  ∃₀ x ∈ X₀ , Pᵒ
syntax ∀₀-syntax (λ x → Pᵒ) =  ∀₀ x , Pᵒ
syntax ∃₀-syntax (λ x → Pᵒ) =  ∃₀ x , Pᵒ
syntax ∀₁∈-syntax {X₁ = X₁} (λ x → Pᵒ) =  ∀₁ x ∈ X₁ , Pᵒ
syntax ∃₁∈-syntax {X₁ = X₁} (λ x → Pᵒ) =  ∃₁ x ∈ X₁ , Pᵒ
syntax ∀₁-syntax (λ x → Pᵒ) =  ∀₁ x , Pᵒ
syntax ∃₁-syntax (λ x → Pᵒ) =  ∃₁ x , Pᵒ
syntax ∀₂∈-syntax {X₂ = X₂} (λ x → Pᵒ) =  ∀₂ x ∈ X₂ , Pᵒ
syntax ∃₂∈-syntax {X₂ = X₂} (λ x → Pᵒ) =  ∃₂ x ∈ X₂ , Pᵒ
syntax ∀₂-syntax (λ x → Pᵒ) =  ∀₂ x , Pᵒ
syntax ∃₂-syntax (λ x → Pᵒ) =  ∃₂ x , Pᵒ

--------------------------------------------------------------------------------
-- ∧ᵒ: Conjunction
-- ∨ᵒ: Disjunction

infixr 7 _∧ᵒ_
infixr 6 _∨ᵒ_

_∧ᵒ_ _∨ᵒ_ :  Propᵒ →  Propᵒ →  Propᵒ
(Pᵒ ∧ᵒ Qᵒ) .!ᵒ a =  Pᵒ .!ᵒ a  ×  Qᵒ .!ᵒ a
(Pᵒ ∧ᵒ Qᵒ) .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ (Pᵒ ∧ᵒ Qᵒ) .!ᵒ
  proof a⊑b (Pa , Qa) =  Pᵒ .monoᵒ a⊑b Pa , Qᵒ .monoᵒ a⊑b Qa
(Pᵒ ∨ᵒ Qᵒ) .!ᵒ a =  Pᵒ .!ᵒ a  ⊎  Qᵒ .!ᵒ a
(Pᵒ ∨ᵒ Qᵒ) .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ (Pᵒ ∨ᵒ Qᵒ) .!ᵒ
  proof a⊑b (inj₀ Pa) =  inj₀ $ Pᵒ .monoᵒ a⊑b Pa
  proof a⊑b (inj₁ Qa) =  inj₁ $ Qᵒ .monoᵒ a⊑b Qa

--------------------------------------------------------------------------------
-- ⊤ᵒ: Truth
-- ⊥ᵒ: Falsehood

⊤ᵒ ⊥ᵒ :  Propᵒ
⊤ᵒ .!ᵒ _ =  ⊤
⊤ᵒ .monoᵒ _ =  _
⊥ᵒ .!ᵒ _ =  ⊥
⊥ᵒ .monoᵒ _ ()

--------------------------------------------------------------------------------
-- ⌜ ⌝₂: Set embedding

⌜_⌝₂ :  Set₂ →  Propᵒ
⌜ X₂ ⌝₂ .!ᵒ _ =  X₂
⌜ _ ⌝₂ .monoᵒ _ x =  x

--------------------------------------------------------------------------------
-- →ᵒ: Implication

infixr 5 _→ᵒ_
_→ᵒ_ :  Propᵒ → Propᵒ → Propᵒ
(Pᵒ →ᵒ Qᵒ) .!ᵒ a =  ∀ {b} →  a ⊑ b →  ✓ b →  Pᵒ .!ᵒ b →  Qᵒ .!ᵒ b
(Pᵒ →ᵒ Qᵒ) .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ (Pᵒ →ᵒ Qᵒ) .!ᵒ
  proof a⊑b P→Qa b⊑c =  P→Qa (⊑-trans a⊑b b⊑c)

--------------------------------------------------------------------------------
-- ∗ᵒ: Separating conjunction

infixr 7 _∗ᵒ_
_∗ᵒ_ :  Propᵒ → Propᵒ → Propᵒ
(Pᵒ ∗ᵒ Qᵒ) .!ᵒ a =  ∑ b , ∑ c , b ∙ c ⊑ a × Pᵒ .!ᵒ b  ×  Qᵒ .!ᵒ c
(Pᵒ ∗ᵒ Qᵒ) .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ (Pᵒ ∗ᵒ Qᵒ) .!ᵒ
  proof a⊑a' (b , c , b∙c⊑a , Pd , Qe) =  b , c , ⊑-trans b∙c⊑a a⊑a' , Pd , Qe

--------------------------------------------------------------------------------
-- -∗ᵒ: Magic wand

infixr 5 _-∗ᵒ_
_-∗ᵒ_ :  Propᵒ → Propᵒ → Propᵒ
(Pᵒ -∗ᵒ Qᵒ) .!ᵒ a =  ∀ {b c} →  a ⊑ b →  ✓ c ∙ b →  Pᵒ .!ᵒ c → Qᵒ .!ᵒ (c ∙ b)
(Pᵒ -∗ᵒ Qᵒ) .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ (Pᵒ -∗ᵒ Qᵒ) .!ᵒ
  proof a⊑b P-∗Qa b⊑c Pc =  P-∗Qa (⊑-trans a⊑b b⊑c) Pc

--------------------------------------------------------------------------------
-- |=>ᵒ: Update modality

infix 8 |=>ᵒ_
|=>ᵒ_ :  Propᵒ → Propᵒ
(|=>ᵒ Pᵒ) .!ᵒ a =  ∀ c →  ✓ c ∙ a →  ∑ b , ✓ c ∙ b × Pᵒ .!ᵒ b
(|=>ᵒ Pᵒ) .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ (|=>ᵒ Pᵒ) .!ᵒ
  proof (d , d∙a≈b) |=>Pa e ✓e∙b  with
    |=>Pa (e ∙ d) $ flip ✓-resp ✓e∙b $ ∙-congʳ (◠˜ d∙a≈b) ◇˜ ∙-assocʳ
  ... | (c , ✓ed∙c , Pc) =  c , flip ✓-mono ✓ed∙c (∙-monoˡ ∙-incrʳ) , Pc

--------------------------------------------------------------------------------
-- □ᵒ: Persistence modality

infix 8 □ᵒ_
□ᵒ_ :  Propᵒ → Propᵒ
(□ᵒ Pᵒ) .!ᵒ a =  Pᵒ .!ᵒ ⌞ a ⌟
(□ᵒ Pᵒ) .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ (□ᵒ Pᵒ) .!ᵒ
  proof a⊑b P⌞a⌟ =  Pᵒ .monoᵒ (⌞⌟-mono a⊑b) P⌞a⌟

--------------------------------------------------------------------------------
-- Own: Owning a resource

Own :  Glob →  Propᵒ
Own a .!ᵒ b =  a ⊑ b
Own a .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ Own a .!ᵒ
  proof b⊑c a⊑b =  ⊑-trans a⊑b b⊑c

abstract

  Own-resp :  a ≈ b →  Own a ⊨' Own b
  Own-resp a≈b a⊑c =  ⊑-respˡ a≈b a⊑c

  Own-mono :  a ⊑ b →  Own b ⊨' Own a
  Own-mono a⊑b b⊑c =  ⊑-trans a⊑b b⊑c

  Own-∙⇒∗ :  Own (a ∙ b) ⊨' Own a ∗ᵒ Own b
  Own-∙⇒∗ a∙b⊑c =  _ , _ , a∙b⊑c , ⊑-refl , ⊑-refl

  Own-∗⇒∙ :  Own a ∗ᵒ Own b ⊨' Own (a ∙ b)
  Own-∗⇒∙ (_ , _ , a'∙b'⊑c , a⊑a' , b⊑b') =
    ⊑-trans (∙-mono a⊑a' b⊑b') a'∙b'⊑c

  Own-ε-intro :  Pᵒ ⊨' Own ε
  Own-ε-intro _ =  ε-min

  Own-⌞⌟-□ :  ⌞ a ⌟ ≈ a →  Own a ⊨' □ᵒ Own a
  Own-⌞⌟-□ ⌞a⌟≈a a⊑b =  ⊑-respˡ ⌞a⌟≈a $ ⌞⌟-mono a⊑b

  Own⇒✓ :  Own a ⊨ ⌜ ✓ a ⌝₂
  Own⇒✓ ✓b a⊑b =  ✓-mono a⊑b ✓b

  Own-↝ :  a ↝ b →  Own a ⊨' |=>ᵒ Own b
  Own-↝ {b = b} a↝b (c , c∙a≈a') d ✓d∙a' =  b , ✓d∙b , ⊑-refl
   where
    ✓d∙b :  ✓ d ∙ b
    ✓d∙b =  ✓-mono (∙-monoˡ ∙-incrʳ) $ a↝b (d ∙ c) $ flip ✓-resp ✓d∙a' $
      ∙-congʳ (◠˜ c∙a≈a') ◇˜ ∙-assocʳ

  Own-↝ˢ :  a ↝ˢ B →  Own a ⊨ |=>ᵒ (∃₂ b , ⌜ b ∈ B ⌝₂ ∧ᵒ Own b)
  Own-↝ˢ a↝B ✓a' (c , c∙a≈a') d ✓d∙a'  with a↝B (d ∙ c) $
    flip ✓-resp ✓d∙a' $ ∙-congʳ (◠˜ c∙a≈a') ◇˜ ∙-assocʳ
  ... | b , b∈B , ✓d∙cb =  b , ✓-mono (∙-monoˡ ∙-incrʳ) ✓d∙cb , b , b∈B , ⊑-refl
