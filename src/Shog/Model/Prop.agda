--------------------------------------------------------------------------------
-- Semantic proposition
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level; ^ˡ_)
open import Shog.Model.RA using (RA)
-- Parametric over the global RA
module Shog.Model.Prop {ℓ : Level} (Globᴿᴬ : RA (^ˡ ℓ) (^ˡ ℓ) (^ˡ ℓ))
  where

open import Base.Few using (⊤; ⊥)
open import Base.Func using (_$_; _▷_; flip; _∈_)
open import Base.Prod using (Σ-syntax; _×_; _,_)
open import Base.Sum using (_⊎_; inj₀; inj₁)
open import Base.List using (List; _∷_; []; map)

open RA Globᴿᴬ renaming (Car to Glob) using (_≈_; _⊑_; ✓_; _∙_; ε; ⌞_⌟; _↝_;
  _↝ˢ_; sym˜; _»˜_; ⊑-refl; ⊑-trans; ⊑-respˡ; ⊑-respʳ; ✓-resp; ✓-mono; ∙-congʳ;
  ∙-monoˡ; ∙-monoʳ; ∙-mono; ∙-incrˡ; ∙-incrʳ; ∙-comm; ∙-assocˡ; ∙-assocʳ; ε-min;
  ⌞⌟-idem; ⌞⌟-mono; ✓-⌞⌟)

private variable
  ℓF :  Level

--------------------------------------------------------------------------------
-- Propᵒ: Semantic proposition

Monoᵒ :  ∀ (predᵒ : ∀ (a : Glob) →  ✓ a →  Set (^ˡ ℓ)) →  Set (^ˡ ℓ)
Monoᵒ predᵒ =  ∀ {a b ✓a ✓b} →  a ⊑ b →  predᵒ a ✓a →  predᵒ b ✓b

record  Propᵒ :  Set (^ˡ ^ˡ ℓ)  where
  constructor propᵒ
  field
    predᵒ :  ∀ (a : Glob) →  ✓ a →  Set (^ˡ ℓ)
    monoᵒ :  Monoᵒ predᵒ
open Propᵒ public

private variable
  X :  Set ℓ
  X^ :  Set (^ˡ ℓ)
  P Q R :  Propᵒ
  P˙ Q˙ :  X → Propᵒ
  x :  X
  F :  X →  Set ℓ
  ℓ' :  Level
  D :  Set ℓ'
  a b :  Glob
  B :  Glob → Set ℓ'

--------------------------------------------------------------------------------
-- ⊨: Entailment

infix 1 _⊨_
_⊨_ :  Propᵒ →  Propᵒ →  Set (^ˡ ℓ)
P ⊨ Q =  ∀ {a ✓a} →  P .predᵒ a ✓a →  Q .predᵒ a ✓a

abstract

  -- ⊨ is reflexive and transitive

  reflᵒ :  P ⊨ P
  reflᵒ Pa =  Pa

  infixr -1 _»ᵒ_
  _»ᵒ_ :  P ⊨ Q →  Q ⊨ R →  P ⊨ R
  (P⊨Q »ᵒ Q⊨R) Pa =  Pa ▷ P⊨Q ▷ Q⊨R

--------------------------------------------------------------------------------
-- ∀ᵒ˙, ∃ᵒ˙, ∀ᵒ˙', ∃ᵒ˙': Universal/existential quantification

-- For Set ℓ

∀ᵒ˙ ∃ᵒ˙ :  (X : Set ℓ) →  (X → Propᵒ) →  Propᵒ
∀ᵒ˙ _ P˙ .predᵒ a ✓a =  ∀ x →  P˙ x .predᵒ a ✓a
∀ᵒ˙ _ P˙ .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ ∀ᵒ˙ _ P˙ .predᵒ
  proof a⊑b ∀xPxa x =  P˙ x .monoᵒ a⊑b (∀xPxa x)
∃ᵒ˙ _ P˙ .predᵒ a ✓a =  Σ x ,  P˙ x .predᵒ a ✓a
∃ᵒ˙ _ P˙ .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ ∃ᵒ˙ _ P˙ .predᵒ
  proof a⊑b (x , Pxa) =  x ,  P˙ x .monoᵒ a⊑b Pxa

-- For Set (^ˡ ℓ)

∀^˙ ∃^˙ :  (X^ : Set (^ˡ ℓ)) →  (X^ → Propᵒ) →  Propᵒ
∀^˙ _ P˙ .predᵒ a ✓a =  ∀ x →  P˙ x .predᵒ a ✓a
∀^˙ _ P˙ .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ ∀^˙ _ P˙ .predᵒ
  proof a⊑b ∀xPxa x =  P˙ x .monoᵒ a⊑b (∀xPxa x)
∃^˙ _ P˙ .predᵒ a ✓a =  Σ x ,  P˙ x .predᵒ a ✓a
∃^˙ _ P˙ .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ ∃^˙ _ P˙ .predᵒ
  proof a⊑b (x , Pxa) =  x ,  P˙ x .monoᵒ a⊑b Pxa

∀ᵒ∈-syntax ∃ᵒ∈-syntax :  (X : Set ℓ) →  (X → Propᵒ) →  Propᵒ
∀^∈-syntax ∃^∈-syntax :  (X^ : Set (^ˡ ℓ)) →  (X^ → Propᵒ) →  Propᵒ
∀ᵒ∈-syntax =  ∀ᵒ˙
∃ᵒ∈-syntax =  ∃ᵒ˙
∀^∈-syntax =  ∀^˙
∃^∈-syntax =  ∃^˙

∀ᵒ-syntax ∃ᵒ-syntax :  (X → Propᵒ) →  Propᵒ
∀^-syntax ∃^-syntax :  (X^ → Propᵒ) →  Propᵒ
∀ᵒ-syntax =  ∀ᵒ˙ _
∃ᵒ-syntax =  ∃ᵒ˙ _
∀^-syntax =  ∀^˙ _
∃^-syntax =  ∃^˙ _

infix 3 ∀ᵒ∈-syntax ∃ᵒ∈-syntax ∀^∈-syntax ∃^∈-syntax
  ∀ᵒ-syntax ∃ᵒ-syntax ∀^-syntax ∃^-syntax
syntax ∀ᵒ∈-syntax X (λ x → P) =  ∀ᵒ x ∈ X , P
syntax ∃ᵒ∈-syntax X (λ x → P) =  ∃ᵒ x ∈ X , P
syntax ∀^∈-syntax X (λ x → P) =  ∀^ x ∈ X , P
syntax ∃^∈-syntax X (λ x → P) =  ∃^ x ∈ X , P
syntax ∀ᵒ-syntax (λ x → P) =  ∀ᵒ x , P
syntax ∃ᵒ-syntax (λ x → P) =  ∃ᵒ x , P
syntax ∀^-syntax (λ x → P) =  ∀^ x , P
syntax ∃^-syntax (λ x → P) =  ∃^ x , P

--------------------------------------------------------------------------------
-- ∧ᵒ: Conjunction
-- ∨ᵒ: Disjunction

infixr 7 _∧ᵒ_
infixr 6 _∨ᵒ_

_∧ᵒ_ _∨ᵒ_ :  Propᵒ →  Propᵒ →  Propᵒ
(P ∧ᵒ Q) .predᵒ a ✓a =  P .predᵒ a ✓a  ×  Q .predᵒ a ✓a
(P ∧ᵒ Q) .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ (P ∧ᵒ Q) .predᵒ
  proof a⊑b (Pa , Qa) =  P .monoᵒ a⊑b Pa , Q .monoᵒ a⊑b Qa
(P ∨ᵒ Q) .predᵒ a ✓a =  P .predᵒ a ✓a  ⊎  Q .predᵒ a ✓a
(P ∨ᵒ Q) .monoᵒ =  proof
 where abstract
  proof :  Monoᵒ $ (P ∨ᵒ Q) .predᵒ
  proof a⊑b (inj₀ Pa) =  inj₀ $ P .monoᵒ a⊑b Pa
  proof a⊑b (inj₁ Qa) =  inj₁ $ Q .monoᵒ a⊑b Qa

--------------------------------------------------------------------------------
-- ⊤ᵒ: Truth
-- ⊥ᵒ: Falsehood

⊤ᵒ ⊥ᵒ :  Propᵒ
⊤ᵒ .predᵒ _ _ =  ⊤
⊤ᵒ .monoᵒ _ _ =  _
⊥ᵒ .predᵒ _ _ =  ⊥
⊥ᵒ .monoᵒ _ ()

--------------------------------------------------------------------------------
-- ⌜ ⌝^: Set embedding

⌜_⌝^ :  Set (^ˡ ℓ) →  Propᵒ
⌜ X ⌝^ .predᵒ _ _ =  X
⌜ _ ⌝^ .monoᵒ _ x =  x

--------------------------------------------------------------------------------
-- →ᵒ: Implication

infixr 5 _→ᵒ_
_→ᵒ_ :  Propᵒ → Propᵒ → Propᵒ
(P →ᵒ Q) .predᵒ a _ =  ∀ {b ✓b} →  a ⊑ b →  P .predᵒ b ✓b →  Q .predᵒ b ✓b
(P →ᵒ Q) .monoᵒ {✓a = ✓a} {✓b} =  proof {✓a = ✓a} {✓b}
 where abstract
  proof :  Monoᵒ $ (P →ᵒ Q) .predᵒ
  proof a⊑b P→Qa b⊑c =  P→Qa (⊑-trans a⊑b b⊑c)

--------------------------------------------------------------------------------
-- ∗ᵒ: Separating conjunction

infixr 7 _∗ᵒ_
_∗ᵒ_ :  Propᵒ → Propᵒ → Propᵒ
(P ∗ᵒ Q) .predᵒ a _ =  Σ b , Σ c , Σ ✓b , Σ ✓c ,
  b ∙ c ≈ a  ×  P .predᵒ b ✓b  ×  Q .predᵒ c ✓c
(P ∗ᵒ Q) .monoᵒ {✓a = ✓a} {✓b} =  proof {✓a = ✓a} {✓b}
 where abstract
  proof :  Monoᵒ $ (P ∗ᵒ Q) .predᵒ
  proof {✓b = ✓b} a⊑b@(c , c∙a≈b) (d , e , _ , _ , d∙e≈a , Pd , Qe) =
    c ∙ d , e ,
    (flip ✓-mono ✓b $ ⊑-respʳ c∙a≈b $ ∙-monoʳ $ e , (∙-comm »˜ d∙e≈a)) ,
    _ , (∙-assocˡ »˜ ∙-congʳ d∙e≈a »˜ c∙a≈b) ,
    P .monoᵒ ∙-incrˡ Pd , Qe

--------------------------------------------------------------------------------
-- [∗ᵒ]: Iterated separating conjunction

[∗ᵒ] :  List Propᵒ →  Propᵒ
[∗ᵒ] [] =  ⊤ᵒ
[∗ᵒ] (P ∷ Ps) =  P ∗ᵒ [∗ᵒ] Ps

-- [∗ᵒ] with map

[∗ᵒ]-map :  (D → Propᵒ) →  List D →  Propᵒ
[∗ᵒ]-map P˙ ds =  [∗ᵒ] (map P˙ ds)

[∗ᵒ]-map-syntax :  (D → Propᵒ) →  List D →  Propᵒ
[∗ᵒ]-map-syntax =  [∗ᵒ]-map

infix 8 [∗ᵒ]-map-syntax
syntax [∗ᵒ]-map-syntax (λ d → P) ds =  [∗ᵒ d ∈ ds ] P

--------------------------------------------------------------------------------
-- -∗ᵒ: Magic wand

infixr 5 _-∗ᵒ_
_-∗ᵒ_ :  Propᵒ → Propᵒ → Propᵒ
(P -∗ᵒ Q) .predᵒ a _ =  ∀ {b c ✓c ✓c∙b} →  a ⊑ b →
  P .predᵒ c ✓c → Q .predᵒ (c ∙ b) ✓c∙b
(P -∗ᵒ Q) .monoᵒ {✓a = ✓a} {✓b} =  proof {✓a = ✓a} {✓b}
 where abstract
  proof :  Monoᵒ $ (P -∗ᵒ Q) .predᵒ
  proof a⊑b P-∗Qa b⊑c Pc =  P-∗Qa (⊑-trans a⊑b b⊑c) Pc

--------------------------------------------------------------------------------
-- |=>ᵒ: Update modality

infix 8 |=>ᵒ_
|=>ᵒ_ :  Propᵒ → Propᵒ
(|=>ᵒ P) .predᵒ a _ =  ∀ c →  ✓ c ∙ a →  Σ b , Σ ✓b ,  ✓ c ∙ b  ×  P .predᵒ b ✓b
(|=>ᵒ P) .monoᵒ {✓a = ✓a} {✓b} =  proof {✓a = ✓a} {✓b}
 where abstract
  proof :  Monoᵒ $ (|=>ᵒ P) .predᵒ
  proof (d , d∙a≈b) |=>Pa e ✓e∙b with
    |=>Pa (e ∙ d) $ flip ✓-resp ✓e∙b $ ∙-congʳ (sym˜ d∙a≈b) »˜ ∙-assocʳ
  ... | (c , _ , ✓ed∙c , Pc) =  c , _ ,
    (flip ✓-mono ✓ed∙c $ ∙-monoˡ ∙-incrʳ) , Pc

--------------------------------------------------------------------------------
-- □ᵒ: Persistence modality

infix 8 □ᵒ_
□ᵒ_ :  Propᵒ → Propᵒ
(□ᵒ P) .predᵒ a ✓a =  P .predᵒ ⌞ a ⌟ (✓-⌞⌟ ✓a)
(□ᵒ P) .monoᵒ {✓a = ✓a} {✓b} =  proof {✓a = ✓a} {✓b}
 where abstract
  proof :  Monoᵒ $ (□ᵒ P) .predᵒ
  proof a⊑b P⌞a⌟ =  P .monoᵒ (⌞⌟-mono a⊑b) P⌞a⌟

--------------------------------------------------------------------------------
-- own: Owning a resource

own :  Glob →  Propᵒ
own a .predᵒ b _ =  a ⊑ b
own a .monoᵒ {✓a = ✓a} {✓b} =  proof {✓a = ✓a} {✓b}
 where abstract
  proof :  Monoᵒ $ own a .predᵒ
  proof b⊑c a⊑b =  ⊑-trans a⊑b b⊑c

abstract

  own-resp :  a ≈ b →  own a ⊨ own b
  own-resp a≈b a⊑c =  ⊑-respˡ a≈b a⊑c

  own-mono :  a ⊑ b →  own b ⊨ own a
  own-mono a⊑b b⊑c =  ⊑-trans a⊑b b⊑c

  own-∙⇒∗ :  own (a ∙ b) ⊨ own a ∗ᵒ own b
  own-∙⇒∗ {a = a} {b} {c} {✓c} ab⊑c@(d , d∙ab≈c) =  d ∙ a , b ,
    (flip ✓-mono ✓c $ ⊑-respʳ d∙ab≈c $ ∙-monoʳ ∙-incrʳ) ,
    (flip ✓-mono ✓c $ ⊑-trans ∙-incrˡ ab⊑c) , (∙-assocˡ »˜ d∙ab≈c) ,
    ∙-incrˡ , ⊑-refl

  own-∗⇒∙ :  own a ∗ᵒ own b ⊨ own (a ∙ b)
  own-∗⇒∙ {a = a} {b} (a' , b' , _ , _ , a'∙b'≈c , a⊑a' , b⊑b') =
    ⊑-respʳ a'∙b'≈c (∙-mono a⊑a' b⊑b')

  own-ε-intro :  P ⊨ own ε
  own-ε-intro _ =  ε-min

  own-⌞⌟-□ :  own ⌞ a ⌟ ⊨ □ᵒ own ⌞ a ⌟
  own-⌞⌟-□ ⌞a⌟⊑b =  ⊑-respˡ ⌞⌟-idem $ ⌞⌟-mono ⌞a⌟⊑b

  own-⌞⌟-□' :  ⌞ a ⌟ ≈ a →  own a ⊨ □ᵒ own a
  own-⌞⌟-□' ⌞a⌟≈a a⊑b =  ⊑-respˡ ⌞a⌟≈a $ ⌞⌟-mono a⊑b

  own⇒✓ :  own a ⊨ ⌜ ✓ a ⌝^
  own⇒✓ {✓a = ✓b} a⊑b =  ✓-mono a⊑b ✓b

  own-↝ :  a ↝ b →  own a ⊨ |=>ᵒ own b
  own-↝ {b = b} a↝b {✓a = ✓a'} (c , c∙a≈a') d ✓d∙a' =  b , ✓-mono ∙-incrˡ ✓d∙b ,
    ✓d∙b , ⊑-refl
   where
    ✓d∙b :  ✓ d ∙ b
    ✓d∙b =  ✓-mono (∙-monoˡ ∙-incrʳ) $ a↝b (d ∙ c) $ flip ✓-resp ✓d∙a' $
      ∙-congʳ (sym˜ c∙a≈a') »˜ ∙-assocʳ

  own-↝ˢ :  a ↝ˢ B →  own a ⊨ |=>ᵒ (∃^ b , ⌜ b ∈ B ⌝^ ∧ᵒ own b)
  own-↝ˢ a↝B {✓a = ✓a'} (c , c∙a≈a') d ✓d∙a' with a↝B (d ∙ c) $
    flip ✓-resp ✓d∙a' $ ∙-congʳ (sym˜ c∙a≈a') »˜ ∙-assocʳ
  ... | b , b∈B , ✓d∙cb =  b , ✓-mono ∙-incrˡ ✓d∙b , ✓d∙b , b , b∈B , ⊑-refl
   where
    ✓d∙b :  ✓ d ∙ b
    ✓d∙b =  ✓-mono (∙-monoˡ ∙-incrʳ) ✓d∙cb
