--------------------------------------------------------------------------------
-- Semantic proposition
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level; sucˡ)
open import Shog.Model.RA using (RA)
-- Parametric over the global RA
module Shog.Model.Prop {ℓ : Level} (Globᴿᴬ : RA (sucˡ ℓ) (sucˡ ℓ) (sucˡ ℓ))
  where

open import Base.Few using (binary; 0₂; 1₂; absurd)
open import Base.Func using (_$_; _▷_; flip; _∘_)
open import Base.Prod using (Σ-syntax; _×_; _,_; proj₀; proj₁)
open import Base.List using (List; _∷_; []; map)

open RA Globᴿᴬ renaming (Car to Glob) using (_≈_; _⊑_; ✓_; _∙_; ε; ⌞_⌟; refl˜;
  sym˜; _»˜_; ⊑-refl; ⊑-trans; ⊑-respʳ; ≈⇒⊑; ✓-resp; ✓-mono; ✓-ε; ∙-congˡ;
  ∙-congʳ; ∙-monoˡ; ∙-monoʳ; ∙-incrˡ; ∙-incrʳ; ∙-comm; ∙-assocˡ; ∙-assocʳ;
  ∙-unitˡ; ⌞⌟-unitˡ; ⌞⌟-idem; ⌞⌟-decr; ⌞⌟-mono; ✓-⌞⌟)

--------------------------------------------------------------------------------
-- Propᵒ: Semantic proposition

Monoᵒ :  ∀ (predᵒ : ∀ (a : Glob) →  ✓ a →  Set (sucˡ ℓ)) →  Set (sucˡ ℓ)
Monoᵒ predᵒ =  ∀ {a b ✓a ✓b} →  a ⊑ b →  predᵒ a ✓a →  predᵒ b ✓b

record  Propᵒ :  Set (sucˡ (sucˡ ℓ))  where
  constructor propᵒ
  field
    predᵒ :  ∀ (a : Glob) →  ✓ a →  Set (sucˡ ℓ)
    monoᵒ :  Monoᵒ predᵒ
open Propᵒ

private variable
  X :  Set (sucˡ ℓ)
  P Q R :  Propᵒ
  P˙ Q˙ :  X → Propᵒ
  x :  X
  F :  X →  Set (sucˡ ℓ)
  ℓ' :  Level
  D :  Set ℓ'

--------------------------------------------------------------------------------
-- ⊨: Entailment

infix 1 _⊨_
_⊨_ :  Propᵒ →  Propᵒ →  Set (sucˡ ℓ)
P ⊨ Q =  ∀ {a ✓a} →  P .predᵒ a ✓a →  Q .predᵒ a ✓a

abstract

  -- ⊨ is reflexive and transitive

  reflᵒ :  P ⊨ P
  reflᵒ Pa =  Pa

  infixr -1 _»ᵒ_
  _»ᵒ_ :  P ⊨ Q →  Q ⊨ R →  P ⊨ R
  (P⊨Q »ᵒ Q⊨R) Pa =  Pa ▷ P⊨Q ▷ Q⊨R

--------------------------------------------------------------------------------
-- ∀ᵒ˙, ∃ᵒ˙: Universal/existential quantification

∀ᵒ˙ ∃ᵒ˙ :  (X : Set (sucˡ ℓ)) →  (X → Propᵒ) →  Propᵒ
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

∀ᵒ∈-syntax ∃ᵒ∈-syntax :  (X : Set (sucˡ ℓ)) →  (X → Propᵒ) →  Propᵒ
∀ᵒ∈-syntax =  ∀ᵒ˙
∃ᵒ∈-syntax =  ∃ᵒ˙

∀ᵒ-syntax ∃ᵒ-syntax :  (X → Propᵒ) →  Propᵒ
∀ᵒ-syntax =  ∀ᵒ˙ _
∃ᵒ-syntax =  ∃ᵒ˙ _

infix 3 ∀ᵒ∈-syntax ∃ᵒ∈-syntax ∀ᵒ-syntax ∃ᵒ-syntax
syntax ∀ᵒ∈-syntax X (λ x → P) =  ∀ᵒ x ∈ X , P
syntax ∃ᵒ∈-syntax X (λ x → P) =  ∃ᵒ x ∈ X , P
syntax ∀ᵒ-syntax (λ x → P) =  ∀ᵒ x , P
syntax ∃ᵒ-syntax (λ x → P) =  ∃ᵒ x , P

abstract

  -- Introducing ∀ᵒ / Eliminating ∃ᵒ

  ∀ᵒ-intro :  (∀ x → P ⊨ Q˙ x) →  P ⊨ ∀ᵒ˙ _ Q˙
  ∀ᵒ-intro ∀xP⊨Qx Pa x =  ∀xP⊨Qx x Pa

  ∃ᵒ-elim :  (∀ x → P˙ x ⊨ Q) →  ∃ᵒ˙ _ P˙ ⊨ Q
  ∃ᵒ-elim ∀xPx⊨Q (x , Pxa) =  ∀xPx⊨Q x Pxa

  -- Eliminating ∀ᵒ / Introducing ∃ᵒ

  ∀ᵒ-elim :  ∀ᵒ˙ _ P˙ ⊨ P˙ x
  ∀ᵒ-elim ∀Pa =  ∀Pa _

  ∃ᵒ-intro :  P˙ x ⊨ ∃ᵒ˙ _ P˙
  ∃ᵒ-intro Px =  _ , Px

  -- Choice

  choiceᵒ :  ∀ {P˙˙ : ∀ (x : X) (y : F x) → _} →
    ∀ᵒ x , ∃ᵒ y , P˙˙ x y ⊨ ∃ᵒ f ∈ (∀ x → F x) , ∀ᵒ x , P˙˙ x (f x)
  choiceᵒ ∀x∃yPxy =  (λ x → ∀x∃yPxy x .proj₀) , λ x → ∀x∃yPxy x .proj₁

--------------------------------------------------------------------------------
-- ∧ᵒ: Conjunction
-- ∨ᵒ: Disjunction

infixr 7 _∧ᵒ_
infixr 6 _∨ᵒ_

_∧ᵒ_ _∨ᵒ_ :  Propᵒ →  Propᵒ →  Propᵒ
P ∧ᵒ Q =  ∀ᵒ˙ _ (binary P Q)
P ∨ᵒ Q =  ∃ᵒ˙ _ (binary P Q)

--------------------------------------------------------------------------------
-- ⊤ᵒ: Truth
-- ⊥ᵒ: Falsehood

⊤ᵒ ⊥ᵒ :  Propᵒ
⊤ᵒ =  ∀ᵒ˙ _ absurd
⊥ᵒ =  ∃ᵒ˙ _ absurd

--------------------------------------------------------------------------------
-- ⌜ ⌝ᵒ: Set embedding

⌜_⌝ᵒ :  Set (sucˡ ℓ) →  Propᵒ
⌜ X ⌝ᵒ =  ∃ᵒ˙ X (λ _ → ⊤ᵒ)

--------------------------------------------------------------------------------
-- →ᵒ: Implication

infixr 5 _→ᵒ_
_→ᵒ_ :  Propᵒ → Propᵒ → Propᵒ
(P →ᵒ Q) .predᵒ a _ =  ∀ {b ✓b} →  a ⊑ b →  P .predᵒ b ✓b →  Q .predᵒ b ✓b
(P →ᵒ Q) .monoᵒ {✓a = ✓a} {✓b} =  proof {✓a = ✓a} {✓b}
 where abstract
  proof :  Monoᵒ $ (P →ᵒ Q) .predᵒ
  proof a⊑b P→Qa b⊑c =  P→Qa (⊑-trans a⊑b b⊑c)

abstract

  →ᵒ-intro :  P ∧ᵒ Q ⊨ R →  Q ⊨ P →ᵒ R
  →ᵒ-intro {Q = Q} P∧Q⊨R Qa a⊑b Pb =  P∧Q⊨R $ binary Pb $ Q .monoᵒ a⊑b Qa

  →ᵒ-elim :  Q ⊨ P →ᵒ R →  P ∧ᵒ Q ⊨ R
  →ᵒ-elim Q⊨P→R P∧Qa =  Q⊨P→R (P∧Qa 1₂) ⊑-refl (P∧Qa 0₂)

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

abstract

  -- ∗ᵒ is unital w.r.t. ⊤ᵒ, commutative, associative, and monotone

  ⊤∗ᵒ-elim :  ⊤ᵒ ∗ᵒ P ⊨ P
  ⊤∗ᵒ-elim {P} (b , c , _ , _ , b∙c≈a , _ , Pc) =  P .monoᵒ (b , b∙c≈a) Pc

  ⊤∗ᵒ-intro :  P ⊨ ⊤ᵒ ∗ᵒ P
  ⊤∗ᵒ-intro Pa =  (ε , _ , ✓-ε , _ , ∙-unitˡ , absurd , Pa)

  ∗ᵒ-comm :  P ∗ᵒ Q ⊨ Q ∗ᵒ P
  ∗ᵒ-comm (b , c , _ , _ , b∙c≈a , Pb , Qc) =
    c , b , _ , _ , (∙-comm »˜ b∙c≈a) , Qc , Pb

  ∗ᵒ-assocˡ :  (P ∗ᵒ Q) ∗ᵒ R ⊨ P ∗ᵒ (Q ∗ᵒ R)
  ∗ᵒ-assocˡ {a = a} {✓a}
   (bc , d , _ , _ , bc∙d≈a , (b , c , _ , _ , b∙c≈bc , Pb , Qc) , Rd) =
    b , c ∙ d , _ , ✓-mono (b , b∙cd≈a) ✓a , b∙cd≈a , Pb , c , d , _ , _ ,
    refl˜ , Qc , Rd
   where
    b∙cd≈a :  b ∙ (c ∙ d) ≈ a
    b∙cd≈a =  ∙-assocʳ »˜ ∙-congˡ b∙c≈bc »˜ bc∙d≈a

  ∗ᵒ-monoˡ :  P ⊨ Q →  P ∗ᵒ R ⊨ Q ∗ᵒ R
  ∗ᵒ-monoˡ P⊨Q (b , c , _ , _ , b∙c≈a , Pb , Rc) =
    b , c , _ , _ , b∙c≈a , P⊨Q Pb , Rc

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

abstract

  -- -∗ᵒ is the right adjoint of ∗ᵒ

  -∗ᵒ-intro :  P ∗ᵒ Q ⊨ R →  Q ⊨ P -∗ᵒ R
  -∗ᵒ-intro {Q = Q} P∗Q⊨R Qa {✓c∙b = ✓c∙b} a⊑b Pb =  P∗Q⊨R $
    _ , _ , _ , ✓-mono ∙-incrˡ ✓c∙b , refl˜ , Pb , Q .monoᵒ a⊑b Qa

  -∗ᵒ-elim :  Q ⊨ P -∗ᵒ R →  P ∗ᵒ Q ⊨ R
  -∗ᵒ-elim {R = R} Q⊨P-∗R {✓a = ✓a} (b , c , _ , _ , b∙c≈a , Pb , Qc) =
    R .monoᵒ {✓a = ✓-resp (sym˜ b∙c≈a) ✓a} (≈⇒⊑ b∙c≈a) $ Q⊨P-∗R Qc ⊑-refl Pb

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

abstract

  -- |=>ᵒ is monadic: monotone, increasing, and idempotent

  |=>ᵒ-mono :  P ⊨ Q →  |=>ᵒ P ⊨ |=>ᵒ Q
  |=>ᵒ-mono P⊨Q |=>Pa c ✓c∙a with |=>Pa c ✓c∙a
  ... | b , _ , ✓c∙b , Pb =  b , _ , ✓c∙b , P⊨Q Pb

  |=>ᵒ-intro :  P ⊨ |=>ᵒ P
  |=>ᵒ-intro Pa c ✓c∙a =  _ , _ , ✓c∙a , Pa

  |=>ᵒ-join :  |=>ᵒ |=>ᵒ P ⊨ |=>ᵒ P
  |=>ᵒ-join |=>|=>Pa d ✓d∙a with |=>|=>Pa d ✓d∙a
  ... | b , _ , ✓d∙b , |=>Pb with  |=>Pb d ✓d∙b
  ...   | c , _ , ✓d∙c , Pc = c , _ , ✓d∙c , Pc

  -- ∗ᵒ can get inside |=>ᵒ

  |=>ᵒ-frameˡ :  P ∗ᵒ |=>ᵒ Q ⊨ |=>ᵒ (P ∗ᵒ Q)
  |=>ᵒ-frameˡ (b , c , _ , _ , b∙c≈a , Pb , |=>Qc) e ✓e∙a with
    |=>Qc (e ∙ b) $ flip ✓-resp ✓e∙a $ ∙-congʳ (sym˜ b∙c≈a) »˜ ∙-assocʳ
  ... | d , _ , ✓eb∙d , Qd =  b ∙ d , (flip ✓-mono ✓eb∙d $ ∙-monoˡ ∙-incrˡ) ,
    (✓-resp ∙-assocˡ ✓eb∙d) , b , d , _ , _ , refl˜ , Pb , Qd

  -- ∃ᵒ _ , can get outside |=>ᵒ

  |=>ᵒ-∃-out :  |=>ᵒ (∃ᵒ _ ∈ X , P) ⊨ ∃ᵒ _ ∈ X , |=>ᵒ P
  |=>ᵒ-∃-out {✓a = ✓a} |=>∃AP .proj₀ with |=>∃AP ε (✓-resp (sym˜ ∙-unitˡ) ✓a)
  ... | _ , _ , _ , x , _ =  x
  |=>ᵒ-∃-out {✓a = ✓a} |=>∃AP .proj₁ c ✓c∙a with |=>∃AP c ✓c∙a
  ... | b , _ , ✓c∙b , _ , Pb =  b , _ , ✓c∙b , Pb

--------------------------------------------------------------------------------
-- □ᵒ: Persistence modality

infix 8 □ᵒ_
□ᵒ_ :  Propᵒ → Propᵒ
(□ᵒ P) .predᵒ a ✓a =  P .predᵒ ⌞ a ⌟ (✓-⌞⌟ ✓a)
(□ᵒ P) .monoᵒ {✓a = ✓a} {✓b} =  proof {✓a = ✓a} {✓b}
 where
  proof :  Monoᵒ $ (□ᵒ P) .predᵒ
  proof a⊑b P⌞a⌟ =  P .monoᵒ (⌞⌟-mono a⊑b) P⌞a⌟

abstract

  -- □ᵒ is comonadic: monotone, decreasing, and idempotent

  □ᵒ-mono :  P ⊨ Q →  □ᵒ P ⊨ □ᵒ Q
  □ᵒ-mono P⊨Q P⌞a⌟ =  P⊨Q P⌞a⌟

  □ᵒ-elim :  □ᵒ P ⊨ P
  □ᵒ-elim {P = P} P⌞a⌟ =  P .monoᵒ ⌞⌟-decr P⌞a⌟

  □ᵒ-dup :  □ᵒ P ⊨ □ᵒ □ᵒ P
  □ᵒ-dup {P = P} P⌞a⌟ =  P .monoᵒ (≈⇒⊑ $ sym˜ ⌞⌟-idem) P⌞a⌟

  -- ∧ᵒ can turn into ∗ᵒ when one argument is under □ᵒ

  □ᵒˡ-∧⇒∗ :  □ᵒ P ∧ᵒ Q ⊨ □ᵒ P ∗ᵒ Q
  □ᵒˡ-∧⇒∗ {P = P} {a = a} {✓a} P⌞a⌟∧Qa =  ⌞ a ⌟ , a , ✓-⌞⌟ ✓a , _ , ⌞⌟-unitˡ ,
    P .monoᵒ (≈⇒⊑ $ sym˜ ⌞⌟-idem) (P⌞a⌟∧Qa 0₂) , P⌞a⌟∧Qa 1₂

  -- ∀ᵒ can get inside □ᵒ

  □ᵒ-∀-in :  ∀ᵒ˙ _ (□ᵒ_ ∘ P˙) ⊨ □ᵒ ∀ᵒ˙ _ P˙
  □ᵒ-∀-in ∀xPx⌞a⌟ =  ∀xPx⌞a⌟

  -- ∃ᵒ can get outside □ᵒ

  □ᵒ-∃-out :  □ᵒ ∃ᵒ˙ _ P˙ ⊨ ∃ᵒ˙ _ (□ᵒ_ ∘ P˙)
  □ᵒ-∃-out ΣxPx⌞a⌟ =  ΣxPx⌞a⌟
