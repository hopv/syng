--------------------------------------------------------------------------------
-- Semantic proposition
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level; sucˡ)
open import Shog.Model.RA using (RA)
-- Parametric over the global RA
module Shog.Model.PropS {ℓ : Level} (Globᴿᴬ : RA (sucˡ ℓ) (sucˡ ℓ) (sucˡ ℓ))
  where

open import Base.Few using (binary; 0₂; 1₂; absurd)
open import Base.Func using (_$_; _▷_; flip)
open import Base.Prod using (Σ-syntax; _×_; _,_; proj₀; proj₁)

open RA Globᴿᴬ renaming (Car to Glob) using (_≈_; _⊑_; ✓_; _∙_; ε; refl˜; sym˜;
  _»˜_; ⊑-refl; ⊑-trans; ⊑-respʳ; ≈⇒⊑; ✓-resp; ✓-mono; ✓-ε; ∙-congˡ; ∙-congʳ;
  ∙-monoʳ; ∙-incrˡ; ∙-comm; ∙-assocˡ; ∙-assocʳ; ∙-unitˡ)

--------------------------------------------------------------------------------
-- Propˢ: Semantic proposition

Monoˢ :  ∀ (predˢ : ∀ (a : Glob) →  ✓ a →  Set (sucˡ ℓ)) →  Set (sucˡ ℓ)
Monoˢ predˢ =  ∀ {a b ✓a ✓b} →  a ⊑ b →  predˢ a ✓a →  predˢ b ✓b

record  Propˢ :  Set (sucˡ (sucˡ ℓ))  where
  constructor propˢ
  field
    predˢ :  ∀ (a : Glob) →  ✓ a →  Set (sucˡ ℓ)
    monoˢ :  Monoˢ predˢ
open Propˢ

private variable
  A :  Set (sucˡ ℓ)
  P Q R :  Propˢ
  P˙ Q˙ :  A → Propˢ
  x :  A
  F :  A →  Set (sucˡ ℓ)

--------------------------------------------------------------------------------
-- ⊨: Entailment

infix 1 _⊨_
_⊨_ :  Propˢ →  Propˢ →  Set (sucˡ ℓ)
P ⊨ Q =  ∀ {a ✓a} →  P .predˢ a ✓a →  Q .predˢ a ✓a

abstract

  -- ⊨ is reflexive and transitive

  reflˢ :  P ⊨ P
  reflˢ Pa =  Pa

  infixr -1 _»ˢ_
  _»ˢ_ :  P ⊨ Q →  Q ⊨ R →  P ⊨ R
  (P⊨Q »ˢ Q⊨R) Pa =  Pa ▷ P⊨Q ▷ Q⊨R

--------------------------------------------------------------------------------
-- ∀ˢ˙, ∃ˢ˙: Universal/existential quantification

∀ˢ˙ ∃ˢ˙ :  (A : Set (sucˡ ℓ)) →  (A → Propˢ) →  Propˢ
∀ˢ˙ _ P˙ .predˢ a ✓a =  ∀ x →  P˙ x .predˢ a ✓a
∀ˢ˙ _ P˙ .monoˢ =  proof
 where abstract
  proof :  Monoˢ $ ∀ˢ˙ _ P˙ .predˢ
  proof a⊑b ∀xPxa x =  P˙ x .monoˢ a⊑b (∀xPxa x)
∃ˢ˙ _ P˙ .predˢ a ✓a =  Σ x ,  P˙ x .predˢ a ✓a
∃ˢ˙ _ P˙ .monoˢ =  proof
 where abstract
  proof :  Monoˢ $ ∃ˢ˙ _ P˙ .predˢ
  proof a⊑b (x , Pxa) =  x ,  P˙ x .monoˢ a⊑b Pxa

∀ˢ∈-syntax ∃ˢ∈-syntax :  (A : Set (sucˡ ℓ)) →  (A → Propˢ) →  Propˢ
∀ˢ∈-syntax =  ∀ˢ˙
∃ˢ∈-syntax =  ∃ˢ˙

∀ˢ-syntax ∃ˢ-syntax :  (A → Propˢ) →  Propˢ
∀ˢ-syntax =  ∀ˢ˙ _
∃ˢ-syntax =  ∃ˢ˙ _

infix 3 ∀ˢ∈-syntax ∃ˢ∈-syntax ∀ˢ-syntax ∃ˢ-syntax
syntax ∀ˢ∈-syntax A (λ x → P) =  ∀ˢ x ∈ A , P
syntax ∃ˢ∈-syntax A (λ x → P) =  ∃ˢ x ∈ A , P
syntax ∀ˢ-syntax (λ x → P) =  ∀ˢ x , P
syntax ∃ˢ-syntax (λ x → P) =  ∃ˢ x , P

abstract

  -- Introducing ∀ˢ / Eliminating ∃ˢ

  ∀ˢ-intro :  (∀ x → P ⊨ Q˙ x) →  P ⊨ ∀ˢ˙ _ Q˙
  ∀ˢ-intro ∀xP⊨Qx Pa x =  ∀xP⊨Qx x Pa

  ∃ˢ-elim :  (∀ x → P˙ x ⊨ Q) →  ∃ˢ˙ _ P˙ ⊨ Q
  ∃ˢ-elim ∀xPx⊨Q (x , Pxa) =  ∀xPx⊨Q x Pxa

  -- Eliminating ∀ˢ / Introducing ∃ˢ

  ∀ˢ-elim :  ∀ˢ˙ _ P˙ ⊨ P˙ x
  ∀ˢ-elim ∀Pa =  ∀Pa _

  ∃ˢ-intro :  P˙ x ⊨ ∃ˢ˙ _ P˙
  ∃ˢ-intro Px =  _ , Px

  -- Choice

  choiceˢ :  ∀ {P˙˙ : ∀ (x : A) (y : F x) → _} →
    ∀ˢ x , ∃ˢ y , P˙˙ x y ⊨ ∃ˢ f ∈ (∀ x → F x) , ∀ˢ x , P˙˙ x (f x)
  choiceˢ ∀x∃yPxy =  (λ x → ∀x∃yPxy x .proj₀) , λ x →  ∀x∃yPxy x .proj₁

--------------------------------------------------------------------------------
-- ∧ˢ: Conjunction
-- ∨ˢ: Disjunction

infixr 7 _∧ˢ_
infixr 6 _∨ˢ_

_∧ˢ_ _∨ˢ_ :  Propˢ →  Propˢ →  Propˢ
P ∧ˢ Q =  ∀ˢ˙ _ (binary P Q)
P ∨ˢ Q =  ∃ˢ˙ _ (binary P Q)

--------------------------------------------------------------------------------
-- ⊤ˢ: Truth
-- ⊥ˢ: Falsehood

⊤ˢ ⊥ˢ :  Propˢ
⊤ˢ =  ∀ˢ˙ _ absurd
⊥ˢ =  ∃ˢ˙ _ absurd

--------------------------------------------------------------------------------
-- →ˢ: Implication

infixr 5 _→ˢ_
_→ˢ_ :  Propˢ → Propˢ → Propˢ
(P →ˢ Q) .predˢ a _ =  ∀ {b ✓b} →  a ⊑ b →  P .predˢ b ✓b →  Q .predˢ b ✓b
(P →ˢ Q) .monoˢ {✓a = ✓a} {✓b} =  proof {✓a = ✓a} {✓b}
 where abstract
  proof :  Monoˢ $ (P →ˢ Q) .predˢ
  proof a⊑b P→Qa b⊑c =  P→Qa (⊑-trans a⊑b b⊑c)

abstract

  →ˢ-intro :  P ∧ˢ Q ⊨ R →  Q ⊨ P →ˢ R
  →ˢ-intro {Q = Q} P∧Q⊨R Qa a⊑b Pb =  P∧Q⊨R $ binary Pb $ Q .monoˢ a⊑b Qa

  →ˢ-elim :  Q ⊨ P →ˢ R →  P ∧ˢ Q ⊨ R
  →ˢ-elim Q⊨P→R P∧Qa =  Q⊨P→R (P∧Qa 1₂) ⊑-refl (P∧Qa 0₂)

--------------------------------------------------------------------------------
-- ∗ˢ: Separating conjunction

infixr 7 _∗ˢ_
_∗ˢ_ :  Propˢ → Propˢ → Propˢ
(P ∗ˢ Q) .predˢ a _ =  Σ b , Σ c , Σ ✓b , Σ ✓c ,
  b ∙ c ≈ a  ×  P .predˢ b ✓b  ×  Q .predˢ c ✓c
(P ∗ˢ Q) .monoˢ {✓a = ✓a} {✓b} =  proof {✓a = ✓a} {✓b}
 where abstract
  proof :  Monoˢ $ (P ∗ˢ Q) .predˢ
  proof {✓b = ✓b} a⊑b@(c , c∙a≈b) (d , e , _ , _ , d∙e≈a , Pd , Qe) =
    c ∙ d , e ,
    (flip ✓-mono ✓b $ ⊑-respʳ c∙a≈b $ ∙-monoʳ $ e , (∙-comm »˜ d∙e≈a)) ,
    _ , (∙-assocˡ »˜ ∙-congʳ d∙e≈a »˜ c∙a≈b) ,
    P .monoˢ ∙-incrˡ Pd , Qe

abstract

  -- ∗ˢ is unital w.r.t. ⊤ˢ, commutative, associative, and monotone

  ⊤∗ˢ-elim :  ⊤ˢ ∗ˢ P ⊨ P
  ⊤∗ˢ-elim {P} (b , c , _ , _ , b∙c≈a , _ , Pc) =  P .monoˢ (b , b∙c≈a) Pc

  ⊤∗ˢ-intro :  P ⊨ ⊤ˢ ∗ˢ P
  ⊤∗ˢ-intro Pa =  (ε , _ , ✓-ε , _ , ∙-unitˡ , absurd , Pa)

  ∗ˢ-comm :  P ∗ˢ Q ⊨ Q ∗ˢ P
  ∗ˢ-comm (b , c , _ , _ , b∙c≈a , Pb , Qc) =
    c , b , _ , _ , (∙-comm »˜ b∙c≈a) , Qc , Pb

  ∗ˢ-assocˡ :  (P ∗ˢ Q) ∗ˢ R ⊨ P ∗ˢ (Q ∗ˢ R)
  ∗ˢ-assocˡ {a = a} {✓a}
   (bc , d , _ , _ , bc∙d≈a , (b , c , _ , _ , b∙c≈bc , Pb , Qc) , Rd) =
    b , c ∙ d , _ , ✓-mono (b , b∙cd≈a) ✓a , b∙cd≈a , Pb , c , d , _ , _ ,
    refl˜ , Qc , Rd
   where
    b∙cd≈a :  b ∙ (c ∙ d) ≈ a
    b∙cd≈a =  ∙-assocʳ »˜ ∙-congˡ b∙c≈bc »˜ bc∙d≈a

  ∗ˢ-monoˡ :  P ⊨ Q →  P ∗ˢ R ⊨ Q ∗ˢ R
  ∗ˢ-monoˡ P⊨Q (b , c , _ , _ , b∙c≈a , Pb , Rc) =
    b , c , _ , _ , b∙c≈a , P⊨Q Pb , Rc

--------------------------------------------------------------------------------
-- -∗ˢ: Magic wand

infixr 5 _-∗ˢ_
_-∗ˢ_ :  Propˢ → Propˢ → Propˢ
(P -∗ˢ Q) .predˢ a _ =  ∀ {b c ✓c ✓c∙b} →  a ⊑ b →
  P .predˢ c ✓c → Q .predˢ (c ∙ b) ✓c∙b
(P -∗ˢ Q) .monoˢ {✓a = ✓a} {✓b} =  proof {✓a = ✓a} {✓b}
 where abstract
  proof :  Monoˢ $ (P -∗ˢ Q) .predˢ
  proof a⊑b P-∗Qa b⊑c Pc =  P-∗Qa (⊑-trans a⊑b b⊑c) Pc

abstract

  -- -∗ˢ is the right adjoint of ∗ˢ

  -∗ˢ-intro :  P ∗ˢ Q ⊨ R →  Q ⊨ P -∗ˢ R
  -∗ˢ-intro {Q = Q} P∗Q⊨R Qa {✓c∙b = ✓c∙b} a⊑b Pb =  P∗Q⊨R $
    _ , _ , _ , ✓-mono ∙-incrˡ ✓c∙b , refl˜ , Pb , Q .monoˢ a⊑b Qa

  -∗ˢ-elim :  Q ⊨ P -∗ˢ R →  P ∗ˢ Q ⊨ R
  -∗ˢ-elim {R = R} Q⊨P-∗R {✓a = ✓a} (b , c , _ , _ , b∙c≈a , Pb , Qc) =
    R .monoˢ {✓a = ✓-resp (sym˜ b∙c≈a) ✓a} (≈⇒⊑ b∙c≈a) $ Q⊨P-∗R Qc ⊑-refl Pb
