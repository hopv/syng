--------------------------------------------------------------------------------
-- General super update
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Base where

open import Base.Level using (Level; _⊔ᴸ_; 1ᴸ; ↓)
open import Base.Func using (_$_; _▷_; _∘_; _›_; id; const)
open import Base.Dec using (upd˙; upd˙-self)
open import Base.Eq using (_≡_; refl; ◠_; _≡˙_)
open import Base.Prod using (∑-syntax; _×_; π₀; _,_; -,_; _,-)
open import Base.Nat using (ℕ)
open import Syho.Lang.Expr using (Mem; ✓ᴹ_)
open import Syho.Model.ERA.Glob using (iᴹᵉᵐ; outᴳ; Envᴵⁿᴳ; Envᴵⁿᴳ˙; envᴳ;
  empᴵⁿᴳ; empᴵⁿᴳ-✓[⊤]; envᴳ-cong; upd˙-out-envᴳ)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; ⊨_; ∀ᵒ-syntax;
  ⊤ᵒ; ⊤ᵒ₀; ⌜_⌝ᵒ; ⌜_⌝ᵒ×_; _∗ᵒ'_; _∗ᵒ_; _-∗ᵒ'_; _-∗ᵒ_; ⤇ᵒ_; _⤇ᴱ'_; _⤇ᴱ_; ⊨⇒⊨✓;
  substᵒ; ∗ᵒ≡∗ᵒ'; ∗ᵒ-mono✓ˡ; ∗ᵒ-monoˡ; ∗ᵒ-monoʳ; ∗ᵒ-comm; ∗ᵒ-assocˡ; ∗ᵒ-assocʳ;
  ∗ᵒ?-intro; ∃ᵒ∗ᵒ-out; -∗ᵒ≡-∗ᵒ'; -∗ᵒ-Mono; -∗ᵒ-monoʳ; -∗ᵒ-introʳ; -∗ᵒ-applyʳ;
  ⤇ᵒ-intro; ⤇ᴱ≡⤇ᴱ'; ⤇ᴱ-Mono; ⤇ᴱ-mono✓; ⤇ᴱ-mono; ⤇ᴱ-respᴱˡ; ⤇ᴱ-respᴱʳ; ⤇ᴱ-param;
  ⊨✓⇒⊨-⤇ᴱ; ⤇ᵒ⇒⤇ᴱ; ⤇ᴱ-intro-✓; ⤇ᵒ-eatʳ; ⤇ᴱ-join; ⤇ᴱ-eatˡ; ⤇ᴱ-eatʳ; ⤇ᴱ-adeq)
open import Syho.Model.Prop.Names using ([⊤]ᴺᵒ)

private variable
  ł ł' ł'' :  Level
  X Y :  Set ł
  Pᵒ Qᵒ :  Propᵒ ł
  j :  ℕ
  M M' M'' :  Mem
  Eᴵⁿ :  Envᴵⁿᴳ
  gsI :  (Envᴵⁿᴳ → X) × (X → Envᴵⁿᴳ → Envᴵⁿᴳ) × (X → Propᵒ ł)
  get get' :  Envᴵⁿᴳ → X
  set set' :  X → Envᴵⁿᴳ → Envᴵⁿᴳ
  Inv Inv' F :  X → Propᵒ ł
  f :  X → Y

--------------------------------------------------------------------------------
-- ⇛ᴳ :  General super-update modality

infix 3 ⟨_⟩[_]⇛ᴳ'⟨_⟩_ ⟨_⟩[_]⇛ᴳ⟨_⟩_ [_]⇛ᵍ_ [_]⇛ᵍ¹_

-- ⇛ᴳ' :  Non-abstract version of ⇛ᴳ

⟨_⟩[_]⇛ᴳ'⟨_⟩_ :  ∀{X : Set ł} →
  Mem →  (Envᴵⁿᴳ → X) × (X → Envᴵⁿᴳ → Envᴵⁿᴳ) × (X → Propᵒ ł') →
  Mem →  Propᵒ ł'' →  Propᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł' ⊔ᴸ ł'')
⟨ M ⟩[ get , set , Inv ]⇛ᴳ'⟨ M' ⟩ Pᵒ =  ∀ᵒ Eᴵⁿ ,
  Inv (get Eᴵⁿ) -∗ᵒ' envᴳ M Eᴵⁿ ⤇ᴱ' λ x → envᴳ M' $ set x Eᴵⁿ , Pᵒ ∗ᵒ' Inv x

abstract

  -- ⇛ᴳ :  General super-update modality

  -- Parametrized over the getter (get) and setter (set) on the environment and
  -- the invariant predicate (Inv)

  ⟨_⟩[_]⇛ᴳ⟨_⟩_ :  ∀{X : Set ł} →
    Mem →  (Envᴵⁿᴳ → X) × (X → Envᴵⁿᴳ → Envᴵⁿᴳ) × (X → Propᵒ ł') →
    Mem →  Propᵒ ł'' →  Propᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł' ⊔ᴸ ł'')
  ⟨ M ⟩[ get , set , Inv ]⇛ᴳ⟨ M' ⟩ Pᵒ =  ∀ᵒ Eᴵⁿ ,
    Inv (get Eᴵⁿ) -∗ᵒ envᴳ M Eᴵⁿ ⤇ᴱ λ x → envᴳ M' $ set x Eᴵⁿ , Pᵒ ∗ᵒ Inv x

-- ⇛ᵍ :  ⇛ᴳ with any fixed memory

[_]⇛ᵍ_ :  ∀{X : Set ł} →
  (Envᴵⁿᴳ → X) × (X → Envᴵⁿᴳ → Envᴵⁿᴳ) × (X → Propᵒ ł') →  Propᵒ ł'' →
  Propᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł' ⊔ᴸ ł'')
[ gsI ]⇛ᵍ Pᵒ =  ∀ᵒ M , ⟨ M ⟩[ gsI ]⇛ᴳ⟨ M ⟩ Pᵒ

-- ⇛ᵍ¹ :  ⇛ᵍ for a component inner ERA

[_]⇛ᵍ¹_ :  ∑ j , (Envᴵⁿᴳ˙ j → Propᵒ ł) →  Propᵒ ł' →  Propᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł')
[ j , Inv ]⇛ᵍ¹ Pᵒ =  [ _$ j , upd˙ j , Inv ]⇛ᵍ Pᵒ

abstract

  -- ⇛ᴳ equals ⇛ᴳ'

  ⇛ᴳ≡⇛ᴳ' :  ∀{X : Set ł}
    {gsI : (Envᴵⁿᴳ → X) × (X → Envᴵⁿᴳ → Envᴵⁿᴳ) × (X → Propᵒ ł')}
    {M M' : Mem} {Pᵒ : Propᵒ ł''}  →
    (⟨ M ⟩[ gsI ]⇛ᴳ⟨ M' ⟩ Pᵒ)  ≡  (⟨ M ⟩[ gsI ]⇛ᴳ'⟨ M' ⟩ Pᵒ)
  ⇛ᴳ≡⇛ᴳ' {ł} {ł'} {ł''} {X}  rewrite -∗ᵒ≡-∗ᵒ' {ł'} {1ᴸ ⊔ᴸ ł ⊔ᴸ ł' ⊔ᴸ ł''} |
    ⤇ᴱ≡⤇ᴱ' {ł} {1ᴸ ⊔ᴸ ł' ⊔ᴸ ł''} {X} | ∗ᵒ≡∗ᵒ' {ł''} {ł'} =  refl

  ⇛ᴳ⇒⇛ᴳ' :  ⟨ M ⟩[ gsI ]⇛ᴳ⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩[ gsI ]⇛ᴳ'⟨ M' ⟩ Pᵒ
  ⇛ᴳ⇒⇛ᴳ' =  substᵒ id ⇛ᴳ≡⇛ᴳ'

  ⇛ᴳ'⇒⇛ᴳ :  ⟨ M ⟩[ gsI ]⇛ᴳ'⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩[ gsI ]⇛ᴳ⟨ M' ⟩ Pᵒ
  ⇛ᴳ'⇒⇛ᴳ =  substᵒ id $ ◠ ⇛ᴳ≡⇛ᴳ'

  -- Monoᵒ for ⇛ᴳ

  ⇛ᴳ-Mono :  Monoᵒ $ ⟨ M ⟩[ gsI ]⇛ᴳ⟨ M' ⟩ Pᵒ
  ⇛ᴳ-Mono a⊑b big _ =  -∗ᵒ-Mono a⊑b $ big _

  ⇛ᵍ-Mono :  Monoᵒ $ [ gsI ]⇛ᵍ Pᵒ
  ⇛ᵍ-Mono a⊑b big _ =  ⇛ᴳ-Mono a⊑b $ big _

  -- Monotonicity of ⇛ᴳ

  ⇛ᴳ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  ⟨ M ⟩[ gsI ]⇛ᴳ⟨ M' ⟩ Pᵒ ⊨ ⟨ M ⟩[ gsI ]⇛ᴳ⟨ M' ⟩ Qᵒ
  ⇛ᴳ-mono✓ P⊨✓Q gsI⇛P Eᴵⁿ =
    (-∗ᵒ-monoʳ $ ⤇ᴱ-mono✓ λ _ → ∗ᵒ-mono✓ˡ P⊨✓Q) $ gsI⇛P Eᴵⁿ

  ⇛ᴳ-mono :  Pᵒ ⊨ Qᵒ →  ⟨ M ⟩[ gsI ]⇛ᴳ⟨ M' ⟩ Pᵒ ⊨ ⟨ M ⟩[ gsI ]⇛ᴳ⟨ M' ⟩ Qᵒ
  ⇛ᴳ-mono =  ⊨⇒⊨✓ › ⇛ᴳ-mono✓

  -- Monotonicity of ⇛ᵍ

  ⇛ᵍ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  [ gsI ]⇛ᵍ Pᵒ ⊨ [ gsI ]⇛ᵍ Qᵒ
  ⇛ᵍ-mono✓ P⊨✓Q big _ =  big _ ▷ ⇛ᴳ-mono✓ P⊨✓Q

  ⇛ᵍ-mono :  Pᵒ ⊨ Qᵒ →  [ gsI ]⇛ᵍ Pᵒ ⊨ [ gsI ]⇛ᵍ Qᵒ
  ⇛ᵍ-mono =  ⊨⇒⊨✓ › ⇛ᵍ-mono✓

  -- Utility for making ⇛ᴳ and ⇛ᵍ¹

  ⇛ᴳ-make :  (∀{Eᴵⁿ} →  Pᵒ  ∗ᵒ  Inv (get Eᴵⁿ)  ⊨
               envᴳ M Eᴵⁿ ⤇ᴱ λ x → envᴳ M' $ set x Eᴵⁿ ,  Qᵒ  ∗ᵒ  Inv x)  →
             Pᵒ ⊨ ⟨ M ⟩[ get , set , Inv ]⇛ᴳ⟨ M' ⟩ Qᵒ
  ⇛ᴳ-make {Pᵒ = Pᵒ} P∗Inv⊨⤇Q∗Inv Pa _ =  Pa ▷ -∗ᵒ-introʳ λ _ → P∗Inv⊨⤇Q∗Inv

  ⇛ᵍ¹-make :  (∀{E} →  Pᵒ  ∗ᵒ  Inv (E $ outᴳ j)  ⊨
                E ⤇ᴱ λ Fʲ → upd˙ (outᴳ j) Fʲ E ,  Qᵒ  ∗ᵒ  Inv Fʲ)  →
              Pᵒ  ⊨ [ j , Inv ]⇛ᵍ¹  Qᵒ
  ⇛ᵍ¹-make big Pa _ =  ⇛ᴳ-make (big › ⤇ᴱ-respᴱʳ upd˙-out-envᴳ) Pa

  -- Apply ⇛ᴳ

  ⇛ᴳ-apply :  (⟨ M ⟩[ get , set , Inv ]⇛ᴳ⟨ M' ⟩ Pᵒ)  ∗ᵒ  Inv (get Eᴵⁿ)  ⊨
                 envᴳ M Eᴵⁿ ⤇ᴱ λ x → envᴳ M' $ set x Eᴵⁿ ,  Pᵒ  ∗ᵒ  Inv x
  ⇛ᴳ-apply =  ⊨✓⇒⊨-⤇ᴱ λ ✓∙ → ∗ᵒ-monoˡ (_$ _) › -∗ᵒ-applyʳ ⤇ᴱ-Mono ✓∙

  -- ⊨✓ ⇛ᴳ/⇛ᵍ into ⊨ ⇛ᴳ/⇛ᵍ

  ⊨✓⇒⊨-⇛ᴳ :  Pᵒ ⊨✓ ⟨ M ⟩[ gsI ]⇛ᴳ⟨ M' ⟩ Qᵒ →  Pᵒ ⊨ ⟨ M ⟩[ gsI ]⇛ᴳ⟨ M' ⟩ Qᵒ
  ⊨✓⇒⊨-⇛ᴳ {Pᵒ = Pᵒ} P⊨✓⇛Q =  ⇛ᴳ-make {Pᵒ = Pᵒ} $ ⊨✓⇒⊨-⤇ᴱ λ ✓∙ →
    ∗ᵒ-mono✓ˡ P⊨✓⇛Q ✓∙ › ⇛ᴳ-apply

  ⊨✓⇒⊨-⇛ᵍ :  Pᵒ ⊨✓ [ gsI ]⇛ᵍ Qᵒ →  Pᵒ ⊨ [ gsI ]⇛ᵍ Qᵒ
  ⊨✓⇒⊨-⇛ᵍ P⊨✓⇛Q Pa _ =  ⊨✓⇒⊨-⇛ᴳ (λ ✓∙ Pb → P⊨✓⇛Q ✓∙ Pb _) Pa

  -- Let ⇛ᴳ/⇛ᵍ use Envᴵⁿᴳ as the parameter

  ⇛ᴳ-all :  (∀{Eᴵⁿ x} → get (set x Eᴵⁿ) ≡ x)  →
            ⟨ M ⟩[ get , set , Inv ]⇛ᴳ⟨ M' ⟩ Pᵒ  ⊨
              ⟨ M ⟩[ id , const , Inv ∘ get ]⇛ᴳ⟨ M' ⟩ Pᵒ
  ⇛ᴳ-all {Inv = Inv} getset≡ =  ⇛ᴳ-make {Pᵒ = ⟨ _ ⟩[ _ ]⇛ᴳ⟨ _ ⟩ _} $
    ⇛ᴳ-apply › ⤇ᴱ-mono (λ _ → ∗ᵒ-monoʳ $ substᵒ Inv $ ◠ getset≡) › ⤇ᴱ-param

  ⇛ᵍ-all :  (∀{Eᴵⁿ x} → get (set x Eᴵⁿ) ≡ x)  →
              [ get , set , Inv ]⇛ᵍ Pᵒ  ⊨  [ id , const , Inv ∘ get ]⇛ᵍ Pᵒ
  ⇛ᵍ-all getset≡ big _ =  big _ ▷ ⇛ᴳ-all getset≡

  -- Introduce ⇛ᴳ/⇛ᵍ/⇛ᵍ¹

  ⤇ᵒ⇒⇛ᴳ :  (∀{Eᴵⁿ} → set (get Eᴵⁿ) Eᴵⁿ ≡˙ Eᴵⁿ) →
           ⤇ᵒ Pᵒ ⊨ ⟨ M ⟩[ get , set , Inv ]⇛ᴳ⟨ M ⟩ Pᵒ
  ⤇ᵒ⇒⇛ᴳ setget≡ =  ⇛ᴳ-make $ ⤇ᵒ-eatʳ › ⤇ᵒ⇒⤇ᴱ ›
    ⤇ᴱ-respᴱˡ (envᴳ-cong setget≡) › ⤇ᴱ-param

  ⇛ᴳ-intro :  (∀{Eᴵⁿ} → set (get Eᴵⁿ) Eᴵⁿ ≡˙ Eᴵⁿ) →
              Pᵒ ⊨ ⟨ M ⟩[ get , set , Inv ]⇛ᴳ⟨ M ⟩ Pᵒ
  ⇛ᴳ-intro setget≡ =  ⤇ᵒ-intro › ⤇ᵒ⇒⇛ᴳ setget≡

  ⤇ᵒ⇒⇛ᵍ :  (∀{Eᴵⁿ} → set (get Eᴵⁿ) Eᴵⁿ ≡˙ Eᴵⁿ) →
           ⤇ᵒ Pᵒ ⊨ [ get , set , Inv ]⇛ᵍ Pᵒ
  ⤇ᵒ⇒⇛ᵍ setget≡ ⤇Pa _ =  ⤇Pa ▷ ⤇ᵒ⇒⇛ᴳ setget≡

  ⇛ᵍ-intro :  (∀{Eᴵⁿ} → set (get Eᴵⁿ) Eᴵⁿ ≡˙ Eᴵⁿ) →
              Pᵒ ⊨ [ get , set , Inv ]⇛ᵍ Pᵒ
  ⇛ᵍ-intro setget≡ =  ⤇ᵒ-intro › ⤇ᵒ⇒⇛ᵍ setget≡

  ⤇ᵒ⇒⇛ᵍ¹ :  ⤇ᵒ Pᵒ ⊨ [ j , Inv ]⇛ᵍ¹ Pᵒ
  ⤇ᵒ⇒⇛ᵍ¹ =  ⤇ᵒ⇒⇛ᵍ upd˙-self

  ⇛ᵍ¹-intro :  Pᵒ ⊨ [ j , Inv ]⇛ᵍ¹ Pᵒ
  ⇛ᵍ¹-intro =  ⤇ᵒ-intro › ⤇ᵒ⇒⇛ᵍ¹

  -- Introduce ⇛ᴳ with ✓ᴹ

  ⇛ᴳ-intro-✓ᴹ :  (∀{Eᴵⁿ} → set (get Eᴵⁿ) Eᴵⁿ ≡˙ Eᴵⁿ) →
                 Pᵒ ⊨ ⟨ M ⟩[ get , set , Inv ]⇛ᴳ⟨ M ⟩ ⌜ ✓ᴹ M ⌝ᵒ× Pᵒ
  ⇛ᴳ-intro-✓ᴹ setget≡ =  ⇛ᴳ-make $ ⤇ᴱ-intro-✓ › ⤇ᴱ-respᴱˡ (envᴳ-cong setget≡) ›
    ⤇ᴱ-mono (λ (-, E✓) → ∗ᵒ-monoˡ (E✓ iᴹᵉᵐ .↓ .π₀ ,_)) › ⤇ᴱ-param

  -- Join the same ⇛ᴳs / ⇛ᵍs

  ⇛ᴳ-join :  (∀{Eᴵⁿ x} → get (set x Eᴵⁿ) ≡ x) →
    (∀{Eᴵⁿ x y} → set y (set x Eᴵⁿ) ≡˙ set y Eᴵⁿ) →
    ⟨ M ⟩[ get , set , Inv ]⇛ᴳ⟨ M' ⟩ ⟨ M' ⟩[ get , set , Inv ]⇛ᴳ⟨ M'' ⟩ Pᵒ  ⊨
      ⟨ M ⟩[ get , set , Inv ]⇛ᴳ⟨ M'' ⟩ Pᵒ
  ⇛ᴳ-join {Inv = Inv} getset≡ setset≡set =  ⇛ᴳ-make {Pᵒ = ⟨ _ ⟩[ _ ]⇛ᴳ⟨ _ ⟩ _} $
    ⇛ᴳ-apply › ⤇ᴱ-mono (λ _ → ∗ᵒ-monoʳ (substᵒ Inv (◠ getset≡)) › ⇛ᴳ-apply) ›
    ⤇ᴱ-join › ⤇ᴱ-respᴱʳ (envᴳ-cong setset≡set) › ⤇ᴱ-param

  ⇛ᵍ-join :  (∀{Eᴵⁿ x} → get (set x Eᴵⁿ) ≡ x) →
             (∀{Eᴵⁿ x y} → set y (set x Eᴵⁿ) ≡˙ set y Eᴵⁿ) →
             [ get , set , Inv ]⇛ᵍ [ get , set , Inv ]⇛ᵍ Pᵒ  ⊨
               [ get , set , Inv ]⇛ᵍ Pᵒ
  ⇛ᵍ-join getset≡ setset≡set big _ =
    big _ ▷ ⇛ᴳ-mono (_$ _) ▷ ⇛ᴳ-join getset≡ setset≡set

  -- Join two different ⇛ᴳs / ⇛ᵍs

  ⇛ᴳ-join2 :  (∀{Eᴵⁿ x} → get' (set x Eᴵⁿ) ≡ get' Eᴵⁿ) →
    ⟨ M ⟩[ get , set , Inv ]⇛ᴳ⟨ M' ⟩ ⟨ M' ⟩[ get' , set' , Inv' ]⇛ᴳ⟨ M'' ⟩ Pᵒ  ⊨
      ⟨ M ⟩[ (λ Eᴵⁿ → (get Eᴵⁿ , get' Eᴵⁿ)) , (λ (x , y) → set x › set' y) ,
             (λ (x , y) → Inv x ∗ᵒ Inv' y) ]⇛ᴳ⟨ M'' ⟩ Pᵒ
  ⇛ᴳ-join2 {Inv' = Inv'} get'set≡get' =  ⇛ᴳ-make {Pᵒ = ⟨ _ ⟩[ _ ]⇛ᴳ⟨ _ ⟩ _} $
      ∗ᵒ-assocʳ › ∗ᵒ-monoˡ ⇛ᴳ-apply › ⤇ᴱ-eatʳ › ⤇ᴱ-mono (λ _ → ∗ᵒ-assocˡ ›
      ∗ᵒ-monoʳ ∗ᵒ-comm › ∗ᵒ-assocʳ ›
      ∗ᵒ-monoˡ (∗ᵒ-monoʳ (substᵒ Inv' (◠ get'set≡get')) › ⇛ᴳ-apply) ›
      ⤇ᴱ-eatʳ › ⤇ᴱ-mono λ _ → ∗ᵒ-assocˡ › ∗ᵒ-monoʳ ∗ᵒ-comm) › ⤇ᴱ-join

  ⇛ᵍ-join2 :  (∀{Eᴵⁿ x} → get' (set x Eᴵⁿ) ≡ get' Eᴵⁿ) →
    [ get , set , Inv ]⇛ᵍ [ get' , set' , Inv' ]⇛ᵍ Pᵒ  ⊨
      [ (λ Eᴵⁿ → (get Eᴵⁿ , get' Eᴵⁿ)) , (λ (x , y) → set x › set' y) ,
        (λ (x , y) → Inv x ∗ᵒ Inv' y) ]⇛ᵍ Pᵒ
  ⇛ᵍ-join2 get'set≡get' big _ =  big _ ▷ ⇛ᴳ-mono (_$ _) ▷ ⇛ᴳ-join2 get'set≡get'

  -- Let ⇛ᴳ/⇛ᵍ eat a proposition under ∗ᵒ

  ⇛ᴳ-eatˡ :  Qᵒ ∗ᵒ (⟨ M ⟩[ gsI ]⇛ᴳ⟨ M' ⟩ Pᵒ)  ⊨ ⟨ M ⟩[ gsI ]⇛ᴳ⟨ M' ⟩  Qᵒ ∗ᵒ Pᵒ
  ⇛ᴳ-eatˡ =  ⇛ᴳ-make {Pᵒ = _ ∗ᵒ _} $ ∗ᵒ-assocˡ › ∗ᵒ-monoʳ ⇛ᴳ-apply › ⤇ᴱ-eatˡ ›
    ⤇ᴱ-mono λ _ → ∗ᵒ-assocʳ

  ⇛ᴳ-eatʳ :  (⟨ M ⟩[ gsI ]⇛ᴳ⟨ M' ⟩ Pᵒ) ∗ᵒ Qᵒ  ⊨ ⟨ M ⟩[ gsI ]⇛ᴳ⟨ M' ⟩  Pᵒ ∗ᵒ Qᵒ
  ⇛ᴳ-eatʳ =  ∗ᵒ-comm › ⇛ᴳ-eatˡ › ⇛ᴳ-mono ∗ᵒ-comm

  ⇛ᵍ-eatˡ :  Qᵒ ∗ᵒ ([ gsI ]⇛ᵍ Pᵒ)  ⊨ [ gsI ]⇛ᵍ  Qᵒ ∗ᵒ Pᵒ
  ⇛ᵍ-eatˡ big _ =  big ▷ ∗ᵒ-monoʳ (_$ _) ▷ ⇛ᴳ-eatˡ

  ⇛ᵍ-eatʳ :  ([ gsI ]⇛ᵍ Pᵒ) ∗ᵒ Qᵒ  ⊨ [ gsI ]⇛ᵍ  Pᵒ ∗ᵒ Qᵒ
  ⇛ᵍ-eatʳ big _ =  big ▷ ∗ᵒ-monoˡ (_$ _) ▷ ⇛ᴳ-eatʳ

  -- Adequacy of ⇛ᴳ
  -- If we have Y under [⊤]ᴺᵒ and ⟨ M ⟩[ get , _ , Inv ]⇛ᴳ⟨ _ ⟩ for valid M and
  -- Inv (get empᴵⁿᴳ) is a tautology, then Y holds purely

  ⇛ᴳ-adeq :  ⊨ Inv (get empᴵⁿᴳ) →  ✓ᴹ M →
             [⊤]ᴺᵒ ⊨ ⟨ M ⟩[ get , set , Inv ]⇛ᴳ⟨ M' ⟩ ⌜ Y ⌝ᵒ →  Y
  ⇛ᴳ-adeq ⊨Invgetemp ✓M [⊤]⊨M⇛M'Y =  ⤇ᴱ-adeq (empᴵⁿᴳ-✓[⊤] ✓M) $
    [⊤]⊨M⇛M'Y › ∗ᵒ?-intro ⊨Invgetemp › ⇛ᴳ-apply ›
    ⤇ᴱ-mono λ _ → ∗ᵒ-monoˡ {Qᵒ = ⌜ _ ⌝ᵒ× ⊤ᵒ₀} (_,-) › ∃ᵒ∗ᵒ-out › π₀
