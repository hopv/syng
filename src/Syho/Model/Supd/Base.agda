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
  ∗ᵒ?-intro; ∃ᵒ∗ᵒ-out; -∗ᵒ≡-∗ᵒ'; -∗ᵒ-Mono; -∗ᵒ-monoʳ; -∗ᵒ-intro; -∗ᵒ-applyʳ;
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
-- ⇛ᵍ :  General super-update modality

infix 3 ⟨_⟩[_]⇛ᵍ'⟨_⟩_ ⟨_⟩[_]⇛ᵍ⟨_⟩_ [_]⇛ᵍᶠ_ [_]⇛ᵍ¹_

-- ⇛ᵍ' :  Non-abstract version of ⇛ᵍ

⟨_⟩[_]⇛ᵍ'⟨_⟩_ :  ∀{X : Set ł} →
  Mem →  (Envᴵⁿᴳ → X) × (X → Envᴵⁿᴳ → Envᴵⁿᴳ) × (X → Propᵒ ł') →
  Mem →  Propᵒ ł'' →  Propᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł' ⊔ᴸ ł'')
⟨ M ⟩[ get , set , Inv ]⇛ᵍ'⟨ M' ⟩ Pᵒ =  ∀ᵒ Eᴵⁿ ,
  Inv (get Eᴵⁿ) -∗ᵒ' envᴳ M Eᴵⁿ ⤇ᴱ' λ x → envᴳ M' $ set x Eᴵⁿ , Pᵒ ∗ᵒ' Inv x

abstract

  -- ⇛ᵍ :  General super-update modality

  -- Parametrized over the getter (get) and setter (set) on the environment and
  -- the invariant predicate (Inv)

  ⟨_⟩[_]⇛ᵍ⟨_⟩_ :  ∀{X : Set ł} →
    Mem →  (Envᴵⁿᴳ → X) × (X → Envᴵⁿᴳ → Envᴵⁿᴳ) × (X → Propᵒ ł') →
    Mem →  Propᵒ ł'' →  Propᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł' ⊔ᴸ ł'')
  ⟨ M ⟩[ get , set , Inv ]⇛ᵍ⟨ M' ⟩ Pᵒ =  ∀ᵒ Eᴵⁿ ,
    Inv (get Eᴵⁿ) -∗ᵒ envᴳ M Eᴵⁿ ⤇ᴱ λ x → envᴳ M' $ set x Eᴵⁿ , Pᵒ ∗ᵒ Inv x

-- ⇛ᵍᶠ :  ⇛ᵍ with any fixed memory

[_]⇛ᵍᶠ_ :  ∀{X : Set ł} →
  (Envᴵⁿᴳ → X) × (X → Envᴵⁿᴳ → Envᴵⁿᴳ) × (X → Propᵒ ł') →  Propᵒ ł'' →
  Propᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł' ⊔ᴸ ł'')
[ gsI ]⇛ᵍᶠ Pᵒ =  ∀ᵒ M , ⟨ M ⟩[ gsI ]⇛ᵍ⟨ M ⟩ Pᵒ

-- ⇛ᵍ¹ :  ⇛ᵍᶠ for a component inner ERA

[_]⇛ᵍ¹_ :  ∑ j , (Envᴵⁿᴳ˙ j → Propᵒ ł) →  Propᵒ ł' →  Propᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł')
[ j , Inv ]⇛ᵍ¹ Pᵒ =  [ _$ j , upd˙ j , Inv ]⇛ᵍᶠ Pᵒ

abstract

  -- ⇛ᵍ equals ⇛ᵍ'

  ⇛ᵍ≡⇛ᵍ' :  ∀{X : Set ł}
    {gsI : (Envᴵⁿᴳ → X) × (X → Envᴵⁿᴳ → Envᴵⁿᴳ) × (X → Propᵒ ł')}
    {M M' : Mem} {Pᵒ : Propᵒ ł''}  →
    (⟨ M ⟩[ gsI ]⇛ᵍ⟨ M' ⟩ Pᵒ)  ≡  (⟨ M ⟩[ gsI ]⇛ᵍ'⟨ M' ⟩ Pᵒ)
  ⇛ᵍ≡⇛ᵍ' {ł} {ł'} {ł''} {X}  rewrite -∗ᵒ≡-∗ᵒ' {ł'} {1ᴸ ⊔ᴸ ł ⊔ᴸ ł' ⊔ᴸ ł''} |
    ⤇ᴱ≡⤇ᴱ' {ł} {1ᴸ ⊔ᴸ ł' ⊔ᴸ ł''} {X} | ∗ᵒ≡∗ᵒ' {ł''} {ł'} =  refl

  ⇛ᵍ⇒⇛ᵍ' :  ⟨ M ⟩[ gsI ]⇛ᵍ⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩[ gsI ]⇛ᵍ'⟨ M' ⟩ Pᵒ
  ⇛ᵍ⇒⇛ᵍ' =  substᵒ id ⇛ᵍ≡⇛ᵍ'

  ⇛ᵍ'⇒⇛ᵍ :  ⟨ M ⟩[ gsI ]⇛ᵍ'⟨ M' ⟩ Pᵒ  ⊨  ⟨ M ⟩[ gsI ]⇛ᵍ⟨ M' ⟩ Pᵒ
  ⇛ᵍ'⇒⇛ᵍ =  substᵒ id $ ◠ ⇛ᵍ≡⇛ᵍ'

  -- Monoᵒ for ⇛ᵍ

  ⇛ᵍ-Mono :  Monoᵒ $ ⟨ M ⟩[ gsI ]⇛ᵍ⟨ M' ⟩ Pᵒ
  ⇛ᵍ-Mono a⊑b big _ =  -∗ᵒ-Mono a⊑b $ big _

  ⇛ᵍᶠ-Mono :  Monoᵒ $ [ gsI ]⇛ᵍᶠ Pᵒ
  ⇛ᵍᶠ-Mono a⊑b big _ =  ⇛ᵍ-Mono a⊑b $ big _

  -- Monotonicity of ⇛ᵍ

  ⇛ᵍ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  ⟨ M ⟩[ gsI ]⇛ᵍ⟨ M' ⟩ Pᵒ ⊨ ⟨ M ⟩[ gsI ]⇛ᵍ⟨ M' ⟩ Qᵒ
  ⇛ᵍ-mono✓ P⊨✓Q gsI⇛P Eᴵⁿ =
    (-∗ᵒ-monoʳ $ ⤇ᴱ-mono✓ λ _ → ∗ᵒ-mono✓ˡ P⊨✓Q) $ gsI⇛P Eᴵⁿ

  ⇛ᵍ-mono :  Pᵒ ⊨ Qᵒ →  ⟨ M ⟩[ gsI ]⇛ᵍ⟨ M' ⟩ Pᵒ ⊨ ⟨ M ⟩[ gsI ]⇛ᵍ⟨ M' ⟩ Qᵒ
  ⇛ᵍ-mono =  ⊨⇒⊨✓ › ⇛ᵍ-mono✓

  -- Monotonicity of ⇛ᵍᶠ

  ⇛ᵍᶠ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  [ gsI ]⇛ᵍᶠ Pᵒ ⊨ [ gsI ]⇛ᵍᶠ Qᵒ
  ⇛ᵍᶠ-mono✓ P⊨✓Q big _ =  big _ ▷ ⇛ᵍ-mono✓ P⊨✓Q

  ⇛ᵍᶠ-mono :  Pᵒ ⊨ Qᵒ →  [ gsI ]⇛ᵍᶠ Pᵒ ⊨ [ gsI ]⇛ᵍᶠ Qᵒ
  ⇛ᵍᶠ-mono =  ⊨⇒⊨✓ › ⇛ᵍᶠ-mono✓

  -- Utility for making ⇛ᵍ and ⇛ᵍ¹

  ⇛ᵍ-make :  (∀{Eᴵⁿ} →  Pᵒ  ∗ᵒ  Inv (get Eᴵⁿ)  ⊨
               envᴳ M Eᴵⁿ ⤇ᴱ λ x → envᴳ M' $ set x Eᴵⁿ ,  Qᵒ  ∗ᵒ  Inv x)  →
             Pᵒ ⊨ ⟨ M ⟩[ get , set , Inv ]⇛ᵍ⟨ M' ⟩ Qᵒ
  ⇛ᵍ-make {Pᵒ = Pᵒ} P∗Inv⊨⤇Q∗Inv Pa _ =  Pa ▷
    -∗ᵒ-intro λ _ → ∗ᵒ-comm › P∗Inv⊨⤇Q∗Inv

  ⇛ᵍ¹-make :  (∀{E} →  Pᵒ  ∗ᵒ  Inv (E $ outᴳ j)  ⊨
                E ⤇ᴱ λ Fʲ → upd˙ (outᴳ j) Fʲ E ,  Qᵒ  ∗ᵒ  Inv Fʲ)  →
              Pᵒ  ⊨ [ j , Inv ]⇛ᵍ¹  Qᵒ
  ⇛ᵍ¹-make big Pa _ =  ⇛ᵍ-make (big › ⤇ᴱ-respᴱʳ upd˙-out-envᴳ) Pa

  -- Apply ⇛ᵍ

  ⇛ᵍ-apply :  (⟨ M ⟩[ get , set , Inv ]⇛ᵍ⟨ M' ⟩ Pᵒ)  ∗ᵒ  Inv (get Eᴵⁿ)  ⊨
                envᴳ M Eᴵⁿ ⤇ᴱ λ x → envᴳ M' $ set x Eᴵⁿ ,  Pᵒ  ∗ᵒ  Inv x
  ⇛ᵍ-apply =  ⊨✓⇒⊨-⤇ᴱ λ ✓∙ → ∗ᵒ-monoˡ (_$ _) › -∗ᵒ-applyʳ ⤇ᴱ-Mono ✓∙

  -- ⊨✓ ⇛ᵍ/⇛ᵍᶠ into ⊨ ⇛ᵍ/⇛ᵍᶠ

  ⊨✓⇒⊨-⇛ᵍ :  Pᵒ ⊨✓ ⟨ M ⟩[ gsI ]⇛ᵍ⟨ M' ⟩ Qᵒ →  Pᵒ ⊨ ⟨ M ⟩[ gsI ]⇛ᵍ⟨ M' ⟩ Qᵒ
  ⊨✓⇒⊨-⇛ᵍ {Pᵒ = Pᵒ} P⊨✓⇛Q =  ⇛ᵍ-make {Pᵒ = Pᵒ} $ ⊨✓⇒⊨-⤇ᴱ λ ✓∙ →
    ∗ᵒ-mono✓ˡ P⊨✓⇛Q ✓∙ › ⇛ᵍ-apply

  ⊨✓⇒⊨-⇛ᵍᶠ :  Pᵒ ⊨✓ [ gsI ]⇛ᵍᶠ Qᵒ →  Pᵒ ⊨ [ gsI ]⇛ᵍᶠ Qᵒ
  ⊨✓⇒⊨-⇛ᵍᶠ P⊨✓⇛Q Pa _ =  ⊨✓⇒⊨-⇛ᵍ (λ ✓∙ Pb → P⊨✓⇛Q ✓∙ Pb _) Pa

  -- Let ⇛ᵍ/⇛ᵍᶠ use Envᴵⁿᴳ as the parameter

  ⇛ᵍ-all :  (∀{Eᴵⁿ x} → get (set x Eᴵⁿ) ≡ x)  →
            ⟨ M ⟩[ get , set , Inv ]⇛ᵍ⟨ M' ⟩ Pᵒ  ⊨
              ⟨ M ⟩[ id , const , Inv ∘ get ]⇛ᵍ⟨ M' ⟩ Pᵒ
  ⇛ᵍ-all {Inv = Inv} getset≡ =  ⇛ᵍ-make {Pᵒ = ⟨ _ ⟩[ _ ]⇛ᵍ⟨ _ ⟩ _} $ ⇛ᵍ-apply ›
    ⤇ᴱ-mono (λ _ → ∗ᵒ-monoʳ $ substᵒ Inv $ ◠ getset≡) › ⤇ᴱ-param

  ⇛ᵍᶠ-all :  (∀{Eᴵⁿ x} → get (set x Eᴵⁿ) ≡ x)  →
             [ get , set , Inv ]⇛ᵍᶠ Pᵒ  ⊨  [ id , const , Inv ∘ get ]⇛ᵍᶠ Pᵒ
  ⇛ᵍᶠ-all getset≡ big _ =  big _ ▷ ⇛ᵍ-all getset≡

  -- Introduce ⇛ᵍ/⇛ᵍᶠ/⇛ᵍ¹

  ⤇ᵒ⇒⇛ᵍ :  (∀{Eᴵⁿ} → set (get Eᴵⁿ) Eᴵⁿ ≡˙ Eᴵⁿ) →
           ⤇ᵒ Pᵒ ⊨ ⟨ M ⟩[ get , set , Inv ]⇛ᵍ⟨ M ⟩ Pᵒ
  ⤇ᵒ⇒⇛ᵍ setget≡ =  ⇛ᵍ-make $ ⤇ᵒ-eatʳ › ⤇ᵒ⇒⤇ᴱ ›
    ⤇ᴱ-respᴱˡ (envᴳ-cong setget≡) › ⤇ᴱ-param

  ⇛ᵍ-intro :  (∀{Eᴵⁿ} → set (get Eᴵⁿ) Eᴵⁿ ≡˙ Eᴵⁿ) →
              Pᵒ ⊨ ⟨ M ⟩[ get , set , Inv ]⇛ᵍ⟨ M ⟩ Pᵒ
  ⇛ᵍ-intro setget≡ =  ⤇ᵒ-intro › ⤇ᵒ⇒⇛ᵍ setget≡

  ⤇ᵒ⇒⇛ᵍᶠ :  (∀{Eᴵⁿ} → set (get Eᴵⁿ) Eᴵⁿ ≡˙ Eᴵⁿ) →
            ⤇ᵒ Pᵒ ⊨ [ get , set , Inv ]⇛ᵍᶠ Pᵒ
  ⤇ᵒ⇒⇛ᵍᶠ setget≡ ⤇Pa _ =  ⤇Pa ▷ ⤇ᵒ⇒⇛ᵍ setget≡

  ⇛ᵍᶠ-intro :  (∀{Eᴵⁿ} → set (get Eᴵⁿ) Eᴵⁿ ≡˙ Eᴵⁿ) →
               Pᵒ ⊨ [ get , set , Inv ]⇛ᵍᶠ Pᵒ
  ⇛ᵍᶠ-intro setget≡ =  ⤇ᵒ-intro › ⤇ᵒ⇒⇛ᵍᶠ setget≡

  ⤇ᵒ⇒⇛ᵍ¹ :  ⤇ᵒ Pᵒ ⊨ [ j , Inv ]⇛ᵍ¹ Pᵒ
  ⤇ᵒ⇒⇛ᵍ¹ =  ⤇ᵒ⇒⇛ᵍᶠ upd˙-self

  ⇛ᵍ¹-intro :  Pᵒ ⊨ [ j , Inv ]⇛ᵍ¹ Pᵒ
  ⇛ᵍ¹-intro =  ⤇ᵒ-intro › ⤇ᵒ⇒⇛ᵍ¹

  -- Introduce ⇛ᵍ with ✓ᴹ

  ⇛ᵍ-intro-✓ᴹ :  (∀{Eᴵⁿ} → set (get Eᴵⁿ) Eᴵⁿ ≡˙ Eᴵⁿ) →
                 Pᵒ ⊨ ⟨ M ⟩[ get , set , Inv ]⇛ᵍ⟨ M ⟩ ⌜ ✓ᴹ M ⌝ᵒ× Pᵒ
  ⇛ᵍ-intro-✓ᴹ setget≡ =  ⇛ᵍ-make $ ⤇ᴱ-intro-✓ › ⤇ᴱ-respᴱˡ (envᴳ-cong setget≡) ›
    ⤇ᴱ-mono (λ (-, E✓) → ∗ᵒ-monoˡ (E✓ iᴹᵉᵐ .↓ .π₀ ,_)) › ⤇ᴱ-param

  -- Join the same ⇛ᵍs / ⇛ᵍᶠs

  ⇛ᵍ-join :
    (∀{Eᴵⁿ x} → get (set x Eᴵⁿ) ≡ x) →
    (∀{Eᴵⁿ x y} → set y (set x Eᴵⁿ) ≡˙ set y Eᴵⁿ) →
    ⟨ M ⟩[ get , set , Inv ]⇛ᵍ⟨ M' ⟩ ⟨ M' ⟩[ get , set , Inv ]⇛ᵍ⟨ M'' ⟩ Pᵒ  ⊨
      ⟨ M ⟩[ get , set , Inv ]⇛ᵍ⟨ M'' ⟩ Pᵒ
  ⇛ᵍ-join {Inv = Inv} getset≡ setset≡set = ⇛ᵍ-make {Pᵒ = ⟨ _ ⟩[ _ ]⇛ᵍ⟨ _ ⟩ _} $
    ⇛ᵍ-apply › ⤇ᴱ-mono (λ _ → ∗ᵒ-monoʳ (substᵒ Inv (◠ getset≡)) › ⇛ᵍ-apply)
    › ⤇ᴱ-join › ⤇ᴱ-respᴱʳ (envᴳ-cong setset≡set) › ⤇ᴱ-param

  ⇛ᵍᶠ-join :  (∀{Eᴵⁿ x} → get (set x Eᴵⁿ) ≡ x) →
              (∀{Eᴵⁿ x y} → set y (set x Eᴵⁿ) ≡˙ set y Eᴵⁿ) →
              [ get , set , Inv ]⇛ᵍᶠ [ get , set , Inv ]⇛ᵍᶠ Pᵒ  ⊨
                [ get , set , Inv ]⇛ᵍᶠ Pᵒ
  ⇛ᵍᶠ-join getset≡ setset≡set big _ =
    big _ ▷ ⇛ᵍ-mono (_$ _) ▷ ⇛ᵍ-join getset≡ setset≡set

  -- Join two different ⇛ᵍs / ⇛ᵍᶠs

  ⇛ᵍ-join2 :  (∀{Eᴵⁿ x} → get' (set x Eᴵⁿ) ≡ get' Eᴵⁿ) →
    ⟨ M ⟩[ get , set , Inv ]⇛ᵍ⟨ M' ⟩ ⟨ M' ⟩[ get' , set' , Inv' ]⇛ᵍ⟨ M'' ⟩ Pᵒ  ⊨
      ⟨ M ⟩[ (λ Eᴵⁿ → (get Eᴵⁿ , get' Eᴵⁿ)) , (λ (x , y) → set x › set' y) ,
             (λ (x , y) → Inv x ∗ᵒ Inv' y) ]⇛ᵍ⟨ M'' ⟩ Pᵒ
  ⇛ᵍ-join2 {Inv' = Inv'} get'set≡get' =  ⇛ᵍ-make {Pᵒ = ⟨ _ ⟩[ _ ]⇛ᵍ⟨ _ ⟩ _} $
      ∗ᵒ-assocʳ › ∗ᵒ-monoˡ ⇛ᵍ-apply › ⤇ᴱ-eatʳ › ⤇ᴱ-mono (λ _ → ∗ᵒ-assocˡ ›
      ∗ᵒ-monoʳ ∗ᵒ-comm › ∗ᵒ-assocʳ ›
      ∗ᵒ-monoˡ (∗ᵒ-monoʳ (substᵒ Inv' (◠ get'set≡get')) › ⇛ᵍ-apply) ›
      ⤇ᴱ-eatʳ › ⤇ᴱ-mono λ _ → ∗ᵒ-assocˡ › ∗ᵒ-monoʳ ∗ᵒ-comm) › ⤇ᴱ-join

  ⇛ᵍᶠ-join2 :  (∀{Eᴵⁿ x} → get' (set x Eᴵⁿ) ≡ get' Eᴵⁿ) →
    [ get , set , Inv ]⇛ᵍᶠ [ get' , set' , Inv' ]⇛ᵍᶠ Pᵒ  ⊨
      [ (λ Eᴵⁿ → (get Eᴵⁿ , get' Eᴵⁿ)) , (λ (x , y) → set x › set' y) ,
        (λ (x , y) → Inv x ∗ᵒ Inv' y) ]⇛ᵍᶠ Pᵒ
  ⇛ᵍᶠ-join2 get'set≡get' big _ =  big _ ▷ ⇛ᵍ-mono (_$ _) ▷ ⇛ᵍ-join2 get'set≡get'

  -- Let ⇛ᵍ/⇛ᵍᶠ eat a proposition under ∗ᵒ

  ⇛ᵍ-eatˡ :  Qᵒ ∗ᵒ (⟨ M ⟩[ gsI ]⇛ᵍ⟨ M' ⟩ Pᵒ)  ⊨ ⟨ M ⟩[ gsI ]⇛ᵍ⟨ M' ⟩  Qᵒ ∗ᵒ Pᵒ
  ⇛ᵍ-eatˡ =  ⇛ᵍ-make {Pᵒ = _ ∗ᵒ _} $ ∗ᵒ-assocˡ › ∗ᵒ-monoʳ ⇛ᵍ-apply › ⤇ᴱ-eatˡ ›
    ⤇ᴱ-mono λ _ → ∗ᵒ-assocʳ

  ⇛ᵍ-eatʳ :  (⟨ M ⟩[ gsI ]⇛ᵍ⟨ M' ⟩ Pᵒ) ∗ᵒ Qᵒ  ⊨ ⟨ M ⟩[ gsI ]⇛ᵍ⟨ M' ⟩  Pᵒ ∗ᵒ Qᵒ
  ⇛ᵍ-eatʳ =  ∗ᵒ-comm › ⇛ᵍ-eatˡ › ⇛ᵍ-mono ∗ᵒ-comm

  ⇛ᵍᶠ-eatˡ :  Qᵒ ∗ᵒ ([ gsI ]⇛ᵍᶠ Pᵒ)  ⊨ [ gsI ]⇛ᵍᶠ  Qᵒ ∗ᵒ Pᵒ
  ⇛ᵍᶠ-eatˡ big _ =  big ▷ ∗ᵒ-monoʳ (_$ _) ▷ ⇛ᵍ-eatˡ

  ⇛ᵍᶠ-eatʳ :  ([ gsI ]⇛ᵍᶠ Pᵒ) ∗ᵒ Qᵒ  ⊨ [ gsI ]⇛ᵍᶠ  Pᵒ ∗ᵒ Qᵒ
  ⇛ᵍᶠ-eatʳ big _ =  big ▷ ∗ᵒ-monoˡ (_$ _) ▷ ⇛ᵍ-eatʳ

  -- Adequacy of ⇛ᵍ
  -- If we have Y under [⊤]ᴺᵒ and ⟨ M ⟩[ get , _ , Inv ]⇛ᵍ⟨ _ ⟩ for valid M and
  -- Inv (get empᴵⁿᴳ) is a tautology, then Y holds purely

  ⇛ᵍ-adeq :  ⊨ Inv (get empᴵⁿᴳ) →  ✓ᴹ M →
             [⊤]ᴺᵒ ⊨ ⟨ M ⟩[ get , set , Inv ]⇛ᵍ⟨ M' ⟩ ⌜ Y ⌝ᵒ →  Y
  ⇛ᵍ-adeq ⊨Invgetemp ✓M [⊤]⊨M⇛M'Y =  ⤇ᴱ-adeq (empᴵⁿᴳ-✓[⊤] ✓M) $
    [⊤]⊨M⇛M'Y › ∗ᵒ?-intro ⊨Invgetemp › ⇛ᵍ-apply ›
    ⤇ᴱ-mono λ _ → ∗ᵒ-monoˡ {Qᵒ = ⌜ _ ⌝ᵒ× ⊤ᵒ₀} (_,-) › ∃ᵒ∗ᵒ-out › π₀
