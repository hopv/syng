--------------------------------------------------------------------------------
-- General fancy update
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syng.Model.Fupd.Base where

open import Base.Level using (Level; _⊔ᴸ_; 1ᴸ; ↓)
open import Base.Func using (_$_; _▷_; _∘_; _›_; id; const)
open import Base.Dec using (upd˙; upd˙-self)
open import Base.Eq using (_≡_; refl; ◠_; _≡˙_; _◇˙_)
open import Base.Prod using (∑-syntax; _×_; π₀; _,_; -,_; _,-)
open import Base.Nat using (ℕ)
open import Syng.Lang.Expr using (Heap; ✓ᴴ_)
open import Syng.Model.ERA.Glob using (iᴴᵉᵃᵖ; outᴳ; Envᴵⁿᴳ; Envᴵⁿᴳ˙; envᴳ;
  ∅ᴵⁿᴳ; ∅ᴵⁿᴳ-✓ᴺ; envᴳ-cong; upd˙-out-envᴳ)
open import Syng.Model.Prop.Base using (SPropᵒ; Monoᵒ; _⊨✓_; _⊨_; ⊨_; ∀ᵒ-syntax;
  ⊤ᵒ; ⊤ᵒ₀; ⌜_⌝ᵒ; ⌜_⌝ᵒ×_; _∗ᵒ'_; _∗ᵒ_; _-∗ᵒ'_; _-∗ᵒ_; ⤇ᵒ_; _⤇ᴱ'_; _⤇ᴱ_; ⤇ᴱ⟨⟩;
  ⊨⇒⊨✓; substᵒ; ∗ᵒ≡∗ᵒ'; ∗ᵒ-mono✓ˡ; ∗ᵒ-monoˡ; ∗ᵒ-monoʳ; ∗ᵒ-comm; ∗ᵒ-assocˡ;
  ∗ᵒ-assocʳ; ∗ᵒ?-intro; ∃ᵒ∗ᵒ-out; -∗ᵒ≡-∗ᵒ'; -∗ᵒ-Mono; -∗ᵒ-monoʳ; -∗ᵒ-introʳ;
  -∗ᵒ-applyʳ; ⤇ᵒ-intro; ⤇ᴱ≡⤇ᴱ'; ⤇ᴱ-Mono; ⤇ᴱ-mono✓; ⤇ᴱ-mono; ⤇ᴱ-respᴱˡ;
  ⤇ᴱ-respᴱʳ; ⤇ᴱ-param; ⊨✓⇒⊨-⤇ᴱ; ⤇ᵒ⇒⤇ᴱ; ⤇ᴱ-intro-✓; ⤇ᵒ-eatʳ; ⤇ᴱ-join; ⤇ᴱ-eatˡ;
  ⤇ᴱ-eatʳ; ⤇ᴱ-adeq)
open import Syng.Model.Prop.Names using ([⊤]ᴺᵒ)

private variable
  ł ł' ł'' :  Level
  X Y :  Set ł
  Pᵒ Qᵒ :  SPropᵒ ł
  j :  ℕ
  H H' H'' :  Heap
  Eᴵⁿ :  Envᴵⁿᴳ
  gsI :  (Envᴵⁿᴳ → X) × (X → Envᴵⁿᴳ → Envᴵⁿᴳ) × (X → SPropᵒ ł)
  get get' :  Envᴵⁿᴳ → X
  set set' :  X → Envᴵⁿᴳ → Envᴵⁿᴳ
  Inv Inv' F :  X → SPropᵒ ł
  f :  X → Y

--------------------------------------------------------------------------------
-- ⇛ᴳ :  General fancy update modality

infix 3 ⟨_⟩[_]⇛ᴳ'⟨_⟩_ ⟨_⟩[_]⇛ᴳ⟨_⟩_ [_]⇛ᵍ_ [_]⇛ᵍ¹_

-- ⇛ᴳ' :  Non-abstract version of ⇛ᴳ

⟨_⟩[_]⇛ᴳ'⟨_⟩_ :  ∀{X : Set ł} →
  Heap →  (Envᴵⁿᴳ → X) × (X → Envᴵⁿᴳ → Envᴵⁿᴳ) × (X → SPropᵒ ł') →
  Heap →  SPropᵒ ł'' →  SPropᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł' ⊔ᴸ ł'')
⟨ H ⟩[ get , set , Inv ]⇛ᴳ'⟨ H' ⟩ Pᵒ =  ∀ᵒ Eᴵⁿ ,
  Inv (get Eᴵⁿ) -∗ᵒ' envᴳ H Eᴵⁿ ⤇ᴱ' λ x → envᴳ H' $ set x Eᴵⁿ , Pᵒ ∗ᵒ' Inv x

abstract

  -- ⇛ᴳ :  General fancy update modality

  -- Parametrized over the getter (get) and setter (set) on the environment and
  -- the invariant predicate (Inv)

  ⟨_⟩[_]⇛ᴳ⟨_⟩_ :  ∀{X : Set ł} →
    Heap →  (Envᴵⁿᴳ → X) × (X → Envᴵⁿᴳ → Envᴵⁿᴳ) × (X → SPropᵒ ł') →
    Heap →  SPropᵒ ł'' →  SPropᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł' ⊔ᴸ ł'')
  ⟨ H ⟩[ get , set , Inv ]⇛ᴳ⟨ H' ⟩ Pᵒ =  ∀ᵒ Eᴵⁿ ,
    Inv (get Eᴵⁿ) -∗ᵒ envᴳ H Eᴵⁿ ⤇ᴱ λ x → envᴳ H' $ set x Eᴵⁿ , Pᵒ ∗ᵒ Inv x

-- ⇛ᵍ :  ⇛ᴳ with any fixed heap

[_]⇛ᵍ_ :  ∀{X : Set ł} →
  (Envᴵⁿᴳ → X) × (X → Envᴵⁿᴳ → Envᴵⁿᴳ) × (X → SPropᵒ ł') →  SPropᵒ ł'' →
  SPropᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł' ⊔ᴸ ł'')
[ gsI ]⇛ᵍ Pᵒ =  ∀ᵒ H , ⟨ H ⟩[ gsI ]⇛ᴳ⟨ H ⟩ Pᵒ

-- ⇛ᵍ¹ :  ⇛ᵍ for a component inner ERA

[_]⇛ᵍ¹_ :  ∑ j , (Envᴵⁿᴳ˙ j → SPropᵒ ł) →  SPropᵒ ł' →  SPropᵒ (1ᴸ ⊔ᴸ ł ⊔ᴸ ł')
[ j , Inv ]⇛ᵍ¹ Pᵒ =  [ _$ j , upd˙ j , Inv ]⇛ᵍ Pᵒ

abstract

  -- ⇛ᴳ equals ⇛ᴳ'

  ⇛ᴳ≡⇛ᴳ' :  ∀{X : Set ł}
    {gsI : (Envᴵⁿᴳ → X) × (X → Envᴵⁿᴳ → Envᴵⁿᴳ) × (X → SPropᵒ ł')}
    {H H' : Heap} {Pᵒ : SPropᵒ ł''}  →
    (⟨ H ⟩[ gsI ]⇛ᴳ⟨ H' ⟩ Pᵒ)  ≡  (⟨ H ⟩[ gsI ]⇛ᴳ'⟨ H' ⟩ Pᵒ)
  ⇛ᴳ≡⇛ᴳ' {ł} {ł'} {ł''} {X}  rewrite -∗ᵒ≡-∗ᵒ' {ł'} {1ᴸ ⊔ᴸ ł ⊔ᴸ ł' ⊔ᴸ ł''} |
    ⤇ᴱ≡⤇ᴱ' {ł} {1ᴸ ⊔ᴸ ł' ⊔ᴸ ł''} {X} | ∗ᵒ≡∗ᵒ' {ł''} {ł'} =  refl

  ⇛ᴳ⇒⇛ᴳ' :  ⟨ H ⟩[ gsI ]⇛ᴳ⟨ H' ⟩ Pᵒ  ⊨  ⟨ H ⟩[ gsI ]⇛ᴳ'⟨ H' ⟩ Pᵒ
  ⇛ᴳ⇒⇛ᴳ' =  substᵒ id ⇛ᴳ≡⇛ᴳ'

  ⇛ᴳ'⇒⇛ᴳ :  ⟨ H ⟩[ gsI ]⇛ᴳ'⟨ H' ⟩ Pᵒ  ⊨  ⟨ H ⟩[ gsI ]⇛ᴳ⟨ H' ⟩ Pᵒ
  ⇛ᴳ'⇒⇛ᴳ =  substᵒ id $ ◠ ⇛ᴳ≡⇛ᴳ'

  -- Monoᵒ for ⇛ᴳ

  ⇛ᴳ-Mono :  Monoᵒ $ ⟨ H ⟩[ gsI ]⇛ᴳ⟨ H' ⟩ Pᵒ
  ⇛ᴳ-Mono a⊑b big _ =  -∗ᵒ-Mono a⊑b $ big _

  ⇛ᵍ-Mono :  Monoᵒ $ [ gsI ]⇛ᵍ Pᵒ
  ⇛ᵍ-Mono a⊑b big _ =  ⇛ᴳ-Mono a⊑b $ big _

  -- Monotonicity of ⇛ᴳ

  ⇛ᴳ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  ⟨ H ⟩[ gsI ]⇛ᴳ⟨ H' ⟩ Pᵒ ⊨ ⟨ H ⟩[ gsI ]⇛ᴳ⟨ H' ⟩ Qᵒ
  ⇛ᴳ-mono✓ P⊨✓Q =  -∗ᵒ-monoʳ (⤇ᴱ-mono✓ λ _ → ∗ᵒ-mono✓ˡ P⊨✓Q) ∘_

  ⇛ᴳ-mono :  Pᵒ ⊨ Qᵒ →  ⟨ H ⟩[ gsI ]⇛ᴳ⟨ H' ⟩ Pᵒ ⊨ ⟨ H ⟩[ gsI ]⇛ᴳ⟨ H' ⟩ Qᵒ
  ⇛ᴳ-mono =  ⊨⇒⊨✓ › ⇛ᴳ-mono✓

  -- Monotonicity of ⇛ᵍ

  ⇛ᵍ-mono✓ :  Pᵒ ⊨✓ Qᵒ →  [ gsI ]⇛ᵍ Pᵒ ⊨ [ gsI ]⇛ᵍ Qᵒ
  ⇛ᵍ-mono✓ P⊨✓Q big _ =  big _ ▷ ⇛ᴳ-mono✓ P⊨✓Q

  ⇛ᵍ-mono :  Pᵒ ⊨ Qᵒ →  [ gsI ]⇛ᵍ Pᵒ ⊨ [ gsI ]⇛ᵍ Qᵒ
  ⇛ᵍ-mono =  ⊨⇒⊨✓ › ⇛ᵍ-mono✓

  -- Utility for making ⇛ᴳ and ⇛ᵍ¹

  ⇛ᴳ-make :  (∀{Eᴵⁿ} →  Pᵒ  ∗ᵒ  Inv (get Eᴵⁿ)  ⊨
               envᴳ H Eᴵⁿ ⤇ᴱ λ x → envᴳ H' $ set x Eᴵⁿ ,  Qᵒ  ∗ᵒ  Inv x)  →
             Pᵒ ⊨ ⟨ H ⟩[ get , set , Inv ]⇛ᴳ⟨ H' ⟩ Qᵒ
  ⇛ᴳ-make {Pᵒ = Pᵒ} P∗Inv⊨⤇Q∗Inv Pa _ =  Pa ▷ -∗ᵒ-introʳ λ _ → P∗Inv⊨⤇Q∗Inv

  ⇛ᵍ¹-make :  (∀{Eʲ} →  Pᵒ  ∗ᵒ  Inv Eʲ  ⊨ Eʲ ⤇ᴱ⟨ outᴳ j ⟩ λ Fʲ → Fʲ ,
                          Qᵒ  ∗ᵒ  Inv Fʲ)  →
              Pᵒ  ⊨ [ j , Inv ]⇛ᵍ¹  Qᵒ
  ⇛ᵍ¹-make P∗Inv⊨⤇Q∗Inv Pa _ =  Pa ▷ ⇛ᴳ-make λ P∗Inva → P∗Inv⊨⤇Q∗Inv P∗Inva _ ▷
    ⤇ᴱ-respᴱˡ (upd˙-out-envᴳ ◇˙ envᴳ-cong upd˙-self) ▷ ⤇ᴱ-respᴱʳ upd˙-out-envᴳ

  -- Apply ⇛ᴳ

  ⇛ᴳ-apply :  (⟨ H ⟩[ get , set , Inv ]⇛ᴳ⟨ H' ⟩ Pᵒ)  ∗ᵒ  Inv (get Eᴵⁿ)  ⊨
                envᴳ H Eᴵⁿ ⤇ᴱ λ x → envᴳ H' $ set x Eᴵⁿ ,  Pᵒ  ∗ᵒ  Inv x
  ⇛ᴳ-apply =  ⊨✓⇒⊨-⤇ᴱ λ ✓∙ → ∗ᵒ-monoˡ (_$ _) › -∗ᵒ-applyʳ ⤇ᴱ-Mono ✓∙

  -- ⊨✓ ⇛ᴳ/⇛ᵍ into ⊨ ⇛ᴳ/⇛ᵍ

  ⊨✓⇒⊨-⇛ᴳ :  Pᵒ ⊨✓ ⟨ H ⟩[ gsI ]⇛ᴳ⟨ H' ⟩ Qᵒ →  Pᵒ ⊨ ⟨ H ⟩[ gsI ]⇛ᴳ⟨ H' ⟩ Qᵒ
  ⊨✓⇒⊨-⇛ᴳ {Pᵒ = Pᵒ} P⊨✓⇛Q =  ⇛ᴳ-make {Pᵒ = Pᵒ} $ ⊨✓⇒⊨-⤇ᴱ λ ✓∙ →
    ∗ᵒ-mono✓ˡ P⊨✓⇛Q ✓∙ › ⇛ᴳ-apply

  ⊨✓⇒⊨-⇛ᵍ :  Pᵒ ⊨✓ [ gsI ]⇛ᵍ Qᵒ →  Pᵒ ⊨ [ gsI ]⇛ᵍ Qᵒ
  ⊨✓⇒⊨-⇛ᵍ P⊨✓⇛Q Pa _ =  ⊨✓⇒⊨-⇛ᴳ (λ ✓∙ Pb → P⊨✓⇛Q ✓∙ Pb _) Pa

  -- Let ⇛ᴳ/⇛ᵍ use Envᴵⁿᴳ as the parameter

  ⇛ᴳ-all :  (∀{Eᴵⁿ x} → get (set x Eᴵⁿ) ≡ x)  →
            ⟨ H ⟩[ get , set , Inv ]⇛ᴳ⟨ H' ⟩ Pᵒ  ⊨
              ⟨ H ⟩[ id , const , Inv ∘ get ]⇛ᴳ⟨ H' ⟩ Pᵒ
  ⇛ᴳ-all {Inv = Inv} gs≡ =  ⇛ᴳ-make {Pᵒ = ⟨ _ ⟩[ _ ]⇛ᴳ⟨ _ ⟩ _} $
    ⇛ᴳ-apply › ⤇ᴱ-mono (λ _ → ∗ᵒ-monoʳ $ substᵒ Inv $ ◠ gs≡) › ⤇ᴱ-param

  ⇛ᵍ-all :  (∀{Eᴵⁿ x} → get (set x Eᴵⁿ) ≡ x)  →
              [ get , set , Inv ]⇛ᵍ Pᵒ  ⊨  [ id , const , Inv ∘ get ]⇛ᵍ Pᵒ
  ⇛ᵍ-all gs≡ big _ =  big _ ▷ ⇛ᴳ-all gs≡

  -- Introduce ⇛ᴳ/⇛ᵍ/⇛ᵍ¹

  ⤇ᵒ⇒⇛ᴳ :  (∀{Eᴵⁿ} → set (get Eᴵⁿ) Eᴵⁿ ≡˙ Eᴵⁿ) →
           ⤇ᵒ Pᵒ ⊨ ⟨ H ⟩[ get , set , Inv ]⇛ᴳ⟨ H ⟩ Pᵒ
  ⤇ᵒ⇒⇛ᴳ sg≡ =  ⇛ᴳ-make $ ⤇ᵒ-eatʳ › ⤇ᵒ⇒⤇ᴱ › ⤇ᴱ-respᴱˡ (envᴳ-cong sg≡) › ⤇ᴱ-param

  ⇛ᴳ-intro :  (∀{Eᴵⁿ} → set (get Eᴵⁿ) Eᴵⁿ ≡˙ Eᴵⁿ) →
              Pᵒ ⊨ ⟨ H ⟩[ get , set , Inv ]⇛ᴳ⟨ H ⟩ Pᵒ
  ⇛ᴳ-intro sg≡ =  ⤇ᵒ-intro › ⤇ᵒ⇒⇛ᴳ sg≡

  ⤇ᵒ⇒⇛ᵍ :  (∀{Eᴵⁿ} → set (get Eᴵⁿ) Eᴵⁿ ≡˙ Eᴵⁿ) →
           ⤇ᵒ Pᵒ ⊨ [ get , set , Inv ]⇛ᵍ Pᵒ
  ⤇ᵒ⇒⇛ᵍ sg≡ ⤇Pa _ =  ⤇Pa ▷ ⤇ᵒ⇒⇛ᴳ sg≡

  ⇛ᵍ-intro :  (∀{Eᴵⁿ} → set (get Eᴵⁿ) Eᴵⁿ ≡˙ Eᴵⁿ) →
              Pᵒ ⊨ [ get , set , Inv ]⇛ᵍ Pᵒ
  ⇛ᵍ-intro sg≡ =  ⤇ᵒ-intro › ⤇ᵒ⇒⇛ᵍ sg≡

  ⤇ᵒ⇒⇛ᵍ¹ :  ⤇ᵒ Pᵒ ⊨ [ j , Inv ]⇛ᵍ¹ Pᵒ
  ⤇ᵒ⇒⇛ᵍ¹ =  ⤇ᵒ⇒⇛ᵍ upd˙-self

  ⇛ᵍ¹-intro :  Pᵒ ⊨ [ j , Inv ]⇛ᵍ¹ Pᵒ
  ⇛ᵍ¹-intro =  ⤇ᵒ-intro › ⤇ᵒ⇒⇛ᵍ¹

  -- Introduce ⇛ᴳ with ✓ᴴ

  ⇛ᴳ-intro-✓ᴴ :  (∀{Eᴵⁿ} → set (get Eᴵⁿ) Eᴵⁿ ≡˙ Eᴵⁿ) →
                 Pᵒ ⊨ ⟨ H ⟩[ get , set , Inv ]⇛ᴳ⟨ H ⟩ ⌜ ✓ᴴ H ⌝ᵒ× Pᵒ
  ⇛ᴳ-intro-✓ᴴ sg≡ =  ⇛ᴳ-make $ ⤇ᴱ-intro-✓ › ⤇ᴱ-respᴱˡ (envᴳ-cong sg≡) ›
    ⤇ᴱ-mono (λ (-, E✓) → ∗ᵒ-monoˡ (E✓ iᴴᵉᵃᵖ .↓ .π₀ ,_)) › ⤇ᴱ-param

  -- Join the same ⇛ᴳs / ⇛ᵍs

  ⇛ᴳ-join :  (∀{Eᴵⁿ x} → get (set x Eᴵⁿ) ≡ x) →
    (∀{Eᴵⁿ x y} → set y (set x Eᴵⁿ) ≡˙ set y Eᴵⁿ) →
    ⟨ H ⟩[ get , set , Inv ]⇛ᴳ⟨ H' ⟩ ⟨ H' ⟩[ get , set , Inv ]⇛ᴳ⟨ H'' ⟩ Pᵒ  ⊨
      ⟨ H ⟩[ get , set , Inv ]⇛ᴳ⟨ H'' ⟩ Pᵒ
  ⇛ᴳ-join {Inv = Inv} gs≡ ss≡s =  ⇛ᴳ-make {Pᵒ = ⟨ _ ⟩[ _ ]⇛ᴳ⟨ _ ⟩ _} $
    ⇛ᴳ-apply › ⤇ᴱ-mono (λ _ → ∗ᵒ-monoʳ (substᵒ Inv (◠ gs≡)) › ⇛ᴳ-apply) ›
    ⤇ᴱ-join › ⤇ᴱ-respᴱʳ (envᴳ-cong ss≡s) › ⤇ᴱ-param

  ⇛ᵍ-join :  (∀{Eᴵⁿ x} → get (set x Eᴵⁿ) ≡ x) →
             (∀{Eᴵⁿ x y} → set y (set x Eᴵⁿ) ≡˙ set y Eᴵⁿ) →
             [ get , set , Inv ]⇛ᵍ [ get , set , Inv ]⇛ᵍ Pᵒ  ⊨
               [ get , set , Inv ]⇛ᵍ Pᵒ
  ⇛ᵍ-join gs≡ ss≡s big _ =  big _ ▷ ⇛ᴳ-mono (_$ _) ▷ ⇛ᴳ-join gs≡ ss≡s

  -- Join two different ⇛ᴳs / ⇛ᵍs

  ⇛ᴳ-join2 :  (∀{Eᴵⁿ x} → get' (set x Eᴵⁿ) ≡ get' Eᴵⁿ) →
    ⟨ H ⟩[ get , set , Inv ]⇛ᴳ⟨ H' ⟩ ⟨ H' ⟩[ get' , set' , Inv' ]⇛ᴳ⟨ H'' ⟩ Pᵒ  ⊨
      ⟨ H ⟩[ (λ Eᴵⁿ → (get Eᴵⁿ , get' Eᴵⁿ)) , (λ (x , y) → set x › set' y) ,
             (λ (x , y) → Inv x ∗ᵒ Inv' y) ]⇛ᴳ⟨ H'' ⟩ Pᵒ
  ⇛ᴳ-join2 {Inv' = Inv'} g's≡g' =  ⇛ᴳ-make {Pᵒ = ⟨ _ ⟩[ _ ]⇛ᴳ⟨ _ ⟩ _} $
      ∗ᵒ-assocˡ › ∗ᵒ-monoˡ ⇛ᴳ-apply › ⤇ᴱ-eatʳ ›
      ⤇ᴱ-mono (λ _ → ∗ᵒ-assocʳ › ∗ᵒ-monoʳ ∗ᵒ-comm › ∗ᵒ-assocˡ ›
        ∗ᵒ-monoˡ (∗ᵒ-monoʳ (substᵒ Inv' (◠ g's≡g')) › ⇛ᴳ-apply) ›
        ⤇ᴱ-eatʳ › ⤇ᴱ-mono λ _ → ∗ᵒ-assocʳ › ∗ᵒ-monoʳ ∗ᵒ-comm) › ⤇ᴱ-join

  ⇛ᵍ-join2 :  (∀{Eᴵⁿ x} → get' (set x Eᴵⁿ) ≡ get' Eᴵⁿ) →
    [ get , set , Inv ]⇛ᵍ [ get' , set' , Inv' ]⇛ᵍ Pᵒ  ⊨
      [ (λ Eᴵⁿ → (get Eᴵⁿ , get' Eᴵⁿ)) , (λ (x , y) → set x › set' y) ,
        (λ (x , y) → Inv x ∗ᵒ Inv' y) ]⇛ᵍ Pᵒ
  ⇛ᵍ-join2 g's≡g' big _ =  big _ ▷ ⇛ᴳ-mono (_$ _) ▷ ⇛ᴳ-join2 g's≡g'

  -- Let ⇛ᴳ/⇛ᵍ eat a proposition under ∗ᵒ

  ⇛ᴳ-eatˡ :  Qᵒ ∗ᵒ (⟨ H ⟩[ gsI ]⇛ᴳ⟨ H' ⟩ Pᵒ)  ⊨ ⟨ H ⟩[ gsI ]⇛ᴳ⟨ H' ⟩  Qᵒ ∗ᵒ Pᵒ
  ⇛ᴳ-eatˡ =  ⇛ᴳ-make {Pᵒ = _ ∗ᵒ _} $ ∗ᵒ-assocʳ › ∗ᵒ-monoʳ ⇛ᴳ-apply › ⤇ᴱ-eatˡ ›
    ⤇ᴱ-mono λ _ → ∗ᵒ-assocˡ

  ⇛ᴳ-eatʳ :  (⟨ H ⟩[ gsI ]⇛ᴳ⟨ H' ⟩ Pᵒ) ∗ᵒ Qᵒ  ⊨ ⟨ H ⟩[ gsI ]⇛ᴳ⟨ H' ⟩  Pᵒ ∗ᵒ Qᵒ
  ⇛ᴳ-eatʳ =  ∗ᵒ-comm › ⇛ᴳ-eatˡ › ⇛ᴳ-mono ∗ᵒ-comm

  ⇛ᵍ-eatˡ :  Qᵒ ∗ᵒ ([ gsI ]⇛ᵍ Pᵒ)  ⊨ [ gsI ]⇛ᵍ  Qᵒ ∗ᵒ Pᵒ
  ⇛ᵍ-eatˡ big _ =  big ▷ ∗ᵒ-monoʳ (_$ _) ▷ ⇛ᴳ-eatˡ

  ⇛ᵍ-eatʳ :  ([ gsI ]⇛ᵍ Pᵒ) ∗ᵒ Qᵒ  ⊨ [ gsI ]⇛ᵍ  Pᵒ ∗ᵒ Qᵒ
  ⇛ᵍ-eatʳ big _ =  big ▷ ∗ᵒ-monoˡ (_$ _) ▷ ⇛ᴳ-eatʳ

  -- Adequacy of ⇛ᴳ
  -- If we have Y under [⊤]ᴺᵒ and ⟨ H ⟩[ get , _ , Inv ]⇛ᴳ⟨ _ ⟩ for valid H and
  -- Inv (get ∅ᴵⁿᴳ) is a tautology, then Y holds purely

  ⇛ᴳ-adeq :  ⊨ Inv (get ∅ᴵⁿᴳ) →  ✓ᴴ H →
             [⊤]ᴺᵒ ⊨ ⟨ H ⟩[ get , set , Inv ]⇛ᴳ⟨ H' ⟩ ⌜ Y ⌝ᵒ →  Y
  ⇛ᴳ-adeq ⊨Invg∅ ✓H [⊤]⊨H⇛H'Y =  ⤇ᴱ-adeq (∅ᴵⁿᴳ-✓ᴺ ✓H) $
    [⊤]⊨H⇛H'Y › ∗ᵒ?-intro ⊨Invg∅ › ⇛ᴳ-apply ›
    ⤇ᴱ-mono λ _ → ∗ᵒ-monoˡ {Qᵒ = ⌜ _ ⌝ᵒ× ⊤ᵒ₀} (_,-) › ∃ᵒ∗ᵒ-out › π₀
