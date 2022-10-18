--------------------------------------------------------------------------------
-- Super update on the impredicative invariant
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Inv where

open import Base.Level using (Level; _⊔ᴸ_; 1ᴸ)
open import Base.Func using (_$_; _▷_; _∘_; _›_)
open import Base.Prod using (_,_; -,_; -ᴵ,_; uncurry)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Base.Nat using (ℕ)
open import Syho.Logic.Prop using (Name; Prop∞)
open import Syho.Logic.Core using (_»_; ∗⇒∧)
open import Syho.Model.ERA.Inv using (Envᴵⁿᵛ; inv; invk; inv-invk-new;
  inv-agree; invk-agree)
open import Syho.Model.ERA.Glob using (jᴵⁿᵛ; ∅ᴵⁿᴳ)
open import Syho.Model.Prop.Base using (Propᵒ; _⊨✓_; _⊨_; ⊨_; _⨿ᵒ_; _∗ᵒ_; _-∗ᵒ_;
  ∗ᵒ⇒∗ᵒ'; ∗ᵒ'⇒∗ᵒ; ∗ᵒ-mono; ∗ᵒ-mono✓ˡ; ∗ᵒ-monoˡ; ∗ᵒ-mono✓ʳ; ∗ᵒ-monoʳ; ∗ᵒ-comm;
  ∗ᵒ-assocˡ; ∗ᵒ-assocʳ; ∗ᵒ?-comm; ?∗ᵒ-intro; ∗ᵒ-elimˡ; ∗ᵒ⨿ᵒ-out; -∗ᵒ-applyˡ;
  ⤇ᴱ-mono✓; ⤇ᴱ-mono; ⤇ᴱ-param; ⤇ᴱ-eatˡ; ⤇ᴱ-eatʳ; □ᵒ-Mono; □ᵒ-elim; □ᵒˡ-×ᵒ⇒∗ᵒ;
  dup-□ᵒ; ↝-◎⟨⟩-⤇ᴱ; ε↝-◎⟨⟩-⤇ᴱ)
open import Syho.Model.Prop.Basic using (⸨_⸩ᴮ; ⸨⸩ᴮ-Mono)
open import Syho.Model.Prop.Smry using (Smry; Smry-0; Smry-add-š; Smry-rem-<;
  Smry-upd)
open import Syho.Model.Prop.Names using ([^_]ᴺᵒ; [^]ᴺᵒ-no2)
open import Syho.Model.Prop.Inv using (&ⁱ⟨_⟩ᵒ_; Invk; %ⁱ⟨_⟩ᵒ_; dup-&ⁱᵒ;
  Invk-no2; &ⁱᵒ-Invk-make)
open import Syho.Model.Prop.Interp using (⸨_⸩; ⸨⸩-Mono; ⸨⸩-ᴮ⇒)
open import Syho.Model.Prop.Sound using (⊢-sem)
open import Syho.Model.Supd.Base using ([_]⇛ᵍ¹_; ⇛ᵍ¹-make; ⇛ᵍ¹-intro)

private variable
  ł :  Level
  i :  ℕ
  nm :  Name
  P :  Prop∞
  Pᵒ :  Propᵒ ł

--------------------------------------------------------------------------------
-- Super update on Invᴱᴿᴬ

-- Lineᴵⁿᵛ :  Line for Invᴵⁿᵛ

Lineᴵⁿᵛ :  ℕ →  Name →  Prop∞ →  Propᵒ 1ᴸ
Lineᴵⁿᵛ i nm P =  Invk i nm P ∗ᵒ ⸨ P ⸩  ⨿ᵒ  [^ nm ]ᴺᵒ

-- Invᴵⁿᵛ :  Invariant for Invᴱᴿᴬ

Invᴵⁿᵛ :  Envᴵⁿᵛ →  Propᵒ 1ᴸ
Invᴵⁿᵛ (ⁿPˇ˙ , n) =  Smry (uncurry ∘ Lineᴵⁿᵛ) ⁿPˇ˙ n

-- ⇛ᴵⁿᵛ :  Super update on Invᴱᴿᴬ

infix 3 ⇛ᴵⁿᵛ_
⇛ᴵⁿᵛ_ :  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⇛ᴵⁿᵛ Pᵒ =  [ jᴵⁿᵛ , Invᴵⁿᵛ ]⇛ᵍ¹ Pᵒ

abstract

  -- Get Invᴵⁿᵛ (∅ᴵⁿᴳ jᴵⁿᵛ) for free

  Invᴵⁿᵛ-∅ :  ⊨ Invᴵⁿᵛ (∅ᴵⁿᴳ jᴵⁿᵛ)
  Invᴵⁿᵛ-∅ =  Smry-0

  -- Introduce ⇛ᴵⁿᵛ

  ⇛ᴵⁿᵛ-intro :  Pᵒ  ⊨ ⇛ᴵⁿᵛ  Pᵒ
  ⇛ᴵⁿᵛ-intro =  ⇛ᵍ¹-intro

  -- Get &ⁱ⟨ nm ⟩ᵒ P by storing P minus &ⁱ⟨ nm ⟩ᵒ P

  &ⁱᵒ-new-rec :  &ⁱ⟨ nm ⟩ᵒ P -∗ᵒ ⸨ P ⸩  ⊨ ⇛ᴵⁿᵛ  &ⁱ⟨ nm ⟩ᵒ P
  &ⁱᵒ-new-rec {P = P} =  ⇛ᵍ¹-make $ ?∗ᵒ-intro (ε↝-◎⟨⟩-⤇ᴱ inv-invk-new) ›
    ⤇ᴱ-eatʳ › ⤇ᴱ-mono✓ (λ _ ✓∙ → ∗ᵒ-monoˡ (&ⁱᵒ-Invk-make › ∗ᵒ-monoˡ dup-&ⁱᵒ ›
      -- ((&∗&)∗Invk)∗(&-*P)*INV → → → &∗((&∗Invk)∗(&-*P))*INV
      ∗ᵒ-assocʳ) › ∗ᵒ-assocʳ › ∗ᵒ-mono✓ʳ (λ ✓∙ → ∗ᵒ-assocˡ ›
      -- ((&∗Invk)∗(&-*P))*INV → → (Invk∗(&∗(&-*P)))*INV → (Invk∗P)∗INV → → INV
      ∗ᵒ-mono✓ˡ (λ ✓∙ → ∗ᵒ-monoˡ ∗ᵒ-comm › ∗ᵒ-assocʳ ›
      ∗ᵒ-mono✓ʳ (-∗ᵒ-applyˡ $ ⸨⸩-Mono {P}) ✓∙ › ĩ₀_) ✓∙ › Smry-add-š) ✓∙) ›
    ⤇ᴱ-param

  -- Store [^ nm ]ᴺᵒ to get Invk i nm P and P under Lineᴵⁿᵛ

  [^]ᴺᵒ-open :  [^ nm ]ᴺᵒ  ∗ᵒ  Lineᴵⁿᵛ i nm P  ⊨✓
                  (Invk i nm P  ∗ᵒ  ⸨ P ⸩)  ∗ᵒ  Lineᴵⁿᵛ i nm P
  [^]ᴺᵒ-open ✓∙ =  ∗ᵒ⨿ᵒ-out › λ{
    (ĩ₀ [nm]∗Invk∗P) →  [nm]∗Invk∗P ▷ ∗ᵒ-comm ▷ ∗ᵒ-monoʳ ĩ₁_;
    (ĩ₁ [nm]∗[nm]) →  [nm]∗[nm] ▷ [^]ᴺᵒ-no2 ✓∙ ▷ λ () }

  -- Store &ⁱ⟨ nm ⟩ᵒ P and [^ nm ]ᴺᵒ to get P and %ⁱ⟨ nm ⟩ᵒ P

  &ⁱᵒ-open :  &ⁱ⟨ nm ⟩ᵒ P  ∗ᵒ  [^ nm ]ᴺᵒ  ⊨ ⇛ᴵⁿᵛ  ⸨ P ⸩  ∗ᵒ  %ⁱ⟨ nm ⟩ᵒ P
  &ⁱᵒ-open =  ⇛ᵍ¹-make $ ∗ᵒ-assocʳ › ∗ᵒ⇒∗ᵒ' › λ{ (-, -, b∙c⊑a ,
    (-, Q , -ᴵ, -, (Q∧R⊢P , Q∧P⊢R) , □Qb , invRb) , [nm]∗INVc) →
    (-, -, b∙c⊑a , □ᵒˡ-×ᵒ⇒∗ᵒ (⸨⸩ᴮ-Mono {Q}) (□Qb ,
      ↝-◎⟨⟩-⤇ᴱ {bⁱ˙ = λ _ → inv _ _ _} inv-agree invRb) ▷ ⤇ᴱ-eatˡ ▷
      ⤇ᴱ-mono (λ _ → ∗ᵒ-elimˡ (□ᵒ-Mono $ ⸨⸩ᴮ-Mono {Q}) › dup-□ᵒ (⸨⸩ᴮ-Mono {Q}) ›
      ∗ᵒ-mono (□ᵒ-elim $ ⸨⸩ᴮ-Mono {Q}) (□ᵒ-elim $ ⸨⸩ᴮ-Mono {Q})) , [nm]∗INVc) ▷
    -- (⤇ Q∗Q)∗[nm]∗INV → ⤇ (Q∗Q)∗[nm]∗INV
    ∗ᵒ'⇒∗ᵒ {Qᵒ = _ ∗ᵒ _} ▷ ⤇ᴱ-eatʳ ▷ ⤇ᴱ-mono✓ (λ (i<n , ≡šR) ✓∙ → ∗ᵒ-mono✓ʳ
    -- [nm]∗INV → [nm]∗LineP∗INV → → → (Invk∗R)∗LineP∗INV → (Invk∗R)∗INV
    (λ ✓∙ → ∗ᵒ-monoʳ (Smry-rem-< i<n ≡šR) › ∗ᵒ-assocˡ ›
      ∗ᵒ-mono✓ˡ [^]ᴺᵒ-open ✓∙ › ∗ᵒ-assocʳ › ∗ᵒ-monoʳ $ Smry-upd ≡šR) ✓∙ ›
    -- (Q∗Q)∗(Invk∗R)∗INV → ((Q∗Q)∗Invk∗R)∗INV
    ∗ᵒ-assocˡ › ∗ᵒ-mono✓ˡ (λ ✓∙ →
    -- (Q∗Q)∗Invk∗R → → → (Q∗R)∗Q∗Invk → P∗(Q∗Invk) → P∗%
    ∗ᵒ-monoʳ ∗ᵒ-comm › ∗ᵒ-assocˡ › ∗ᵒ-monoˡ ∗ᵒ?-comm › ∗ᵒ-assocʳ ›
    ∗ᵒ-mono✓ˡ (λ ✓∙ → ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {Q}) › ⊢-sem (∗⇒∧ » Q∧R⊢P) ✓∙) ✓∙ ›
    ∗ᵒ-monoʳ (λ big → -, -, -ᴵ, -, ∗⇒∧ » Q∧P⊢R , big)) ✓∙) ▷ ⤇ᴱ-param }

  -- Store Invk i nm P and P to get [^ nm ]ᴺᵒ under Lineᴵⁿᵛ

  Invk-close :  (Invk i nm P  ∗ᵒ  ⸨ P ⸩)  ∗ᵒ  Lineᴵⁿᵛ i nm P  ⊨✓
                  [^ nm ]ᴺᵒ  ∗ᵒ  Lineᴵⁿᵛ i nm P
  Invk-close ✓∙ =  ∗ᵒ⨿ᵒ-out › λ{
    (ĩ₀ Invk∗P²) →  Invk∗P² ▷ ∗ᵒ-assocˡ ▷
      ∗ᵒ-mono✓ˡ (λ ✓∙ → ∗ᵒ?-comm › ∗ᵒ-mono✓ˡ Invk-no2 ✓∙ › ∗ᵒ⇒∗ᵒ') ✓∙ ▷
      ∗ᵒ⇒∗ᵒ' ▷ λ ();
    (ĩ₁ Invk∗P∗[nm]) →  Invk∗P∗[nm] ▷ ∗ᵒ-comm ▷ ∗ᵒ-monoʳ ĩ₀_ }

  -- Store P and %ⁱ⟨ nm ⟩ᵒ P to get [^ nm ]ᴺᵒ

  %ⁱᵒ-close :  ⸨ P ⸩  ∗ᵒ  %ⁱ⟨ nm ⟩ᵒ P  ⊨ ⇛ᴵⁿᵛ  [^ nm ]ᴺᵒ
  %ⁱᵒ-close =  ∗ᵒ-comm › ⇛ᵍ¹-make $ ∗ᵒ-assocʳ › ∗ᵒ⇒∗ᵒ' › λ{ (-, -, b∙c⊑a ,
    (-, Q , -ᴵ, -, Q∗P⊢R , Q∗Invkb) , P∗INVc) →
    (-, -, b∙c⊑a , Q∗Invkb ▷ ∗ᵒ-monoʳ
      (↝-◎⟨⟩-⤇ᴱ {bⁱ˙ = λ _ → invk _ _ _} invk-agree) ▷ ⤇ᴱ-eatˡ , P∗INVc) ▷
    ∗ᵒ'⇒∗ᵒ {Qᵒ = _ ∗ᵒ _} ▷ ⤇ᴱ-eatʳ ▷ ⤇ᴱ-mono✓ (λ (i<n , ≡šR) ✓∙ →
    -- (Q∗Invk)∗P∗INV → ((Q∗Invk)∗P)∗INV → → (Invk∗Q∗P)∗INV → (Invk∗R)∗INV →
    -- (Invk∗R)∗INV → (Invk∗R)∗(Line∗INV) → → [nm]∗(Line∗INV) → [nm]∗INV
    ∗ᵒ-assocˡ › ∗ᵒ-mono✓ˡ (λ ✓∙ → ∗ᵒ-monoˡ ∗ᵒ-comm › ∗ᵒ-assocʳ ›
    ∗ᵒ-mono✓ʳ (λ ✓∙ → ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {Q}) › ⊢-sem Q∗P⊢R ✓∙) ✓∙) ✓∙ ›
    ∗ᵒ-monoʳ (Smry-rem-< i<n ≡šR) › ∗ᵒ-assocˡ ›
    ∗ᵒ-mono✓ˡ Invk-close ✓∙ › ∗ᵒ-assocʳ › ∗ᵒ-monoʳ $ Smry-upd ≡šR) ▷ ⤇ᴱ-param }
