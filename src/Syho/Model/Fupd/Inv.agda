--------------------------------------------------------------------------------
-- Fancy update on the impredicative invariant
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Fupd.Inv where

open import Base.Level using (Level; _⊔ᴸ_; 1ᴸ)
open import Base.Func using (_$_; _▷_; _∘_; _›_)
open import Base.Prod using (_,_; -,_; -ᴵ,_; uncurry)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Base.Nat using (ℕ)
open import Syho.Logic.Prop using (Name; Prop∞)
open import Syho.Model.ERA.Inv using (Envᴵⁿᵛ)
open import Syho.Model.ERA.Glob using (jᴵⁿᵛ; ∅ᴵⁿᴳ)
open import Syho.Model.Prop.Base using (Propᵒ; _⊨✓_; _⊨_; ⊨_; _⨿ᵒ_; _∗ᵒ_; _-∗ᵒ_;
  ∗ᵒ⇒∗ᵒ'; ∗ᵒ'⇒∗ᵒ; ∗ᵒ-Mono; ∗ᵒ-mono; ∗ᵒ-mono✓ˡ; ∗ᵒ-monoˡ; ∗ᵒ-mono✓ʳ; ∗ᵒ-monoʳ;
  ∗ᵒ-comm; ∗ᵒ-assocˡ; ∗ᵒ-assocʳ; ?∗ᵒ-comm; ∗ᵒ?-comm; ?∗ᵒ-intro; ∗ᵒ-elimʳ;
  ∗ᵒ⨿ᵒ-out; -∗ᵒ-applyˡ; ⤇ᴱ⟨⟩-mono✓; ⤇ᴱ⟨⟩-param; ⤇ᴱ⟨⟩-eatʳ; □ᵒ-elim; dup-□ᵒ)
open import Syho.Model.Prop.Basic using (⸨_⸩ᴮ; ⸨⸩ᴮ-Mono)
open import Syho.Model.Prop.Smry using (Smry; Smry-0; Smry-add-š; Smry-rem-<;
  Smry-back)
open import Syho.Model.Prop.Names using ([^_]ᴺᵒ; [^]ᴺᵒ-no2)
open import Syho.Model.Prop.Inv using (Inv; &ⁱ⟨_⟩ᵒ_; Invk; %ⁱ⟨_⟩ᵒ_; dup-&ⁱᵒ;
  Invk-no2; &ⁱᵒ-Invk-new; Inv-agree; Invk-agree)
open import Syho.Model.Prop.Interp using (⸨_⸩; ⸨⸩-Mono; ⸨⸩-ᴮ⇒)
open import Syho.Model.Prop.Sound using (⊢-sem)
open import Syho.Model.Fupd.Base using ([_]⇛ᵍ¹_; ⇛ᵍ-mono✓; ⊨✓⇒⊨-⇛ᵍ; ⇛ᵍ¹-make;
  ⇛ᵍ¹-intro; ⇛ᵍ-eatˡ)

private variable
  ł :  Level
  i :  ℕ
  nm :  Name
  P :  Prop∞
  Pᵒ :  Propᵒ ł

--------------------------------------------------------------------------------
-- Fancy update on Invᴱᴿᴬ

-- Lineᴵⁿᵛ :  Line for Invᴵⁿᵛ

Lineᴵⁿᵛ :  ℕ →  Name →  Prop∞ →  Propᵒ 1ᴸ
Lineᴵⁿᵛ i nm P =  Invk i nm P ∗ᵒ ⸨ P ⸩  ⨿ᵒ  [^ nm ]ᴺᵒ

-- Invᴵⁿᵛ :  Invariant for Invᴱᴿᴬ

Invᴵⁿᵛ :  Envᴵⁿᵛ →  Propᵒ 1ᴸ
Invᴵⁿᵛ (ⁿPˇ˙ , n) =  Smry (uncurry ∘ Lineᴵⁿᵛ) ⁿPˇ˙ n

-- ⇛ᴵⁿᵛ :  Fancy update on Invᴱᴿᴬ

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

  -- Get &ⁱ⟨ nm ⟩ᵒ P by storing ⸨ P ⸩ minus &ⁱ⟨ nm ⟩ᵒ ⸨ P ⸩

  &ⁱᵒ-new-rec :  &ⁱ⟨ nm ⟩ᵒ P -∗ᵒ ⸨ P ⸩  ⊨ ⇛ᴵⁿᵛ  &ⁱ⟨ nm ⟩ᵒ P
  &ⁱᵒ-new-rec {P = P} =  ⇛ᵍ¹-make $ ?∗ᵒ-intro &ⁱᵒ-Invk-new ›
    -- (&∗Invk)∗(&-*P)*INV → → (&∗&∗Invk)∗(&-*P)*INV → →
    -- &∗((&∗Invk)∗(&-*P))*INV → → &∗(Invk∗&∗(&-*P))*INV → &∗(Invk∗P)∗INV → →
    -- &∗INV
    ⤇ᴱ⟨⟩-eatʳ › ⤇ᴱ⟨⟩-mono✓ (λ _ ✓∙ → ∗ᵒ-monoˡ (∗ᵒ-monoˡ dup-&ⁱᵒ › ∗ᵒ-assocʳ) ›
      ∗ᵒ-assocʳ › ∗ᵒ-mono✓ʳ (λ ✓∙ → ∗ᵒ-assocˡ › ∗ᵒ-mono✓ˡ (λ ✓∙ →
      ∗ᵒ-monoˡ ∗ᵒ-comm › ∗ᵒ-assocʳ › ∗ᵒ-mono✓ʳ (-∗ᵒ-applyˡ $ ⸨⸩-Mono {P}) ✓∙ ›
      ĩ₀_) ✓∙ › Smry-add-š) ✓∙) › ⤇ᴱ⟨⟩-param

  -- Store [^ nm ]ᴺᵒ to get Invk i nm P and ⸨ P ⸩ under Lineᴵⁿᵛ

  [^]ᴺᵒ-open :  [^ nm ]ᴺᵒ  ∗ᵒ  Lineᴵⁿᵛ i nm P  ⊨✓
                  (Invk i nm P  ∗ᵒ  ⸨ P ⸩)  ∗ᵒ  Lineᴵⁿᵛ i nm P
  [^]ᴺᵒ-open ✓∙ =  ∗ᵒ⨿ᵒ-out › λ{
    (ĩ₀ [nm]∗Invk∗P) →  [nm]∗Invk∗P ▷ ∗ᵒ-comm ▷ ∗ᵒ-monoʳ ĩ₁_;
    (ĩ₁ [nm]∗[nm]) →  [nm]∗[nm] ▷ [^]ᴺᵒ-no2 ✓∙ ▷ λ () }

  -- Store Inv i nm P and [^ nm ]ᴺᵒ to get ⸨ P ⸩ and Invk i nm P

  Inv-open :  Inv i nm P  ∗ᵒ  [^ nm ]ᴺᵒ  ⊨ ⇛ᴵⁿᵛ  ⸨ P ⸩  ∗ᵒ  Invk i nm P
  Inv-open =  ⇛ᵍ¹-make $ ∗ᵒ-assocʳ › ∗ᵒ-monoˡ Inv-agree › ⤇ᴱ⟨⟩-eatʳ ›
    -- Inv∗[nm]∗INV → [nm]∗INV → [nm]∗Line∗INV → ([nm]∗Line)∗INV →
    -- ((Invk∗P)∗Line)∗INV → (Invk∗P)∗Line∗INV → (P∗Invk)∗INV
    ⤇ᴱ⟨⟩-mono✓ (λ (i<n , ≡šR) ✓∙ → ∗ᵒ-elimʳ ∗ᵒ-Mono ›
      ∗ᵒ-monoʳ (Smry-rem-< i<n ≡šR) › ∗ᵒ-assocˡ › ∗ᵒ-mono✓ˡ [^]ᴺᵒ-open ✓∙ ›
      ∗ᵒ-assocʳ › ∗ᵒ-mono ∗ᵒ-comm (Smry-back ≡šR)) › ⤇ᴱ⟨⟩-param

  -- Store &ⁱ⟨ nm ⟩ᵒ P and [^ nm ]ᴺᵒ to get ⸨ P ⸩ and %ⁱ⟨ nm ⟩ᵒ P

  &ⁱᵒ-open :  &ⁱ⟨ nm ⟩ᵒ P  ∗ᵒ  [^ nm ]ᴺᵒ  ⊨ ⇛ᴵⁿᵛ  ⸨ P ⸩  ∗ᵒ  %ⁱ⟨ nm ⟩ᵒ P
  &ⁱᵒ-open =  ∗ᵒ⇒∗ᵒ' › λ{ (-, -, ∙⊑ , (-, Q , -ᴵ, -, (Q∗R⊢P , Q∗P⊢R) ,
    □Q∗InvRb) , [nm]c) → let MonoQ = ⸨⸩ᴮ-Mono {Q} in
    -- (□Q∗Inv)∗[nm] → □Q∗Inv∗[nm] → → □Q∗R∗Invk → → (Q∗Q)∗R∗Invk → → →
    -- (Q∗R)∗Q∗Invk → P∗Q∗Invk → P∗%
    ∗ᵒ'⇒∗ᵒ (-, -, ∙⊑ , □Q∗InvRb , [nm]c) ▷ ∗ᵒ-assocʳ ▷ ∗ᵒ-monoʳ Inv-open ▷
    ⇛ᵍ-eatˡ ▷ ⇛ᵍ-mono✓ λ ✓∙ → ∗ᵒ-monoˡ (dup-□ᵒ MonoQ ›
    ∗ᵒ-mono (□ᵒ-elim MonoQ › ⸨⸩-ᴮ⇒ {Q}) (□ᵒ-elim MonoQ)) › ∗ᵒ-assocʳ ›
    ∗ᵒ-monoʳ ?∗ᵒ-comm › ∗ᵒ-assocˡ › ∗ᵒ-mono✓ˡ (⊢-sem Q∗R⊢P) ✓∙ › ∗ᵒ-monoʳ
    λ big → -, Q , -ᴵ, -, Q∗P⊢R , big }

  -- Store Invk i nm P and ⸨ P ⸩ to get [^ nm ]ᴺᵒ under Lineᴵⁿᵛ

  Invk-close' :  (Invk i nm P  ∗ᵒ  ⸨ P ⸩)  ∗ᵒ  Lineᴵⁿᵛ i nm P  ⊨✓
                   [^ nm ]ᴺᵒ  ∗ᵒ  Lineᴵⁿᵛ i nm P
  Invk-close' ✓∙ =  ∗ᵒ⨿ᵒ-out › λ{
    (ĩ₀ Invk∗P²) →  Invk∗P² ▷ ∗ᵒ-assocˡ ▷
      ∗ᵒ-mono✓ˡ (λ ✓∙ → ∗ᵒ?-comm › ∗ᵒ-mono✓ˡ Invk-no2 ✓∙ › ∗ᵒ⇒∗ᵒ') ✓∙ ▷
      ∗ᵒ⇒∗ᵒ' ▷ λ ();
    (ĩ₁ Invk∗P∗[nm]) →  Invk∗P∗[nm] ▷ ∗ᵒ-comm ▷ ∗ᵒ-monoʳ ĩ₀_ }

  -- Store ⸨ P ⸩ and Invk i nm P to get [^ nm ]ᴺᵒ

  Invk-close :  ⸨ P ⸩  ∗ᵒ  Invk i nm P  ⊨ ⇛ᴵⁿᵛ  [^ nm ]ᴺᵒ
  Invk-close =  ∗ᵒ-comm › ⇛ᵍ¹-make $ ∗ᵒ-assocʳ › ∗ᵒ-monoˡ Invk-agree ›
    ⤇ᴱ⟨⟩-eatʳ › ⤇ᴱ⟨⟩-mono✓ (λ (i<n , ≡šR) ✓∙ →
      -- Invk∗P∗INV → (Invk∗P)∗INV → (Invk∗P)∗Line∗INV → ((Invk∗P)∗Line)∗INV →
      -- ([nm]∗Line)∗INV → [nm]∗Line∗INV → [nm]∗INV
      ∗ᵒ-assocˡ › ∗ᵒ-monoʳ (Smry-rem-< i<n ≡šR) › ∗ᵒ-assocˡ ›
      ∗ᵒ-mono✓ˡ Invk-close' ✓∙ › ∗ᵒ-assocʳ › ∗ᵒ-monoʳ $ Smry-back ≡šR) ›
    ⤇ᴱ⟨⟩-param

  -- Store ⸨ P ⸩ and %ⁱ⟨ nm ⟩ᵒ P to get [^ nm ]ᴺᵒ

  %ⁱᵒ-close :  ⸨ P ⸩  ∗ᵒ  %ⁱ⟨ nm ⟩ᵒ P  ⊨ ⇛ᴵⁿᵛ  [^ nm ]ᴺᵒ
  %ⁱᵒ-close =  ∗ᵒ⇒∗ᵒ' › λ{ (-, -, ∙⊑ , Pb , -, Q , -ᴵ, -, Q∗P⊢R , Q∗Invkc) →
    -- P∗Q∗Invk → Q∗P∗Invk → (Q∗P)∗Invk → → R∗Invk
    ∗ᵒ'⇒∗ᵒ (-, -, ∙⊑ , Pb , Q∗Invkc) ▷ ⊨✓⇒⊨-⇛ᵍ λ ✓∙ → ?∗ᵒ-comm › ∗ᵒ-assocˡ ›
    ∗ᵒ-mono✓ˡ (λ ✓∙ → ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {Q}) › ⊢-sem Q∗P⊢R ✓∙) ✓∙ › Invk-close }
