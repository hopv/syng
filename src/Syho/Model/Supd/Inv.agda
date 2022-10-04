--------------------------------------------------------------------------------
-- Super update on the impredicative invariant
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Inv where

open import Base.Level using (Level; _⊔ᴸ_; 1ᴸ)
open import Base.Func using (_$_; _▷_; _∘_; _›_)
open import Base.Few using (absurd)
open import Base.Dec using (upd˙)
open import Base.Prod using (_,_; -,_; -ᴵ,_; uncurry)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Base.Nat using (ℕ)
open import Syho.Lang.Reduce using (Mem)
open import Syho.Logic.Prop using (Name; Prop∞)
open import Syho.Logic.Core using (_»_; ∗⇒∧)
open import Syho.Model.ERA.Inv using (Envᴵⁿᵛ; inv; inv-invk-alloc; inv-agree)
open import Syho.Model.ERA.Glob using (jᴵⁿᵛ; upd˙-out-envᴳ)
open import Syho.Model.Prop.Base using (Propᵒ; _⊨✓_; _⊨_; _⨿ᵒ_; _∗ᵒ_; _-∗ᵒ_;
  ∗ᵒ⇒∗ᵒ'; ∗ᵒ'⇒∗ᵒ; ∗ᵒ-mono; ∗ᵒ-mono✓ˡ; ∗ᵒ-monoˡ; ∗ᵒ-mono✓ʳ; ∗ᵒ-monoʳ; ∗ᵒ-comm;
  ∗ᵒ-assocˡ; ∗ᵒ-assocʳ; ∗ᵒ?-comm; ?∗ᵒ-intro; ∗ᵒ-elimˡ; ∗ᵒ⨿ᵒ-out; -∗ᵒ-apply;
  ⤇ᴱ-mono✓; ⤇ᴱ-mono; ⤇ᴱ-param; ⤇ᴱ-eatˡ; ⤇ᴱ-eatʳ; □ᵒ-Mono; □ᵒ-elim; □ᵒˡ-×ᵒ⇒∗ᵒ;
  dup-□ᵒ; ↝-◎⟨⟩-⤇ᴱ; ε↝-◎⟨⟩-⤇ᴱ)
open import Syho.Model.Prop.Basic using (⸨_⸩ᴮ; ⸨⸩ᴮ-Mono)
open import Syho.Model.Prop.Smry using (Smry; Smry-add-š; Smry-rem-<; Smry-upd)
open import Syho.Model.Prop.Names using ([^_]ᴺᵒ; [^]ᴺᵒ-no2)
open import Syho.Model.Prop.Inv using (Invᵒ; Invk; OInvᵒ; dup-Invᵒ;
  Invᵒ∗ᵒInvk-make)
open import Syho.Model.Prop.Interp using (⸨_⸩; ⸨⸩-Mono; ⸨⸩-ᴮ⇒)
open import Syho.Model.Prop.Sound using (⊢-sem)
open import Syho.Model.Supd.Base using ([_]⇛ᵍ¹_; ⇛ᵍ¹-make)

private variable
  ł :  Level
  i :  ℕ
  M :  Mem
  nm :  Name
  P :  Prop∞

--------------------------------------------------------------------------------
-- Super update on Invᴱᴿᴬ

-- Line of a super update

Lineᴵⁿᵛ :  ℕ →  Name →  Prop∞ →  Propᵒ 1ᴸ
Lineᴵⁿᵛ i nm P =  Invk i nm P ∗ᵒ ⸨ P ⸩  ⨿ᵒ  [^ nm ]ᴺᵒ

-- Invariant for Invᴱᴿᴬ

Invᴵⁿᵛ :  Envᴵⁿᵛ →  Propᵒ 1ᴸ
Invᴵⁿᵛ (ⁿPˇ˙ , n) =  Smry (uncurry ∘ Lineᴵⁿᵛ) ⁿPˇ˙ n

-- Super update on Invᴱᴿᴬ

infix 3 ⇛ᴵⁿᵛ_
⇛ᴵⁿᵛ_ :  Propᵒ ł →  Propᵒ (1ᴸ ⊔ᴸ ł)
⇛ᴵⁿᵛ Pᵒ =  [ jᴵⁿᵛ , Invᴵⁿᵛ ]⇛ᵍ¹ Pᵒ

abstract

  -- Get Invᵒ nm P by storing P minus Invᵒ nm P

  Invᵒ-alloc-rec :  Invᵒ nm P -∗ᵒ ⸨ P ⸩  ⊨ ⇛ᴵⁿᵛ  Invᵒ nm P
  Invᵒ-alloc-rec {P = P} =  ⇛ᵍ¹-make $ ?∗ᵒ-intro (ε↝-◎⟨⟩-⤇ᴱ inv-invk-alloc) ›
    ⤇ᴱ-eatʳ › ⤇ᴱ-mono✓ (λ _ ✓∙ → ∗ᵒ-monoˡ (Invᵒ∗ᵒInvk-make › ∗ᵒ-monoˡ dup-Invᵒ ›
      -- ((Inv∗Inv)∗Invk)∗(Inv-*P)*INV → → → Inv∗((Inv∗Invk)∗(Inv-*P))*INV
      ∗ᵒ-assocˡ) › ∗ᵒ-assocˡ › ∗ᵒ-mono✓ʳ (λ ✓∙ → ∗ᵒ-assocʳ ›
      -- ((Inv∗Invk)∗(Inv-*P))*INV → → (Invk∗(Inv∗(Inv-*P)))*INV →
      -- (Invk∗P)∗INV → → INV
      ∗ᵒ-mono✓ˡ (λ ✓∙ → ∗ᵒ-monoˡ ∗ᵒ-comm › ∗ᵒ-assocˡ ›
      ∗ᵒ-mono✓ʳ (-∗ᵒ-apply $ ⸨⸩-Mono {P}) ✓∙ › ĩ₀_) ✓∙ › Smry-add-š) ✓∙) ›
    ⤇ᴱ-param

  -- Store [^ nm ]ᴺᵒ to get Invk i nm P and P under Lineᴵⁿᵛ

  [^]ᴺᵒ-open :  [^ nm ]ᴺᵒ  ∗ᵒ  Lineᴵⁿᵛ i nm P  ⊨✓
                  (Invk i nm P  ∗ᵒ  ⸨ P ⸩)  ∗ᵒ  Lineᴵⁿᵛ i nm P
  [^]ᴺᵒ-open ✓∙ =  ∗ᵒ⨿ᵒ-out › λ{
    (ĩ₀ [nm]∗Invk∗P) →  [nm]∗Invk∗P ▷ ∗ᵒ-comm ▷ ∗ᵒ-monoʳ ĩ₁_;
    (ĩ₁ [nm]∗[nm]) →  [nm]∗[nm] ▷ [^]ᴺᵒ-no2 ✓∙ ▷ λ () }

  -- Store Invᵒ nm P and [^ nm ]ᴺᵒ to get P and OInvᵒ nm P

  Invᵒ-open :  Invᵒ nm P  ∗ᵒ  [^ nm ]ᴺᵒ  ⊨ ⇛ᴵⁿᵛ  ⸨ P ⸩  ∗ᵒ  OInvᵒ nm P
  Invᵒ-open =  ⇛ᵍ¹-make $ ∗ᵒ-assocˡ › ∗ᵒ⇒∗ᵒ' › λ{ (-, -, b∙c⊑a ,
    (-, Q , -ᴵ, -, (Q∧R⊢P , Q∧P⊢R) , □Qb , invRb) , [nm]∗INVc) →
    (-, -, b∙c⊑a , □ᵒˡ-×ᵒ⇒∗ᵒ (⸨⸩ᴮ-Mono {Q}) (□Qb ,
      ↝-◎⟨⟩-⤇ᴱ {bⁱ˙ = λ _ → inv _ _ _} inv-agree invRb) ▷ ⤇ᴱ-eatˡ ▷
      ⤇ᴱ-mono (λ _ → ∗ᵒ-elimˡ (□ᵒ-Mono $ ⸨⸩ᴮ-Mono {Q}) › dup-□ᵒ (⸨⸩ᴮ-Mono {Q}) ›
      ∗ᵒ-mono (□ᵒ-elim $ ⸨⸩ᴮ-Mono {Q}) (□ᵒ-elim $ ⸨⸩ᴮ-Mono {Q})) , [nm]∗INVc) ▷
    -- (⤇ Q∗Q)∗[nm]∗INV → ⤇ (Q∗Q)∗[nm]∗INV
    ∗ᵒ'⇒∗ᵒ {Qᵒ = _ ∗ᵒ _} ▷ ⤇ᴱ-eatʳ ▷ ⤇ᴱ-mono✓ (λ (≡šR , i<n) ✓∙ → ∗ᵒ-mono✓ʳ
    -- [nm]∗INV → [nm]∗LineP∗INV → → → (Invk∗R)∗LineP∗INV → (Invk∗R)∗INV
    (λ ✓∙ → ∗ᵒ-monoʳ (Smry-rem-< ≡šR i<n) › ∗ᵒ-assocʳ ›
      ∗ᵒ-mono✓ˡ [^]ᴺᵒ-open ✓∙ › ∗ᵒ-assocˡ › ∗ᵒ-monoʳ $ Smry-upd ≡šR) ✓∙ ›
    -- (Q∗Q)∗(Invk∗R)∗INV → ((Q∗Q)∗Invk∗R)∗INV
    ∗ᵒ-assocʳ › ∗ᵒ-mono✓ˡ (λ ✓∙ →
    -- (Q∗Q)∗Invk∗R → → → (Q∗R)∗Q∗Invk → P∗(Q∗Invk) → P∗OInv
    ∗ᵒ-monoʳ ∗ᵒ-comm › ∗ᵒ-assocʳ › ∗ᵒ-monoˡ ∗ᵒ?-comm › ∗ᵒ-assocˡ ›
    ∗ᵒ-mono✓ˡ (λ ✓∙ → ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {Q}) › ⊢-sem (∗⇒∧ » Q∧R⊢P) ✓∙) ✓∙ ›
    ∗ᵒ-monoʳ (λ big → -, -, -ᴵ, -, ∗⇒∧ » Q∧P⊢R , big)) ✓∙) ▷ ⤇ᴱ-param }
