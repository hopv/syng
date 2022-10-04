--------------------------------------------------------------------------------
-- Super update on the impredicative invariant
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Supd.Inv where

open import Base.Level using (Level; _⊔ᴸ_; 1ᴸ)
open import Base.Func using (_$_; _∘_; _›_)
open import Base.Dec using (upd˙)
open import Base.Prod using (_,_; uncurry)
open import Base.Sum using (ĩ₀_)
open import Base.Nat using (ℕ)
open import Syho.Lang.Reduce using (Mem)
open import Syho.Logic.Prop using (Name; Prop∞)
open import Syho.Model.ERA.Inv using (Envᴵⁿᵛ; inv-invk-alloc)
open import Syho.Model.ERA.Glob using (jᴵⁿᵛ; upd˙-out-envᴳ)
open import Syho.Model.Prop.Base using (Propᵒ; _⊨_; _⨿ᵒ_; _∗ᵒ_; _-∗ᵒ_; ∗ᵒ-mono;
  ∗ᵒ-mono✓ˡ; ∗ᵒ-monoˡ; ∗ᵒ-mono✓ʳ; ∗ᵒ-comm; ∗ᵒ-assocˡ; ∗ᵒ-assocʳ; ?∗ᵒ-intro;
  -∗ᵒ-apply; ⤇ᴱ-mono✓; ⤇ᴱ-param; ⤇ᴱ-eatʳ; ε↝-◎⟨⟩-⤇ᴱ)
open import Syho.Model.Prop.Smry using (Smry; Smry-add-š)
open import Syho.Model.Prop.Names using ([^_]ᴺᵒ)
open import Syho.Model.Prop.Inv using (Invᵒ; Invk; dup-Invᵒ; Invᵒ∗ᵒInvk-make)
open import Syho.Model.Prop.Interp using (⸨_⸩; ⸨⸩-Mono)
open import Syho.Model.Supd.Base using ([_]⇛ᵍ¹_; ⇛ᵍ¹-make)

private variable
  ł :  Level
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
