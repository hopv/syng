--------------------------------------------------------------------------------
-- Interpret the points-to and freeing tokens
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Prop.Mem where

open import Base.Level using (1ᴸ)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Few using (⊤₀)
open import Base.Eq using (_≡_)
open import Base.Dec using (upd˙)
open import Base.Option using (š_; ň)
open import Base.Prod using (∑-syntax; _,_; -,_)
open import Base.Nat using (ℕ; +-0)
open import Base.List using (List; []; _∷_; len; rep)
open import Base.Ratp using (ℚ⁺; 1ᴿ⁺; _≈ᴿ⁺_; _+ᴿ⁺_; _≤1ᴿ⁺)
open import Syho.Lang.Expr using (Addr; _ₒ_; TyVal; ⊤-; Mem; _‼ᴹ_; updᴹ)
open import Syho.Model.ERA.Mem using (Memᴱᴿᴬ; εᴹᵉᵐ; [∙ᴹᵉᵐ∈ⁱ]-syntax;
  [∙ᴹᵉᵐ∈ⁱ⟨⟩]-syntax; ◠˜ᴹᵉᵐ_; _↦⟨_⟩ʳ_; _↦ʳ_; freeʳ; _↦ᴸʳ_; ↦⟨⟩ʳ-cong; ↦⟨⟩ʳ-∙;
  ↦⟨⟩ʳ-≤1; ↦⟨⟩ʳ-agree; [∙∈ⁱ]↦≈↦ᴸʳ; ↦⟨⟩ʳ-read; ↦ʳ-write; ↦ᴸʳ-alloc; freeʳ-š;
  ↦ᴸʳ-free)
open import Syho.Model.ERA.Glob using (iᴹᵉᵐ; Envᴵⁿᴳ; envᴳ; upd˙-mem-envᴳ)
open import Syho.Model.Prop.Base using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; ⊨_; ∃ᵒ-syntax;
  ⌜_⌝ᵒ; ⌜_⌝ᵒ×_; ⊤ᵒ₀; _∗ᵒ_; [∗ᵒ∈ⁱ]-syntax; [∗ᵒ∈ⁱ⟨⟩]-syntax; _⤇ᴱ_; ◎⟨_⟩_; ∃ᵒ-Mono;
  ∗ᵒ-monoʳ; ⤇ᴱ-mono; ⤇ᴱ-respᴱʳ; ⤇ᴱ-param; ◎-Mono; ◎⟨⟩-resp; ◎⟨⟩-ε; ◎⟨⟩-∗ᵒ⇒∙;
  ◎⟨⟩-∙⇒∗ᵒ; ◎⟨⟩-✓; ↝-◎⟨⟩-⤇ᴱ; ε↝-◎⟨⟩-⤇ᴱ)

private variable
  i k n o :  ℕ
  θ :  Addr
  p q :  ℚ⁺
  ᵗu ᵗv :  TyVal
  ᵗvs :  List TyVal
  M :  Mem
  E :  Envᴵⁿᴳ

--------------------------------------------------------------------------------
-- Interpret the points-to and freeing tokens

infix 9 _↦⟨_⟩ᵒ_ _↦ᵒ_

-- ↦⟨ ⟩ᵒ : Interpret the points-to token

_↦⟨_⟩ᵒ_ :  Addr →  ℚ⁺ →  TyVal →  Propᵒ 1ᴸ
θ ↦⟨ p ⟩ᵒ ᵗv =  ◎⟨ iᴹᵉᵐ ⟩ θ ↦⟨ p ⟩ʳ ᵗv

-- ↦ᵒ : ↦⟨ ⟩ᵒ with the fraction 1

_↦ᵒ_ :  Addr →  TyVal →  Propᵒ 1ᴸ
θ ↦ᵒ ᵗv =  θ ↦⟨ 1ᴿ⁺ ⟩ᵒ ᵗv

-- Freeᵒ' : The freeing token over a block id

Freeᵒ' :  ℕ →  ℕ →  Propᵒ 1ᴸ
Freeᵒ' n o =  ◎⟨ iᴹᵉᵐ ⟩ freeʳ n o

-- Freeᵒ : Interpret the freeing token

Freeᵒ :  ℕ →  Addr →  Propᵒ 1ᴸ
Freeᵒ n θ =  ∃ᵒ o ,  ⌜ θ ≡ (o , 0) ⌝ᵒ×  Freeᵒ' n o

-- ↦ᴸᵒ, ↦ᴸᵒ' :  Interpret the points-to token over a list of values

infix 9 _↦ᴸᵒ_ _↦ᴸᵒ'_

_↦ᴸᵒ_ :  Addr →  List TyVal →  Propᵒ 1ᴸ
θ ↦ᴸᵒ ᵗvs =  [∗ᵒ (i , ᵗv) ∈ⁱ ᵗvs ] θ ₒ i ↦ᵒ ᵗv

_↦ᴸᵒ'_ :  ℕ →  List TyVal →  Propᵒ 1ᴸ
o ↦ᴸᵒ' ᵗvs =  ◎⟨ iᴹᵉᵐ ⟩ o ↦ᴸʳ ᵗvs

abstract

  -- Mono for Freeᵒ

  Freeᵒ-Mono :  Monoᵒ $ Freeᵒ n θ
  Freeᵒ-Mono =  ∃ᵒ-Mono λ _ → ∃ᵒ-Mono λ _ → ◎-Mono

  -- Modify the fraction of ↦⟨ ⟩ᵒ

  ↦⟨⟩ᵒ-resp :  p ≈ᴿ⁺ q  →   θ ↦⟨ p ⟩ᵒ ᵗv  ⊨  θ ↦⟨ q ⟩ᵒ ᵗv
  ↦⟨⟩ᵒ-resp p≈q =  ◎⟨⟩-resp $ ↦⟨⟩ʳ-cong p≈q

  -- Merge and split ↦⟨ ⟩ᵒ with ∗ᵒ

  ↦⟨⟩ᵒ-merge :  θ ↦⟨ p ⟩ᵒ ᵗv  ∗ᵒ  θ ↦⟨ q ⟩ᵒ ᵗv  ⊨  θ ↦⟨ p +ᴿ⁺ q ⟩ᵒ ᵗv
  ↦⟨⟩ᵒ-merge =  ◎⟨⟩-∗ᵒ⇒∙ › ◎⟨⟩-resp ↦⟨⟩ʳ-∙

  ↦⟨⟩ᵒ-split :  θ ↦⟨ p +ᴿ⁺ q ⟩ᵒ ᵗv  ⊨  θ ↦⟨ p ⟩ᵒ ᵗv  ∗ᵒ  θ ↦⟨ q ⟩ᵒ ᵗv
  ↦⟨⟩ᵒ-split =  ◎⟨⟩-resp (◠˜ᴹᵉᵐ ↦⟨⟩ʳ-∙) › ◎⟨⟩-∙⇒∗ᵒ

  -- The fraction of ↦⟨ ⟩ᵒ is no more than 1

  ↦⟨⟩ᵒ-≤1 :  θ ↦⟨ p ⟩ᵒ ᵗv  ⊨✓  ⌜ p ≤1ᴿ⁺ ⌝ᵒ
  ↦⟨⟩ᵒ-≤1 ✓∙ =  ◎⟨⟩-✓ ✓∙ › λ (-, ✓↦⟨⟩ʳ) → ↦⟨⟩ʳ-≤1 ✓↦⟨⟩ʳ

  -- Agreement of ↦⟨ ⟩ᵒ

  ↦⟨⟩ᵒ-agree :  θ ↦⟨ p ⟩ᵒ ᵗu  ∗ᵒ  θ ↦⟨ q ⟩ᵒ ᵗv  ⊨✓  ⌜ ᵗu ≡ ᵗv ⌝ᵒ
  ↦⟨⟩ᵒ-agree ✓∙ =  ◎⟨⟩-∗ᵒ⇒∙ › ◎⟨⟩-✓ ✓∙ › λ (-, ✓↦⟨⟩ʳ) → ↦⟨⟩ʳ-agree ✓↦⟨⟩ʳ

  -- [∗ᵒ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] (o , 0) ₒ i ↦ᵒ ᵗv  agrees with
  -- ◎⟨ iᴹᵉᵐ ⟩ [∙ᴹᵉᵐ (i , ᵗv) ∈ⁱ ᵗvs ] (o , i) ↦ʳ ᵗv

  [∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ⇒◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ :
    [∗ᵒ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] (o , 0) ₒ i ↦ᵒ ᵗv  ⊨
      ◎⟨ iᴹᵉᵐ ⟩ [∙ᴹᵉᵐ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] (o , i) ↦ʳ ᵗv
  [∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ⇒◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ {ᵗvs = []} _ =  ◎⟨⟩-ε
  [∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ⇒◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ {k} {_ ∷ ᵗvs'}  rewrite +-0 {k} =
    ∗ᵒ-monoʳ ([∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ⇒◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ {ᵗvs = ᵗvs'}) › ◎⟨⟩-∗ᵒ⇒∙

  ◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ⇒[∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ :
    ◎⟨ iᴹᵉᵐ ⟩ [∙ᴹᵉᵐ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] (o , i) ↦ʳ ᵗv  ⊨
      [∗ᵒ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] (o , 0) ₒ i ↦ᵒ ᵗv
  ◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ⇒[∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ {ᵗvs = []} _ =  _
  ◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ⇒[∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ {k} {_ ∷ ᵗvs'}  rewrite +-0 {k} =
    ◎⟨⟩-∙⇒∗ᵒ › ∗ᵒ-monoʳ $ ◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ⇒[∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ {ᵗvs = ᵗvs'}

  -- (o , 0) ↦ᴸᵒ ᵗvs  agrees with  o ↦ᴸᵒ' ᵗvs

  ↦ᴸᵒ⇒↦ᴸᵒ' :  (o , 0) ↦ᴸᵒ ᵗvs  ⊨  o ↦ᴸᵒ' ᵗvs
  ↦ᴸᵒ⇒↦ᴸᵒ' {ᵗvs = ᵗvs} =  [∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ⇒◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ {ᵗvs = ᵗvs} ›
    ◎⟨⟩-resp $ [∙∈ⁱ]↦≈↦ᴸʳ {ᵗvs = ᵗvs}

  ↦ᴸᵒ'⇒↦ᴸᵒ :  o ↦ᴸᵒ' ᵗvs  ⊨  (o , 0) ↦ᴸᵒ ᵗvs
  ↦ᴸᵒ'⇒↦ᴸᵒ {ᵗvs = ᵗvs} =  ◎⟨⟩-resp (◠˜ᴹᵉᵐ [∙∈ⁱ]↦≈↦ᴸʳ {ᵗvs = ᵗvs}) ›
    ◎⟨⟩[∙∈ⁱ⟨⟩]↦ʳ⇒[∗ᵒ∈ⁱ⟨⟩]ₒ↦ᵒ {ᵗvs = ᵗvs}

  -- Read using ↦⟨⟩ᵒ

  ↦⟨⟩ᵒ-read' :  θ ↦⟨ p ⟩ᵒ ᵗv  ⊨ envᴳ M E ⤇ᴱ λ (_ : ⊤₀) →
                  envᴳ M E , ⌜ M ‼ᴹ θ ≡ š ᵗv ⌝ᵒ×  θ ↦⟨ p ⟩ᵒ ᵗv
  ↦⟨⟩ᵒ-read' =  ↝-◎⟨⟩-⤇ᴱ ↦⟨⟩ʳ-read › ⤇ᴱ-respᴱʳ upd˙-mem-envᴳ ›
    ⤇ᴱ-mono (λ M‼θ≡v →  M‼θ≡v ,_) › ⤇ᴱ-param

  -- Write using ↦⟨⟩ᵒ

  ↦ᵒ-write' :  θ ↦ᵒ ᵗu  ⊨ envᴳ M E ⤇ᴱ λ (_ : ⊤₀) →
                 envᴳ (updᴹ θ ᵗv M) E , θ ↦ᵒ ᵗv
  ↦ᵒ-write' =  ↝-◎⟨⟩-⤇ᴱ ↦ʳ-write › ⤇ᴱ-respᴱʳ upd˙-mem-envᴳ › ⤇ᴱ-param

  -- Allocate to get ↦ᴸᵒ' and Freeᵒ'

  ↦ᴸᵒ'-alloc' :  M o ≡ ň  →
    ⊨ envᴳ M E ⤇ᴱ λ (_ : ⊤₀) → envᴳ (upd˙ o (š rep n ⊤-) M) E ,
      o ↦ᴸᵒ' rep n ⊤-  ∗ᵒ  Freeᵒ' n o
  ↦ᴸᵒ'-alloc' Mo≡ň =  ε↝-◎⟨⟩-⤇ᴱ (↦ᴸʳ-alloc Mo≡ň) ▷
    ⤇ᴱ-respᴱʳ upd˙-mem-envᴳ ▷ ⤇ᴱ-mono λ _ → ◎⟨⟩-∙⇒∗ᵒ

  -- Bounds check using Freeᵒ'

  Freeᵒ'-š' :  Freeᵒ' n o  ⊨ envᴳ M E ⤇ᴱ λ (_ : ⊤₀) → envᴳ M E ,
    ⌜ ∑ ᵗvs , M o ≡ š ᵗvs ⌝ᵒ×  Freeᵒ' n o
  Freeᵒ'-š' =  ↝-◎⟨⟩-⤇ᴱ freeʳ-š › ⤇ᴱ-respᴱʳ upd˙-mem-envᴳ ›
    ⤇ᴱ-mono (λ Mo≡vs →  Mo≡vs ,_) › ⤇ᴱ-param

  -- Free using ↦ᴸᵒ' and Freeᵒ'

  ↦ᴸᵒ'-free' :  len ᵗvs ≡ n  →
    o ↦ᴸᵒ' ᵗvs  ∗ᵒ  Freeᵒ' n o  ⊨ envᴳ M E ⤇ᴱ λ (_ : ⊤₀) →
      envᴳ (upd˙ o ň M) E , ⊤ᵒ₀
  ↦ᴸᵒ'-free' lenvs≡n =  ◎⟨⟩-∗ᵒ⇒∙ ›
    ↝-◎⟨⟩-⤇ᴱ {bⁱ˙ = λ _ → εᴹᵉᵐ} (↦ᴸʳ-free lenvs≡n) › ⤇ᴱ-respᴱʳ upd˙-mem-envᴳ ›
    ⤇ᴱ-mono _
