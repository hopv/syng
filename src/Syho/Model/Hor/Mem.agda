--------------------------------------------------------------------------------
-- Semantic super update and weakest precondition lemmas for the memory
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Hor.Mem where

open import Base.Func using (_$_; _▷_; _›_)
open import Base.Eq using (_≡_; refl; ◠_; _◇_)
open import Base.Dec using (upd˙)
open import Base.Option using (š_; ň; š-inj)
open import Base.Prod using (∑-syntax; π₁; _,_; -,_; ≡∑⇒π₁≡)
open import Base.Nat using (ℕ)
open import Base.List using (List; len; rep)
open import Base.RatPos using (ℚ⁺)
open import Base.Sety using (Setʸ)
open import Syho.Lang.Expr using (Addr; Type; ◸ʸ_; ∇_; Val; TyVal; ⊤-)
open import Syho.Lang.Ktxred using (🞰ᴿ_; _←ᴿ_; fauᴿ; casᴿ; allocᴿ; freeᴿ)
open import Syho.Lang.Reduce using (Mem; _‼ᴹ_; updᴹ; 🞰⇒; ←⇒; fau⇒; cas⇒-tt;
  cas⇒-ff; alloc⇒; free⇒; ✓ᴹ-∑ň)
open import Syho.Model.ERA.Glob using (upd˙-mem-envᴳ)
open import Syho.Model.ERA.Mem using (εᴹᵉᵐ; ↦⟨⟩ʳ-read; ↦ʳ-write; ↦ᴸʳ-alloc;
  freeʳ-š; ↦ᴸʳ-free)
open import Syho.Model.Prop.Base using (Propᵒ; _⊨_; ⊨_; ⌜_⌝ᵒ×_; ⊤ᵒ₀; _∗ᵒ_;
  ∗ᵒ-mono; ∗ᵒ-monoˡ; ∗ᵒ-monoʳ; ∗ᵒ-comm; ∗ᵒ∃ᵒ-out; ⤇ᴱ-mono; ⤇ᴱ-respᴱʳ; ⤇ᴱ-param;
  ◎⟨⟩-∗ᵒ⇒∙; ◎⟨⟩-∙⇒∗ᵒ; ↝-◎⟨⟩-⤇ᴱ; ε↝-◎⟨⟩-⤇ᴱ)
open import Syho.Model.Prop.Mem using (_↦⟨_⟩ᵒ_; _↦ᵒ_; Freeᵒ'; Freeᵒ; _↦ᴸᵒ_;
  _↦ᴸᵒ'_; ↦ᴸᵒ⇒↦ᴸᵒ'; ↦ᴸᵒ'⇒↦ᴸᵒ)
open import Syho.Model.Supd.Interp using (⟨_⟩⇛ᵒ⟨_⟩_; ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᵒ; ⊨⤇ᴱᴹᵉᵐ⇒⊨⇛ᵒ;
  ⇛ᵒ-mono; ⇛ᵒ-intro; ⇛ᵒ-intro-✓ᴹ; ⇛ᵒ-eatˡ)
open import Syho.Model.Hor.Wp using (ᵃ⟨_⟩ᵒ_)

private variable
  X :  Set₀
  Xʸ :  Setʸ
  T :  Type
  M :  Mem
  θ :  Addr
  p :  ℚ⁺
  o n :  ℕ
  ᵗu ᵗv :  TyVal
  ᵗvs :  List TyVal
  v x :  X
  f :  X → X

--------------------------------------------------------------------------------
-- Semantic super update for the memory

abstract

  -- Read using ↦⟨⟩ᵒ

  ↦⟨⟩ᵒ-read :  θ ↦⟨ p ⟩ᵒ ᵗv  ⊨ ⟨ M ⟩⇛ᵒ⟨ M ⟩
                 ⌜ M ‼ᴹ θ ≡ š ᵗv ⌝ᵒ×  θ ↦⟨ p ⟩ᵒ ᵗv
  ↦⟨⟩ᵒ-read =  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᵒ $ ↝-◎⟨⟩-⤇ᴱ ↦⟨⟩ʳ-read › ⤇ᴱ-respᴱʳ upd˙-mem-envᴳ ›
    ⤇ᴱ-mono (λ M‼θ≡v →  M‼θ≡v ,_) › ⤇ᴱ-param

  -- Write using ↦ᵒ

  ↦ᵒ-write :  θ ↦ᵒ ᵗu  ⊨ ⟨ M ⟩⇛ᵒ⟨ updᴹ θ ᵗv M ⟩  θ ↦ᵒ ᵗv
  ↦ᵒ-write =  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᵒ $ ↝-◎⟨⟩-⤇ᴱ ↦ʳ-write › ⤇ᴱ-respᴱʳ upd˙-mem-envᴳ

  -- Allocate to get ↦ᴸᵒ' and Freeᵒ'

  ↦ᴸᵒ'-alloc :  M o ≡ ň  →
    ⊨ ⟨ M ⟩⇛ᵒ⟨ upd˙ o (š rep n ⊤-) M ⟩  o ↦ᴸᵒ' rep n ⊤-  ∗ᵒ  Freeᵒ' n o
  ↦ᴸᵒ'-alloc Mo≡ň =  ⊨⤇ᴱᴹᵉᵐ⇒⊨⇛ᵒ (ε↝-◎⟨⟩-⤇ᴱ (↦ᴸʳ-alloc Mo≡ň) ▷
    ⤇ᴱ-respᴱʳ upd˙-mem-envᴳ ▷ ⤇ᴱ-mono λ _ → ◎⟨⟩-∙⇒∗ᵒ)

  -- Bounds check using Freeᵒ'

  Freeᵒ'-š :  Freeᵒ' n o  ⊨ ⟨ M ⟩⇛ᵒ⟨ M ⟩  ⌜ ∑ ᵗvs , M o ≡ š ᵗvs ⌝ᵒ×  Freeᵒ' n o
  Freeᵒ'-š =  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᵒ $ ↝-◎⟨⟩-⤇ᴱ freeʳ-š › ⤇ᴱ-respᴱʳ upd˙-mem-envᴳ ›
    ⤇ᴱ-mono (λ Mo≡vs →  Mo≡vs ,_) › ⤇ᴱ-param

  -- Free using ↦ᴸᵒ' and Freeᵒ'

  ↦ᴸᵒ'-free :  len ᵗvs ≡ n  →
    o ↦ᴸᵒ' ᵗvs  ∗ᵒ  Freeᵒ' n o  ⊨ ⟨ M ⟩⇛ᵒ⟨ upd˙ o ň M ⟩  ⊤ᵒ₀
  ↦ᴸᵒ'-free lenvs≡n =  ?⊨⤇ᴱᴹᵉᵐ⇒?⊨⇛ᵒ $ ◎⟨⟩-∗ᵒ⇒∙ ›
    ↝-◎⟨⟩-⤇ᴱ {bⁱ˙ = λ _ → εᴹᵉᵐ} (↦ᴸʳ-free lenvs≡n) › ⤇ᴱ-respᴱʳ upd˙-mem-envᴳ ›
    ⤇ᴱ-mono _

--------------------------------------------------------------------------------
-- Atomic weakest precondition lemmas for the memory

abstract

  -- 🞰 and ᵃ⟨⟩ᵒ

  ᵃ⟨⟩ᵒ-🞰 :  θ ↦⟨ p ⟩ᵒ (T , v)  ⊨ ᵃ⟨ 🞰ᴿ_ {T} θ ⟩ᵒ λ u →
              ⌜ u ≡ v ⌝ᵒ×  θ ↦⟨ p ⟩ᵒ (T , v)
  ᵃ⟨⟩ᵒ-🞰 θ↦v _ =  ↦⟨⟩ᵒ-read θ↦v ▷ ⇛ᵒ-mono λ (M‼θ≡v , θ↦v) → (-, 🞰⇒ M‼θ≡v) ,
    λ{ _ _ _ (🞰⇒ M‼θ≡u) → -, (refl , refl) ,
    ⇛ᵒ-intro (≡∑⇒π₁≡ $ š-inj $ ◠ M‼θ≡u ◇ M‼θ≡v , θ↦v) }

  -- ← and ᵃ⟨⟩ᵒ

  ᵃ⟨⟩ᵒ-← :  θ ↦ᵒ ᵗu  ⊨ ᵃ⟨ _←ᴿ_ {T} θ v ⟩ᵒ λ _ →  θ ↦ᵒ (T , v)
  ᵃ⟨⟩ᵒ-← θ↦ _ =  ↦⟨⟩ᵒ-read θ↦ ▷ ⇛ᵒ-mono λ (M‼θ≡ , θ↦) → (-, ←⇒ (-, M‼θ≡)) ,
    λ{ _ _ _ (←⇒ _) → -, (refl , refl) , ↦ᵒ-write θ↦ }

  -- fau and ᵃ⟨⟩ᵒ

  ᵃ⟨⟩ᵒ-fau :  θ ↦ᵒ (◸ʸ Xʸ , x)  ⊨ ᵃ⟨ fauᴿ f θ ⟩ᵒ λ y →
                ⌜ y ≡ x ⌝ᵒ×  θ ↦ᵒ (-, f x)
  ᵃ⟨⟩ᵒ-fau θ↦x _ =  ↦⟨⟩ᵒ-read θ↦x ▷ ⇛ᵒ-mono λ (M‼θ≡x , θ↦x) → (-, fau⇒ M‼θ≡x) ,
    λ{ _ _ _ (fau⇒ M‼θ≡y) → -, (refl , refl) , ↦ᵒ-write θ↦x ▷ ⇛ᵒ-mono λ θ↦fx →
    (≡∑⇒π₁≡ $ š-inj $ ◠ M‼θ≡y ◇ M‼θ≡x) ▷ λ{ refl → refl , θ↦fx }}

  -- alloc and ᵃ⟨⟩ᵒ

  ᵃ⟨⟩ᵒ-alloc :  ⊨ ᵃ⟨ allocᴿ n ⟩ᵒ λ θ →  θ ↦ᴸᵒ rep n ⊤-  ∗ᵒ  Freeᵒ n θ
  ᵃ⟨⟩ᵒ-alloc {n} _ =  ⇛ᵒ-intro-✓ᴹ {Pᵒ = ⊤ᵒ₀} _  ▷ ⇛ᵒ-mono λ (✓M , -) →
    (-, alloc⇒ _ $ ✓ᴹ-∑ň ✓M .π₁) , λ{ _ _ _ (alloc⇒ _ Mo≡ň) → -, (refl , refl) ,
    ↦ᴸᵒ'-alloc Mo≡ň ▷
    ⇛ᵒ-mono (∗ᵒ-mono (↦ᴸᵒ'⇒↦ᴸᵒ {ᵗvs = rep n _}) λ Free' → -, refl , Free') }

  -- free and ᵃ⟨⟩ᵒ

  ᵃ⟨⟩ᵒ-free :  len ᵗvs ≡ n  →
    θ ↦ᴸᵒ ᵗvs  ∗ᵒ  Freeᵒ n θ  ⊨ ᵃ⟨ freeᴿ θ ⟩ᵒ λ _ →  ⊤ᵒ₀
  ᵃ⟨⟩ᵒ-free {ᵗvs} lenvs≡n θ↦vs∗Free _ =  θ↦vs∗Free ▷ ∗ᵒ∃ᵒ-out ▷ λ (-, big) →
    ∗ᵒ∃ᵒ-out big ▷ λ{ (refl , big) → big ▷ ∗ᵒ-monoʳ Freeᵒ'-š ▷ ⇛ᵒ-eatˡ ▷
    ⇛ᵒ-mono (∗ᵒ∃ᵒ-out › λ (Mo≡š , big) → (-, free⇒ Mo≡š) , λ{ _ _ _ (free⇒ _) →
    -, (refl , refl) , big ▷ ∗ᵒ-monoˡ (↦ᴸᵒ⇒↦ᴸᵒ' {ᵗvs = ᵗvs}) ▷
    ↦ᴸᵒ'-free lenvs≡n }) }
