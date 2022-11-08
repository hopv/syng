--------------------------------------------------------------------------------
-- Semantic fancy update and weakest precondition lemmas for the heap
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Symp.Model.Hor.Heap where

open import Base.Func using (_$_; _▷_; _›_)
open import Base.Few using (absurd)
open import Base.Eq using (_≡_; _≢_; refl; ◠_; _◇_)
open import Base.Dec using (upd˙)
open import Base.Bool using (tt; ff)
open import Base.Option using (š_; ň; š-inj)
open import Base.Prod using (∑-syntax; π₁; _,_; -,_; ≡∑⇒π₁≡)
open import Base.Nat using (ℕ)
open import Base.List using (List; len; rep)
open import Base.Ratp using (ℚ⁺)
open import Base.Sety using (Setʸ)
open import Symp.Lang.Expr using (Addr; Type; ◸ʸ_; ∇_; Val; TyVal; ⊤-; Heap;
  _‼ᴴ_; updᴴ; ✓ᴴ-∑ň)
open import Symp.Lang.Ktxred using (🞰ᴿ_; _←ᴿ_; fauᴿ; casᴿ; allocᴿ; freeᴿ)
open import Symp.Lang.Reduce using (🞰⇒; ←⇒; fau⇒; cas⇒-tt; cas⇒-ff; alloc⇒;
  free⇒)
open import Symp.Model.Prop.Base using (SPropᵒ; _⊨_; ⊨_; ⌜_⌝ᵒ×_; ⊤ᵒ₀; _∗ᵒ_;
  ∗ᵒ-mono; ∗ᵒ-monoˡ; ∗ᵒ-monoʳ; ∗ᵒ-comm; ∗ᵒ∃ᵒ-out)
open import Symp.Model.Prop.Heap using (_↦⟨_⟩ᵒ_; _↦ᵒ_; Freeᵒ'; Freeᵒ; _↦ᴸᵒ_;
  _↦ᴸᵒ'_; ↦ᴸᵒ⇒↦ᴸᵒ'; ↦ᴸᵒ'⇒↦ᴸᵒ; ↦⟨⟩ᵒ-read'; ↦ᵒ-write'; ↦ᴸᵒ'-alloc'; Freeᵒ'-š';
  ↦ᴸᵒ'-free')
open import Symp.Model.Fupd.Interp using (⟨_⟩⇛ˢ⟨_⟩_; ?⊨⤇ᴱᴴᵉᵃᵖ⇒?⊨⇛ˢ; ⊨⤇ᴱᴴᵉᵃᵖ⇒⊨⇛ˢ;
  ⇛ˢ-mono; ⇛ˢ-intro; ⇛ˢ-intro-✓ᴴ; ⇛ˢ-eatˡ)
open import Symp.Model.Hor.Wp using (ᵃ⟨_⟩ᵒ)

private variable
  X :  Set₀
  Xʸ :  Setʸ
  T :  Type
  H :  Heap
  θ :  Addr
  p :  ℚ⁺
  o n :  ℕ
  ᵗu ᵗv :  TyVal
  ᵗvs :  List TyVal
  v x y z :  X
  f :  X → X

--------------------------------------------------------------------------------
-- Semantic fancy update for the heap

abstract

  -- Read using ↦⟨⟩ᵒ

  ↦⟨⟩ᵒ-read :  θ ↦⟨ p ⟩ᵒ ᵗv  ⊨ ⟨ H ⟩⇛ˢ⟨ H ⟩
                 ⌜ H ‼ᴴ θ ≡ š ᵗv ⌝ᵒ×  θ ↦⟨ p ⟩ᵒ ᵗv
  ↦⟨⟩ᵒ-read =  ?⊨⤇ᴱᴴᵉᵃᵖ⇒?⊨⇛ˢ ↦⟨⟩ᵒ-read'

  -- Write using ↦ᵒ

  ↦ᵒ-write :  θ ↦ᵒ ᵗu  ⊨ ⟨ H ⟩⇛ˢ⟨ updᴴ θ ᵗv H ⟩  θ ↦ᵒ ᵗv
  ↦ᵒ-write {ᵗu = ᵗu} =  ?⊨⤇ᴱᴴᵉᵃᵖ⇒?⊨⇛ˢ $ ↦ᵒ-write' {ᵗu = ᵗu}

  -- Allocate to get ↦ᴸᵒ' and Freeᵒ'

  ↦ᴸᵒ'-alloc :  H o ≡ ň  →
    ⊨ ⟨ H ⟩⇛ˢ⟨ upd˙ o (š rep n ⊤-) H ⟩  o ↦ᴸᵒ' rep n ⊤-  ∗ᵒ  Freeᵒ' n o
  ↦ᴸᵒ'-alloc Ho≡ň =  ⊨⤇ᴱᴴᵉᵃᵖ⇒⊨⇛ˢ $ ↦ᴸᵒ'-alloc' Ho≡ň

  -- Bounds check using Freeᵒ'

  Freeᵒ'-š :  Freeᵒ' n o  ⊨ ⟨ H ⟩⇛ˢ⟨ H ⟩  ⌜ ∑ ᵗvs , H o ≡ š ᵗvs ⌝ᵒ×  Freeᵒ' n o
  Freeᵒ'-š =  ?⊨⤇ᴱᴴᵉᵃᵖ⇒?⊨⇛ˢ Freeᵒ'-š'

  -- Free using ↦ᴸᵒ' and Freeᵒ'

  ↦ᴸᵒ'-free :  len ᵗvs ≡ n  →
    o ↦ᴸᵒ' ᵗvs  ∗ᵒ  Freeᵒ' n o  ⊨ ⟨ H ⟩⇛ˢ⟨ upd˙ o ň H ⟩  ⊤ᵒ₀
  ↦ᴸᵒ'-free lenvs≡n =  ?⊨⤇ᴱᴴᵉᵃᵖ⇒?⊨⇛ˢ $ ↦ᴸᵒ'-free' lenvs≡n

--------------------------------------------------------------------------------
-- Atomic weakest precondition lemmas for the heap

abstract

  -- For lemmas like ᵃ⟨⟩ᵒ-🞰, through ≡∑⇒π₁≡, we implicitly enjoy the property
  -- that Type satisfies the UIP (which comes from Type's decidable equality)

  -- 🞰 by ᵃ⟨⟩ᵒ

  ᵃ⟨⟩ᵒ-🞰 :  θ ↦⟨ p ⟩ᵒ (T , v)  ⊨ ᵃ⟨ 🞰ᴿ_ {T} θ ⟩ᵒ λ u →
              ⌜ u ≡ v ⌝ᵒ×  θ ↦⟨ p ⟩ᵒ (T , v)
  ᵃ⟨⟩ᵒ-🞰 θ↦v _ =  ↦⟨⟩ᵒ-read θ↦v ▷ ⇛ˢ-mono λ (H‼θ≡v , θ↦v) → (-, -, 🞰⇒ H‼θ≡v) ,
    λ{ _ _ _ (-, 🞰⇒ H‼θ≡u) → -, (refl , refl) ,
      ⇛ˢ-intro (≡∑⇒π₁≡ $ š-inj $ ◠ H‼θ≡u ◇ H‼θ≡v , θ↦v) }

  -- ← by ᵃ⟨⟩ᵒ

  ᵃ⟨⟩ᵒ-← :  θ ↦ᵒ ᵗu  ⊨ ᵃ⟨ _←ᴿ_ {T} θ v ⟩ᵒ λ _ →  θ ↦ᵒ (T , v)
  ᵃ⟨⟩ᵒ-← θ↦ _ =  ↦⟨⟩ᵒ-read θ↦ ▷ ⇛ˢ-mono λ (H‼θ≡ , θ↦) → (-, -, ←⇒ H‼θ≡) ,
    λ{ _ _ _ (-, ←⇒ _) → -, (refl , refl) , ↦ᵒ-write θ↦ }

  -- fau by ᵃ⟨⟩ᵒ

  ᵃ⟨⟩ᵒ-fau :  θ ↦ᵒ (◸ʸ Xʸ , x)  ⊨ ᵃ⟨ fauᴿ f θ ⟩ᵒ λ y →
                ⌜ y ≡ x ⌝ᵒ×  θ ↦ᵒ (-, f x)
  ᵃ⟨⟩ᵒ-fau θ↦x _ =  ↦⟨⟩ᵒ-read θ↦x ▷ ⇛ˢ-mono λ (H‼θ≡x , θ↦x) →
    (-, -, fau⇒ H‼θ≡x) ,
    λ{ _ _ _ (-, fau⇒ H‼θ≡y) → -, (refl , refl) , ↦ᵒ-write θ↦x ▷ ⇛ˢ-mono
      λ θ↦fx → (≡∑⇒π₁≡ $ š-inj $ ◠ H‼θ≡y ◇ H‼θ≡x) ▷ λ{ refl → refl , θ↦fx } }

  -- cas by ᵃ⟨⟩ᵒ

  ᵃ⟨⟩ᵒ-cas-tt :  θ ↦ᵒ (◸ʸ Xʸ , x)  ⊨ ᵃ⟨ casᴿ θ x y ⟩ᵒ λ b →
                   ⌜ b ≡ tt ⌝ᵒ×  θ ↦ᵒ (-, y)
  ᵃ⟨⟩ᵒ-cas-tt θ↦x _ =  ↦⟨⟩ᵒ-read θ↦x ▷ ⇛ˢ-mono λ (H‼θ≡x , θ↦x) →
    (-, -, cas⇒-tt H‼θ≡x) , λ _ _ _ →
    λ{ (-, cas⇒-ff H‼θ≡z z≢x) → absurd $ z≢x $ ≡∑⇒π₁≡ $ š-inj $ ◠ H‼θ≡z ◇ H‼θ≡x;
       (-, cas⇒-tt _) → -, (refl , refl) , ↦ᵒ-write θ↦x ▷ ⇛ˢ-mono (refl ,_) }

  ᵃ⟨⟩ᵒ-cas-ff :  z ≢ x  →
    θ ↦⟨ p ⟩ᵒ (◸ʸ Xʸ , z)  ⊨ ᵃ⟨ casᴿ θ x y ⟩ᵒ λ b →
      ⌜ b ≡ ff ⌝ᵒ×  θ ↦⟨ p ⟩ᵒ (-, z)
  ᵃ⟨⟩ᵒ-cas-ff z≢x θ↦z _ =  ↦⟨⟩ᵒ-read θ↦z ▷ ⇛ˢ-mono λ (H‼θ≡z , θ↦z) →
    (-, -, cas⇒-ff H‼θ≡z z≢x) , λ _ _ _ →
    λ{ (-, cas⇒-tt H‼θ≡x) → absurd $ z≢x $ ≡∑⇒π₁≡ $ š-inj $ ◠ H‼θ≡z ◇ H‼θ≡x;
       (-, cas⇒-ff _ _) → -, (refl , refl) , ⇛ˢ-intro (refl , θ↦z) }

  -- alloc by ᵃ⟨⟩ᵒ

  ᵃ⟨⟩ᵒ-alloc :  ⊨ ᵃ⟨ allocᴿ n ⟩ᵒ λ θ →  θ ↦ᴸᵒ rep n ⊤-  ∗ᵒ  Freeᵒ n θ
  ᵃ⟨⟩ᵒ-alloc {n} _ =  ⇛ˢ-intro-✓ᴴ {Pᵒ = ⊤ᵒ₀} _  ▷ ⇛ˢ-mono λ (✓H , -) →
    (-, -, alloc⇒ _ $ ✓ᴴ-∑ň ✓H .π₁) ,
    λ{ _ _ _ (-, alloc⇒ _ Ho≡ň) → -, (refl , refl) , ↦ᴸᵒ'-alloc Ho≡ň ▷
      ⇛ˢ-mono (∗ᵒ-mono (↦ᴸᵒ'⇒↦ᴸᵒ {ᵗvs = rep n _}) λ Free' → -, refl , Free') }

  -- free by ᵃ⟨⟩ᵒ

  ᵃ⟨⟩ᵒ-free :  len ᵗvs ≡ n  →
    θ ↦ᴸᵒ ᵗvs  ∗ᵒ  Freeᵒ n θ  ⊨ ᵃ⟨ freeᴿ θ ⟩ᵒ λ _ →  ⊤ᵒ₀
  ᵃ⟨⟩ᵒ-free {ᵗvs} lenvs≡n θ↦vs∗Free _ =  θ↦vs∗Free ▷ ∗ᵒ∃ᵒ-out ▷ λ (-, big) →
    ∗ᵒ∃ᵒ-out big ▷ λ{ (refl , big) → big ▷ ∗ᵒ-monoʳ Freeᵒ'-š ▷ ⇛ˢ-eatˡ ▷
    ⇛ˢ-mono (∗ᵒ∃ᵒ-out › λ (Ho≡š , big) → (-, -, free⇒ Ho≡š) ,
    λ{ _ _ _ (-, free⇒ _) → -, (refl , refl) ,
      big ▷ ∗ᵒ-monoˡ (↦ᴸᵒ⇒↦ᴸᵒ' {ᵗvs = ᵗvs}) ▷ ↦ᴸᵒ'-free lenvs≡n }) }
