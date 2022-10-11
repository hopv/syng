--------------------------------------------------------------------------------
-- Proof rules on the memory
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Logic.Mem where

open import Base.Func using (_$_; _▷_)
open import Base.Eq using (_≡_; _≢_; refl)
open import Base.Size using (Size; !)
open import Base.Bool using (tt; ff)
open import Base.Prod using (_,_; -,_)
open import Base.Sum using (ĩ₁_)
open import Base.Nat using (ℕ)
open import Base.List using (List; len; rep)
open import Base.RatPos using (ℚ⁺)
open import Base.Sety using (Setʸ)
open import Syho.Lang.Expr using (Addr; Type; ◸ʸ_; ∇_; V⇒E; TyVal; ⊤-)
open import Syho.Lang.Ktxred using (🞰ᴿ_; _←ᴿ_; fauᴿ; casᴿ; allocᴿ; freeᴿ; Ktx;
  _ᴷ◁_)
open import Syho.Logic.Prop using (WpKind; par; tot; Prop∞; _∗_; _↦⟨_⟩_; _↦_;
  _↦ᴸ_; Free)
open import Syho.Logic.Core using (_»_; ∗-assocˡ; ∗-assocʳ; ⊤∗-intro; ∗-elimʳ;
  ∃∗-elim)
open import Syho.Logic.Hor using (_⊢[_]⁺⟨_⟩[_]_; _⊢[<ᴾ_]⟨_⟩[_]_; ahor-frameʳ;
  ahor-hor; hor<ᴾ-map)

-- Import and re-export
open import Syho.Logic.Judg public using (↦⟨⟩-merge; ↦⟨⟩-split; ↦⟨⟩-≤1;
  ↦⟨⟩-agree; ahor-🞰; ahor-←; ahor-fau; ahor-cas-tt; ahor-cas-ff; ahor-alloc;
  ahor-free)

private variable
  ι :  Size
  T U :  Type
  Xʸ :  Setʸ
  X :  Set₀
  κ :  WpKind
  K :  Ktx T U
  n :  ℕ
  p :  ℚ⁺
  θ :  Addr
  v x y z :  X
  f :  X → X
  ᵗu :  TyVal
  ᵗvs :  List TyVal
  P :  Prop∞
  Q˙ :  X → Prop∞

abstract

  ------------------------------------------------------------------------------
  -- On the memory

  -->  ↦⟨⟩-merge :  θ ↦⟨ p ⟩ ᵗv  ∗  θ ↦⟨ q ⟩ ᵗv  ⊢[ ι ]  θ ↦⟨ p +ᴿ⁺ q ⟩ ᵗv

  -->  ↦⟨⟩-split :  θ ↦⟨ p +ᴿ⁺ q ⟩ ᵗv  ⊢[ ι ]  θ ↦⟨ p ⟩ ᵗv  ∗  θ ↦⟨ q ⟩ ᵗv

  -->  ↦⟨⟩-≤1 :  θ ↦⟨ p ⟩ ᵗv  ⊢[ ι ]  ⌜ p ≤1ᴿ⁺ ⌝

  -->  ↦⟨⟩-agree :  θ ↦⟨ p ⟩ ᵗu  ∗  θ ↦⟨ q ⟩ ᵗv  ⊢[ ι ]  ⌜ ᵗu ≡ ᵗv ⌝

  -- Memory read

  -->  ahor-🞰 :  θ ↦⟨ p ⟩ (T , v)  ⊢[ ι ][ i ]ᵃ⟨ 🞰ᴿ_ {T} θ ⟩ λ u →
  -->              ⌜ u ≡ v ⌝∧  θ ↦⟨ p ⟩ (T , v)

  hor-🞰 :  θ ↦⟨ p ⟩ (T , v)  ∗  P  ⊢[<ᴾ ι ]⟨ K ᴷ◁ V⇒E v ⟩[ κ ]  Q˙  →
           θ ↦⟨ p ⟩ (T , v)  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , 🞰ᴿ_ {T} θ) ⟩[ κ ]  Q˙
  hor-🞰 θ↦v∗P⊢⟨Kv⟩Q =  ahor-hor (ahor-frameʳ $ ahor-🞰 {i = 0}) λ _ →
    hor<ᴾ-map (λ big → ∃∗-elim λ{ refl → big }) θ↦v∗P⊢⟨Kv⟩Q

  -- Memory write

  -->  ahor-← :  θ ↦ ᵗu  ⊢[ ι ][ i ]ᵃ⟨ _←ᴿ_ {T} θ v ⟩ λ _ →  θ ↦ (T , v)

  hor-← :  θ ↦ (T , v)  ∗  P  ⊢[<ᴾ ι ]⟨ K ᴷ◁ ∇ _ ⟩[ κ ]  Q˙  →
           θ ↦ ᵗu  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , _←ᴿ_ {T} θ v) ⟩[ κ ]  Q˙
  hor-← θ↦v∗P⊢⟨K⟩Q =  ahor-hor (ahor-frameʳ $ ahor-← {i = 0}) λ _ → θ↦v∗P⊢⟨K⟩Q

  -- Fetch and update

  -->  ahor-fau :  θ ↦ (◸ʸ Xʸ , x)  ⊢[ ι ][ i ]ᵃ⟨ fauᴿ f θ ⟩ λᵛ y ,
  -->                ⌜ y ≡ x ⌝∧  θ ↦ (-, f x)

  hor-fau :  θ ↦ (◸ʸ Xʸ , f x)  ∗  P  ⊢[<ᴾ ι ]⟨ K ᴷ◁ ∇ x ⟩[ κ ]  Q˙  →
             θ ↦ (-, x)  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , fauᴿ f θ) ⟩[ κ ]  Q˙
  hor-fau θ↦fx∗P⊢⟨Kx⟩Q =  ahor-hor (ahor-frameʳ $ ahor-fau {i = 0}) λ _ →
    hor<ᴾ-map (λ big → ∃∗-elim λ{ refl → big }) θ↦fx∗P⊢⟨Kx⟩Q

  -- Compare and swap, the success and failure cases

  -->  ahor-cas-tt :  θ ↦ (◸ʸ Xʸ , x)  ⊢[ ι ][ i ]ᵃ⟨ casᴿ θ x y ⟩ λᵛ b ,
  -->                   ⌜ b ≡ tt ⌝∧  θ ↦ (-, y)

  hor-cas-tt :  θ ↦ (◸ʸ Xʸ , y)  ∗  P  ⊢[<ᴾ ι ]⟨ K ᴷ◁ ∇ tt ⟩[ κ ]  Q˙  →
                θ ↦ (-, x)  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , casᴿ θ x y) ⟩[ κ ]  Q˙
  hor-cas-tt θ↦x∗P⊢⟨Ktt⟩Q =  ahor-hor (ahor-frameʳ $ ahor-cas-tt {i = 0}) λ _ →
    hor<ᴾ-map (λ big → ∃∗-elim λ{ refl → big }) θ↦x∗P⊢⟨Ktt⟩Q

  -->  ahor-cas-ff :  z ≢ x  →
  -->    θ ↦⟨ p ⟩ (◸ʸ Xʸ , z)  ⊢[ ι ][ i ]ᵃ⟨ casᴿ θ x y ⟩ λᵛ b ,
  -->      ⌜ b ≡ ff ⌝∧  θ ↦⟨ p ⟩ (-, z)

  hor-cas-ff :  z ≢ x  →
    θ ↦⟨ p ⟩ (◸ʸ Xʸ , z)  ∗  P  ⊢[<ᴾ ι ]⟨ K ᴷ◁ ∇ ff ⟩[ κ ]  Q˙  →
    θ ↦⟨ p ⟩ (-, z)  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , casᴿ θ x y) ⟩[ κ ]  Q˙
  hor-cas-ff z≢x θ↦z∗P⊢⟨Kff⟩Q =  ahor-hor
    (ahor-frameʳ $ ahor-cas-ff {i = 0} z≢x) λ _ →
    hor<ᴾ-map (λ big → ∃∗-elim λ{ refl → big }) θ↦z∗P⊢⟨Kff⟩Q

  -- Memory allocation

  -->  ahor-alloc :  ⊤'  ⊢[ ι ][ i ]ᵃ⟨ allocᴿ n ⟩ λᵛ θ ,
  -->                  θ ↦ᴸ rep n ⊤-  ∗  Free n θ

  hor-alloc :
    (∀ θ →  θ ↦ᴸ rep n ⊤-  ∗  Free n θ  ∗  P  ⊢[<ᴾ ι ]⟨ K ᴷ◁ ∇ θ ⟩[ κ ]  Q˙)  →
    P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , allocᴿ n) ⟩[ κ ]  Q˙
  hor-alloc θ↦∗Freeθ∗P⊢⟨Kθ⟩Q =  ahor-hor
    (⊤∗-intro » ahor-frameʳ $ ahor-alloc {i = 0}) λ θ →
    hor<ᴾ-map (∗-assocˡ »_) $ θ↦∗Freeθ∗P⊢⟨Kθ⟩Q θ

  -- Memory freeing

  -->  ahor-free :  len ᵗvs ≡ n  →
  -->    θ ↦ᴸ ᵗvs  ∗  Free n θ  ⊢[ ι ][ i ]ᵃ⟨ freeᴿ θ ⟩ λ _ →  ⊤'

  hor-free :  len ᵗvs ≡ n  →   P  ⊢[<ᴾ ι ]⟨ K ᴷ◁ ∇ _ ⟩[ κ ]  Q˙  →
    θ ↦ᴸ ᵗvs  ∗  Free n θ  ∗  P  ⊢[ ι ]⁺⟨ ĩ₁ (-, K , freeᴿ θ) ⟩[ κ ]  Q˙
  hor-free lenvs≡n P⊢⟨K⟩Q =  ∗-assocʳ »
    ahor-hor (ahor-frameʳ $ ahor-free {i = 0} lenvs≡n) λ _ →
    hor<ᴾ-map (∗-elimʳ »_) P⊢⟨K⟩Q
