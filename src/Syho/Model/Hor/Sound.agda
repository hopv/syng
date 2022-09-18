--------------------------------------------------------------------------------
-- Prove the semantic soundness of the partial and total Hoare triples
--------------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Syho.Model.Hor.Sound where

open import Base.Size using (Size; ∞; !)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Few using (absurd)
open import Base.Prod using (_,_; -,_; ∑-case)
open import Base.Nat using (ℕ)
open import Base.List using (List; []; _∷_; rep)
open import Syho.Lang.Expr using (Addr; _ₒ_; Type; Val; TyVal)
open import Syho.Lang.Ktxred using (Val/Ktxred)
open import Syho.Logic.Prop using (Prop'; _↦_; [∗∈ⁱ⟨⟩]-syntax)
open import Syho.Logic.Core using (_»_; ∃₁-elim)
open import Syho.Logic.Ind using (↪⟨⟩ᴾ-use; ↪⟨⟩ᵀ-use)
open import Syho.Logic.Hor using (_⊢[_]⁺⟨_⟩ᴾ_; _⊢[_]⁺⟨_⟩ᵀ[_]_; hor-ᵀ⇒ᴾ; horᵀ-ṡ;
  _ᵘ»ʰ_; _ʰ»ᵘ_; hor-frameˡ; hor-bind; hor-valᵘ; hor-nd; horᴾ-▶; horᵀ-▶; hor-◁;
  hor-⁏)
open import Syho.Logic.Mem using (hor-🞰; hor-←; hor-alloc; hor-free)
open import Syho.Model.Prop.Base using (_⊨_; ∗ᵒ-monoˡ; ∗ᵒ-monoʳ; ∗ᵒ∃ᵒ-out;
  [∗ᵒ∈ⁱ⟨⟩]-syntax)
open import Syho.Model.Prop.Mem using (_↦ᵒ_)
open import Syho.Model.Prop.Interp using (⸨_⸩)
open import Syho.Model.Prop.Sound using (⊢-sem)
open import Syho.Model.Supd.Ind using (↪⟨⟩ᴾᵒ-use; ↪⟨⟩ᵀᵒ-use)
open import Syho.Model.Supd.Interp using (⇛ᴵⁿᵈ⇒⇛ᵒ; ⇛ᵒ-mono; ⇛ᵒ-eatˡ)
open import Syho.Model.Supd.Sound using (⊢⇛-sem)
open import Syho.Model.Hor.Wp using (⁺⟨_⟩ᴾᵒ[_]_; ⁺⟨_⟩ᵀᵒ[_]_; ⁺⟨⟩ᴾᵒ-val;
  ⁺⟨⟩ᵀᵒ-val; ⁺⟨⟩ᴾᵒ-mono; ⁺⟨⟩ᵀᵒ-mono; ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ; ⇛ᵒ-⁺⟨⟩ᴾᵒ; ⇛ᵒ-⁺⟨⟩ᵀᵒ;
  ⊨✓⇒⊨-⁺⟨⟩ᴾᵒ; ⊨✓⇒⊨-⁺⟨⟩ᵀᵒ; ⁺⟨⟩ᴾᵒ-⇛ᵒ; ⁺⟨⟩ᵀᵒ-⇛ᵒ; ⁺⟨⟩ᴾᵒ-eatˡ; ⁺⟨⟩ᵀᵒ-eatˡ)
open import Syho.Model.Hor.Lang using (⟨⟩ᴾᵒ-bind; ⟨⟩ᵀᵒ-bind; ⁺⟨⟩ᴾᵒ-nd; ⁺⟨⟩ᵀᵒ-nd;
  ⁺⟨⟩ᴾᵒ-▶; ⁺⟨⟩ᵀᵒ-▶; ⁺⟨⟩ᴾᵒ-◁; ⁺⟨⟩ᵀᵒ-◁; ⁺⟨⟩ᴾᵒ-⁏; ⁺⟨⟩ᵀᵒ-⁏)
open import Syho.Model.Hor.Mem using (⁺⟨⟩ᴾᵒ-🞰; ⁺⟨⟩ᵀᵒ-🞰; ⁺⟨⟩ᴾᵒ-←; ⁺⟨⟩ᵀᵒ-←;
  ⁺⟨⟩ᴾᵒ-alloc; ⁺⟨⟩ᵀᵒ-alloc; ⁺⟨⟩ᴾᵒ-free; ⁺⟨⟩ᵀᵒ-free)

private variable
  ι :  Size
  T :  Type
  P :  Prop' ∞
  Q˙ :  Val T →  Prop' ∞
  vk :  Val/Ktxred T
  i k :  ℕ
  θ :  Addr
  ᵗvs :  List TyVal

--------------------------------------------------------------------------------
-- Lemmas on ↦ᴸ

abstract

  -- ⸨ θ ↦ᴸ ᵗvs ⸩ agrees with θ ↦ᴸᵒ ᵗvs
  -- For induction we use the unfolded versions with ∈ⁱ⟨ k ⟩

  ↦ᴸ⇒↦ᴸᵒ :  ⸨ [∗ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] θ ₒ i ↦ ᵗv ⸩  ⊨
            [∗ᵒ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] θ ₒ i ↦ᵒ ᵗv
  ↦ᴸ⇒↦ᴸᵒ {ᵗvs = []} =  _
  ↦ᴸ⇒↦ᴸᵒ {ᵗvs = _ ∷ ᵗvs'} =  ∗ᵒ-monoʳ $ ↦ᴸ⇒↦ᴸᵒ {ᵗvs = ᵗvs'}

  ↦ᴸᵒ⇒↦ᴸ :  [∗ᵒ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] θ ₒ i ↦ᵒ ᵗv  ⊨
            ⸨ [∗ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] θ ₒ i ↦ ᵗv ⸩
  ↦ᴸᵒ⇒↦ᴸ {ᵗvs = []} _ =  absurd
  ↦ᴸᵒ⇒↦ᴸ {ᵗvs = _ ∷ ᵗvs'} =  ∗ᵒ-monoʳ $ ↦ᴸᵒ⇒↦ᴸ {ᵗvs = ᵗvs'}

--------------------------------------------------------------------------------
-- ⊢⁺⟨⟩ᵀ-sem :  Semantic soundness of the total Hoare triple

abstract

  ⊢⁺⟨⟩ᵀ-sem :
    P  ⊢[ ∞ ]⁺⟨ vk ⟩ᵀ[ i ]  Q˙  →   ⸨ P ⸩  ⊨  ⁺⟨ vk ⟩ᵀᵒ[ ∞ ]  λ v → ⸨ Q˙ v ⸩

  -- _»_ :  P ⊢[ ∞ ] Q →  Q ⊢[ ∞ ]⁺⟨ vk ⟩ᵀ[ i ] R˙ →  P ⊢[ ∞ ]⁺⟨ vk ⟩ᵀ[ i ] R˙

  ⊢⁺⟨⟩ᵀ-sem (P⊢Q » Q⊢⟨vk⟩R) =
    ⊨✓⇒⊨-⁺⟨⟩ᵀᵒ λ ✓∙ → ⊢-sem P⊢Q ✓∙ › ⊢⁺⟨⟩ᵀ-sem Q⊢⟨vk⟩R

  -- ∃₁-elim :  (∀ x →  P˙ x ⊢[ ∞ ][ i ]⇛ Q) →  ∃₁˙ P˙ ⊢[ ∞ ][ i ]⇛ Q

  ⊢⁺⟨⟩ᵀ-sem (∃₁-elim Px⊢⟨vk⟩Q) =   ∑-case λ x → ⊢⁺⟨⟩ᵀ-sem (Px⊢⟨vk⟩Q x)

  -- ↪⟨⟩ᵀ-use :  P˂ .! ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂˙)
  --               ⊢[ ∞ ]⟨ ¡ e ⟩ᵀ[ ṡ i ]  λ v → Q˂˙ v .!
  ---- The counter increment ṡ i makes the recursive call of ⊢⁺⟨⟩ᵀ-sem inductive

  ⊢⁺⟨⟩ᵀ-sem ↪⟨⟩ᵀ-use big =  ⇛ᵒ-⁺⟨⟩ᵀᵒ λ _ → big ▷
    ∗ᵒ-monoʳ (↪⟨⟩ᵀᵒ-use › ⇛ᴵⁿᵈ⇒⇛ᵒ) ▷ ⇛ᵒ-eatˡ ▷ ⇛ᵒ-mono $ ∗ᵒ∃ᵒ-out › λ (-, big) →
    ∗ᵒ∃ᵒ-out big ▷ λ (P∗R⊢⟨e⟩Q , PRa) → ⊢⁺⟨⟩ᵀ-sem P∗R⊢⟨e⟩Q PRa

  -- horᵀ-ṡ :  P  ⊢[ ∞ ]⁺⟨ vk ⟩ᵀ[ i ]  Q˙  →   P  ⊢[ ∞ ]⁺⟨ vk ⟩ᵀ[ ṡ i ]  Q˙

  ⊢⁺⟨⟩ᵀ-sem (horᵀ-ṡ P⊢⟨vk⟩Q) =  ⊢⁺⟨⟩ᵀ-sem P⊢⟨vk⟩Q

  -- _ᵘ»ʰ_ :  P  ⊢[ ∞ ][ i ]⇛  Q  →   Q  ⊢[ ∞ ]⁺⟨ vk ⟩ᵀ[ i ]  R˙  →
  --          P  ⊢[ ∞ ]⁺⟨ vk ⟩ᵀ[ i ]  R˙

  ⊢⁺⟨⟩ᵀ-sem (P⊢⇛Q ᵘ»ʰ Q⊢⟨vk⟩R) Pa =  ⇛ᵒ-⁺⟨⟩ᵀᵒ λ _ → Pa ▷ ⊢⇛-sem P⊢⇛Q ▷
    ⇛ᵒ-mono $ ⊢⁺⟨⟩ᵀ-sem Q⊢⟨vk⟩R

  -- _ʰ»ᵘ_ :  P  ⊢[ ∞ ]⁺⟨ vk ⟩ᵀ[ i ]  Q˙  →
  --          (∀ v →  Q˙ v  ⊢[ ∞ ][ i ]⇛  R˙ v)  →
  --          P  ⊢[ ∞ ]⁺⟨ vk ⟩ᵀ[ i ]  R˙

  ⊢⁺⟨⟩ᵀ-sem (P⊢⟨vk⟩Q ʰ»ᵘ Qv⊢⇛Rv) =  ⊢⁺⟨⟩ᵀ-sem P⊢⟨vk⟩Q ›
    ⁺⟨⟩ᵀᵒ-mono (λ v Qva _ → ⊢⇛-sem (Qv⊢⇛Rv v) Qva) › ⁺⟨⟩ᵀᵒ-⇛ᵒ

  -- hor-frameˡ :  P  ⊢[ ∞ ]⁺⟨ vk ⟩ᵀ[ i ]  Q˙  →
  --               R  ∗  P  ⊢[ ∞ ]⁺⟨ vk ⟩ᵀ[ i ]  λ v →  R  ∗  Q˙ v

  ⊢⁺⟨⟩ᵀ-sem (hor-frameˡ P⊢⟨vk⟩Q) =  ∗ᵒ-monoʳ (⊢⁺⟨⟩ᵀ-sem P⊢⟨vk⟩Q ) › ⁺⟨⟩ᵀᵒ-eatˡ

  -- hor-valᵘ :  P  ⊢[ ∞ ]⇛  Q˙ v  →   P  ⊢[ ∞ ]⁺⟨ ĩ₀ v ⟩ᵀ[ i ]  Q˙

  ⊢⁺⟨⟩ᵀ-sem (hor-valᵘ P⊢⇛Qv) Pa =  ⁺⟨⟩ᵀᵒ-val λ _ → Pa ▷ ⊢⇛-sem P⊢⇛Qv

  -- hor-bind :  P  ⊢[ ∞ ]⟨ e ⟩ᵀ[ i ]  Q˙  →
  --             (∀ v →  Q˙ v  ⊢[ ∞ ]⟨ K ᴷ◁ V⇒E v ⟩ᵀ[ i ]  R˙)  →
  --             P  ⊢[ ∞ ]⟨ K ᴷ◁ e ⟩ᵀ[ i ]  R˙

  ⊢⁺⟨⟩ᵀ-sem (hor-bind P⊢⟨e⟩Q Qv⊢⟨Kv⟩R) =  ⊢⁺⟨⟩ᵀ-sem P⊢⟨e⟩Q ›
    ⁺⟨⟩ᵀᵒ-mono (λ v → ⊢⁺⟨⟩ᵀ-sem (Qv⊢⟨Kv⟩R v)) › ⟨⟩ᵀᵒ-bind

  -- hor-nd :  {{Inh X}} →  (∀(x : X) →  P  ⊢[ ∞ ]⟨ K ᴷ◁ ∇ x ⟩ᵀ[ i ]  Q˙)  →
  --           P  ⊢[ ∞ ]⁺⟨ ĩ₁ (K ᴷ| ndᴿ) ⟩ᵀ[ i ]  Q˙

  ⊢⁺⟨⟩ᵀ-sem (hor-nd P⊢⟨Kx⟩Q) Pa =  ⁺⟨⟩ᵀᵒ-nd λ x → Pa ▷ ⊢⁺⟨⟩ᵀ-sem (P⊢⟨Kx⟩Q x)

  -- horᵀ-▶ :  P  ⊢[ ∞ ]⟨ K ᴷ◁ e˂ .! ⟩ᵀ[ i ]  Q˙  →
  --           P  ⊢[ ∞ ]⁺⟨ ĩ₁ (K ᴷ| ▶ᴿ e˂) ⟩ᵀ[ i ]  Q˙

  ⊢⁺⟨⟩ᵀ-sem (horᵀ-▶ P⊢⟨Ke⟩Q) =  ⊢⁺⟨⟩ᵀ-sem P⊢⟨Ke⟩Q › ⁺⟨⟩ᵀᵒ-▶

  -- hor-◁ :  P  ⊢[ ∞ ]⟨ K ᴷ◁ e˙ x ⟩ᵀ[ i ]  Q˙  →
  --          P  ⊢[ ∞ ]⁺⟨ ĩ₁ (K ᴷ| e˙ ◁ᴿ x) ⟩ᵀ[ i ]  Q˙

  ⊢⁺⟨⟩ᵀ-sem (hor-◁ P⊢⟨Kex⟩Q) =  ⊢⁺⟨⟩ᵀ-sem P⊢⟨Kex⟩Q › ⁺⟨⟩ᵀᵒ-◁

  -- hor-⁏ :  P  ⊢[ ∞ ]⟨ K ᴷ◁ e ⟩ᵀ[ i ]  Q˙  →
  --          P  ⊢[ ∞ ]⁺⟨ ĩ₁ (K ᴷ| v ⁏ᴿ e) ⟩ᵀ[ i ]  Q˙

  ⊢⁺⟨⟩ᵀ-sem (hor-⁏ P⊢⟨Ke⟩Q) =  ⊢⁺⟨⟩ᵀ-sem P⊢⟨Ke⟩Q › ⁺⟨⟩ᵀᵒ-⁏

  -- hor-🞰 :  θ ↦⟨ p ⟩ (-, v)  ∗  P  ⊢[ ∞ ]⟨ K ᴷ◁ V⇒E v ⟩ᵀ[ i ]  Q˙  →
  --          θ ↦⟨ p ⟩ (-, v)  ∗  P  ⊢[ ∞ ]⁺⟨ ĩ₁ (K ᴷ| 🞰ᴿ θ) ⟩ᵀ[ i ]  Q˙

  ⊢⁺⟨⟩ᵀ-sem (hor-🞰 θ↦v∗P⊢⟨Kv⟩Q) =  ⁺⟨⟩ᵀᵒ-🞰 $ ⊢⁺⟨⟩ᵀ-sem θ↦v∗P⊢⟨Kv⟩Q

  -- hor-← :  θ ↦ (-, v)  ∗  P  ⊢[ ∞ ]⟨ K ᴷ◁ ∇ _ ⟩ᵀ[ i ]  Q˙  →
  --          θ ↦ ᵗu  ∗  P  ⊢[ ∞ ]⁺⟨ ĩ₁ (K ᴷ| θ ←ᴿ v) ⟩ᵀ[ i ]  Q˙

  ⊢⁺⟨⟩ᵀ-sem (hor-← θ↦v∗P⊢⟨K⟩Q) =  ⁺⟨⟩ᵀᵒ-← $ ⊢⁺⟨⟩ᵀ-sem θ↦v∗P⊢⟨K⟩Q

  -- hor-alloc :
  --   (∀ θ →
  --     θ ↦ᴸ rep n ⊤ṽ  ∗  Free n θ  ∗  P  ⊢[ ∞ ]⟨ K ᴷ◁ ∇ θ ⟩ᵀ[ i ]  Q˙)  →
  --   P  ⊢[ ∞ ]⁺⟨ ĩ₁ (K ᴷ| allocᴿ n) ⟩ᵀ[ i ]  Q˙

  ⊢⁺⟨⟩ᵀ-sem (hor-alloc {n = n} θ↦∗Free∗P⊢⟨Kθ⟩Q) =  ⁺⟨⟩ᵀᵒ-alloc λ θ →
    ∗ᵒ-monoˡ (↦ᴸᵒ⇒↦ᴸ {ᵗvs = rep n _}) › ⊢⁺⟨⟩ᵀ-sem (θ↦∗Free∗P⊢⟨Kθ⟩Q θ)

  -- hor-free :  len ᵗvs ≡ n  →   P  ⊢[ ∞ ]⟨ K ᴷ◁ ∇ _ ⟩ᵀ[ i ]  Q˙  →
  --   θ ↦ᴸ ᵗvs  ∗  Free n θ  ∗  P  ⊢[ ∞ ]⁺⟨ ĩ₁ (K ᴷ| freeᴿ θ) ⟩ᵀ[ i ]  Q˙

  ⊢⁺⟨⟩ᵀ-sem (hor-free {ᵗvs} lenvs≡n P⊢⟨K⟩Q) =
    ∗ᵒ-monoˡ (↦ᴸ⇒↦ᴸᵒ {ᵗvs = ᵗvs}) › ⁺⟨⟩ᵀᵒ-free lenvs≡n (⊢⁺⟨⟩ᵀ-sem P⊢⟨K⟩Q)

--------------------------------------------------------------------------------
-- ⊢⁺⟨⟩ᴾ-sem :  Semantic soundness of the partial Hoare triple

abstract

  ⊢⁺⟨⟩ᴾ-sem :
    P  ⊢[ ∞ ]⁺⟨ vk ⟩ᴾ  Q˙  →   ⸨ P ⸩  ⊨  ⁺⟨ vk ⟩ᴾᵒ[ ι ]  λ v → ⸨ Q˙ v ⸩

  -- _»_ :  P ⊢[ ∞ ] Q →  Q ⊢[ ∞ ]⁺⟨ vk ⟩ᴾ R˙ →  P ⊢[ ∞ ]⁺⟨ vk ⟩ᴾ R˙

  ⊢⁺⟨⟩ᴾ-sem (P⊢Q » Q⊢⟨vk⟩R) =
    ⊨✓⇒⊨-⁺⟨⟩ᴾᵒ λ ✓∙ → ⊢-sem P⊢Q ✓∙ › ⊢⁺⟨⟩ᴾ-sem Q⊢⟨vk⟩R

  -- ∃₁-elim :  (∀ x →  P˙ x ⊢[ ∞ ][ i ]⇛ Q) →  ∃₁˙ P˙ ⊢[ ∞ ][ i ]⇛ Q

  ⊢⁺⟨⟩ᴾ-sem (∃₁-elim Px⊢⟨vk⟩Q) =   ∑-case λ x → ⊢⁺⟨⟩ᴾ-sem (Px⊢⟨vk⟩Q x)

  -- ↪⟨⟩ᴾ-use :  P˂ .! ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂˙)  ⊢[ ∞ ]⟨ ▶ ¡ e ⟩ᴾ  λ v → Q˂˙ v .!

  ⊢⁺⟨⟩ᴾ-sem ↪⟨⟩ᴾ-use big =  ⁺⟨⟩ᴾᵒ-▶ λ{ .! → ⇛ᵒ-⁺⟨⟩ᴾᵒ λ _ → big ▷
    ∗ᵒ-monoʳ (↪⟨⟩ᴾᵒ-use › ⇛ᴵⁿᵈ⇒⇛ᵒ) ▷ ⇛ᵒ-eatˡ ▷ ⇛ᵒ-mono $ ∗ᵒ∃ᵒ-out › λ (-, big) →
    ∗ᵒ∃ᵒ-out big ▷ λ (P∗R⊢⟨e⟩Q , PRa) → ⊢⁺⟨⟩ᴾ-sem P∗R⊢⟨e⟩Q PRa }

  -- _ᵘ»ʰ_ :  P  ⊢[ ∞ ][ i ]⇛  Q  →   Q  ⊢[ ∞ ]⁺⟨ vk ⟩ᴾ  R˙  →
  --          P  ⊢[ ∞ ]⁺⟨ vk ⟩ᴾ  R˙

  ⊢⁺⟨⟩ᴾ-sem (P⊢⇛Q ᵘ»ʰ Q⊢⟨vk⟩R) Pa =  ⇛ᵒ-⁺⟨⟩ᴾᵒ λ _ → Pa ▷ ⊢⇛-sem P⊢⇛Q ▷
    ⇛ᵒ-mono $ ⊢⁺⟨⟩ᴾ-sem Q⊢⟨vk⟩R

  -- _ʰ»ᵘ_ :  P  ⊢[ ∞ ]⁺⟨ vk ⟩ᴾ  Q˙  →
  --          (∀ v →  Q˙ v  ⊢[ ∞ ][ i ]⇛  R˙ v)  →
  --          P  ⊢[ ∞ ]⁺⟨ vk ⟩ᴾ  R˙

  ⊢⁺⟨⟩ᴾ-sem (P⊢⟨vk⟩Q ʰ»ᵘ Qv⊢⇛Rv) =  ⊢⁺⟨⟩ᴾ-sem P⊢⟨vk⟩Q ›
    ⁺⟨⟩ᴾᵒ-mono (λ v Qva _ → ⊢⇛-sem (Qv⊢⇛Rv v) Qva) › ⁺⟨⟩ᴾᵒ-⇛ᵒ

  -- hor-ᵀ⇒ᴾ :  P  ⊢[ ι ]⁺⟨ vk ⟩ᵀ  Q˙  →   P  ⊢[ ι ]⁺⟨ vk ⟩ᴾ  Q˙

  ⊢⁺⟨⟩ᴾ-sem (hor-ᵀ⇒ᴾ P⊢⟨vk⟩Q) =  ⊢⁺⟨⟩ᵀ-sem P⊢⟨vk⟩Q › ⁺⟨⟩ᵀᵒ⇒⁺⟨⟩ᴾᵒ

  -- hor-frameˡ :  P  ⊢[ ∞ ]⁺⟨ vk ⟩ᴾ  Q˙  →
  --               R  ∗  P  ⊢[ ∞ ]⁺⟨ vk ⟩ᴾ  λ v →  R  ∗  Q˙ v

  ⊢⁺⟨⟩ᴾ-sem (hor-frameˡ P⊢⟨vk⟩Q) =  ∗ᵒ-monoʳ (⊢⁺⟨⟩ᴾ-sem P⊢⟨vk⟩Q ) › ⁺⟨⟩ᴾᵒ-eatˡ

  -- hor-valᵘ :  P  ⊢[ ∞ ]⇛  Q˙ v  →   P  ⊢[ ∞ ]⁺⟨ ĩ₀ v ⟩ᴾ  Q˙

  ⊢⁺⟨⟩ᴾ-sem (hor-valᵘ P⊢⇛Qv) Pa =  ⁺⟨⟩ᴾᵒ-val λ _ → Pa ▷ ⊢⇛-sem P⊢⇛Qv

  -- hor-bind :  P  ⊢[ ∞ ]⟨ e ⟩ᴾ  Q˙  →
  --             (∀ v →  Q˙ v  ⊢[ ∞ ]⟨ K ᴷ◁ V⇒E v ⟩ᴾ  R˙)  →
  --             P  ⊢[ ∞ ]⟨ K ᴷ◁ e ⟩ᴾ  R˙

  ⊢⁺⟨⟩ᴾ-sem (hor-bind P⊢⟨e⟩Q Qv⊢⟨Kv⟩R) =  ⊢⁺⟨⟩ᴾ-sem P⊢⟨e⟩Q ›
    ⁺⟨⟩ᴾᵒ-mono (λ v → ⊢⁺⟨⟩ᴾ-sem (Qv⊢⟨Kv⟩R v)) › ⟨⟩ᴾᵒ-bind

  -- hor-nd :  {{Inh X}} →  (∀(x : X) →  P  ⊢[ ∞ ]⟨ K ᴷ◁ ∇ x ⟩ᴾ  Q˙)  →
  --           P  ⊢[ ∞ ]⁺⟨ ĩ₁ (K ᴷ| ndᴿ) ⟩ᴾ  Q˙

  ⊢⁺⟨⟩ᴾ-sem (hor-nd P⊢⟨Kx⟩Q) Pa =  ⁺⟨⟩ᴾᵒ-nd λ x → Pa ▷ ⊢⁺⟨⟩ᴾ-sem (P⊢⟨Kx⟩Q x)

  -- horᴾ-▶ :  P  ⊢[< ∞ ]⟨ K ᴷ◁ e˂ .! ⟩ᴾ  Q˙  →
  --           P  ⊢[ ∞ ]⁺⟨ ĩ₁ (K ᴷ| ▶ᴿ e˂) ⟩ᴾ  Q˙

  ⊢⁺⟨⟩ᴾ-sem (horᴾ-▶ P⊢⟨Ke⟩Q) Pa =  ⁺⟨⟩ᴾᵒ-▶ λ{ .! → ⊢⁺⟨⟩ᴾ-sem (P⊢⟨Ke⟩Q .!) Pa }

  -- hor-◁ :  P  ⊢[ ∞ ]⟨ K ᴷ◁ e˙ x ⟩ᴾ  Q˙  →
  --          P  ⊢[ ∞ ]⁺⟨ ĩ₁ (K ᴷ| e˙ ◁ᴿ x) ⟩ᴾ  Q˙

  ⊢⁺⟨⟩ᴾ-sem (hor-◁ P⊢⟨Kex⟩Q) =  ⊢⁺⟨⟩ᴾ-sem P⊢⟨Kex⟩Q › ⁺⟨⟩ᴾᵒ-◁

  -- hor-⁏ :  P  ⊢[ ∞ ]⟨ K ᴷ◁ e ⟩ᴾ  Q˙  →
  --          P  ⊢[ ∞ ]⁺⟨ ĩ₁ (K ᴷ| v ⁏ᴿ e) ⟩ᴾ  Q˙

  ⊢⁺⟨⟩ᴾ-sem (hor-⁏ P⊢⟨Ke⟩Q) =  ⊢⁺⟨⟩ᴾ-sem P⊢⟨Ke⟩Q › ⁺⟨⟩ᴾᵒ-⁏

  -- hor-🞰 :  θ ↦⟨ p ⟩ (-, v)  ∗  P  ⊢[ ∞ ]⟨ K ᴷ◁ V⇒E v ⟩ᴾ  Q˙  →
  --          θ ↦⟨ p ⟩ (-, v)  ∗  P  ⊢[ ∞ ]⁺⟨ ĩ₁ (K ᴷ| 🞰ᴿ θ) ⟩ᴾ  Q˙

  ⊢⁺⟨⟩ᴾ-sem (hor-🞰 θ↦v∗P⊢⟨Kv⟩Q) =  ⁺⟨⟩ᴾᵒ-🞰 $ ⊢⁺⟨⟩ᴾ-sem θ↦v∗P⊢⟨Kv⟩Q

  -- hor-← :  θ ↦ (-, v)  ∗  P  ⊢[ ∞ ]⟨ K ᴷ◁ ∇ _ ⟩ᴾ  Q˙  →
  --          θ ↦ ᵗu  ∗  P  ⊢[ ∞ ]⁺⟨ ĩ₁ (K ᴷ| θ ←ᴿ v) ⟩ᴾ  Q˙

  ⊢⁺⟨⟩ᴾ-sem (hor-← θ↦v∗P⊢⟨K⟩Q) =  ⁺⟨⟩ᴾᵒ-← $ ⊢⁺⟨⟩ᴾ-sem θ↦v∗P⊢⟨K⟩Q

  -- hor-alloc :
  --   (∀ θ →  θ ↦ᴸ rep n ⊤ṽ  ∗  Free n θ  ∗  P  ⊢[ ∞ ]⟨ K ᴷ◁ ∇ θ ⟩ᴾ  Q˙)  →
  --   P  ⊢[ ∞ ]⁺⟨ ĩ₁ (K ᴷ| allocᴿ n) ⟩ᴾ  Q˙

  ⊢⁺⟨⟩ᴾ-sem (hor-alloc {n = n} θ↦∗Free∗P⊢⟨Kθ⟩Q) =  ⁺⟨⟩ᴾᵒ-alloc λ θ →
    ∗ᵒ-monoˡ (↦ᴸᵒ⇒↦ᴸ {ᵗvs = rep n _}) › ⊢⁺⟨⟩ᴾ-sem (θ↦∗Free∗P⊢⟨Kθ⟩Q θ)

  -- hor-free :  len ᵗvs ≡ n  →   P  ⊢[ ∞ ]⟨ K ᴷ◁ ∇ _ ⟩ᴾ  Q˙  →
  --   θ ↦ᴸ ᵗvs  ∗  Free n θ  ∗  P  ⊢[ ∞ ]⁺⟨ ĩ₁ (K ᴷ| freeᴿ θ) ⟩ᴾ  Q˙

  ⊢⁺⟨⟩ᴾ-sem (hor-free {ᵗvs} lenvs≡n P⊢⟨K⟩Q) =
    ∗ᵒ-monoˡ (↦ᴸ⇒↦ᴸᵒ {ᵗvs = ᵗvs}) › ⁺⟨⟩ᴾᵒ-free lenvs≡n (⊢⁺⟨⟩ᴾ-sem P⊢⟨K⟩Q)
