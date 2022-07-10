--------------------------------------------------------------------------------
-- Reduction
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Lang.Reduce (ℓ : Level) where

open import Base.Level using (^_; ↑_)
open import Base.Size using (Size; ∞)
open import Base.Func using (_$_; id)
open import Base.Prod using (∑-syntax; _×_; _,_)
open import Base.Sum using (_⊎_; inj₀; inj₁)
open import Shog.Lang.Type ℓ using (Type; ValGen; Val)
open import Shog.Lang.Expr ℓ using (Expr; ▶_; ∇*_; λ*˙; _◁_; ★_; _←_; Exprᵛ;
  ⇒Exprᵛ)

private variable
  T U :  Type
  Φ :  ValGen

--------------------------------------------------------------------------------
-- Value & Context-Redex Pair

-- Type for a context-redex pair

Ctxred :  ValGen →  Type →  Set (^ ℓ)
Ctxred Φ T =  ∑ U , (Expr Φ ∞ U → Expr Φ ∞ T) × Expr Φ ∞ U

-- Type for either a value or a context-redex pair

Val/Ctxred :  ValGen →  Type →  Set (^ ℓ)
Val/Ctxred Φ T =  Val (Exprᵛ Φ) T ⊎ Ctxred Φ T

-- Calculate the value or context-redex pair of the expression

val/ctxred :  Expr Φ ∞ T →  Val/Ctxred Φ T
val/ctxred {T = T} (∇* a) =  inj₀ $ ⇒Exprᵛ {T = T} a
val/ctxred (λ*˙ e˙) =  inj₀ $ λ*˙ e˙
val/ctxred (▶ e) =  inj₁ $ _ , id , ▶ e
val/ctxred (e ◁ e') =  inj₁ body
 where
  body :  _
  body  with val/ctxred e'
  ... | inj₁ (_ , e'ᶜ , e'ʳ) =  _ , (λ e₀ → e ◁ e'ᶜ e₀) , e'ʳ
  ... | inj₀ _  with val/ctxred e
  ...   | inj₁ (_ , eᶜ , eʳ) =  _ , (λ e₀ → eᶜ e₀ ◁ e') , eʳ
  ...   | inj₀ _ =  _ , id , (e ◁ e')
val/ctxred (★ e) =  inj₁ body
 where
  body :  _
  body  with val/ctxred e
  ... | inj₁ (_ , eᶜ , eʳ) =  _ , (λ e₀ → ★ eᶜ e₀) , eʳ
  ... | inj₀ _ =  _ , id , ★ e
val/ctxred (e ← e') =  inj₁ body
 where
  body :  _
  body  with  val/ctxred e'
  ... | inj₁ (_ , e'ᶜ , e'ʳ) =  _ , (λ e₀ → e ← e'ᶜ e₀) , e'ʳ
  ... | inj₀ _  with val/ctxred e
  ...   | inj₁ (_ , eᶜ , eʳ) =  _ , (λ e₀ → eᶜ e₀ ← e') , eʳ
  ...   | inj₀ _ =  _ , id , (e ← e')
