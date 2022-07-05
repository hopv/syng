--------------------------------------------------------------------------------
-- Reduction
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Lang.Reduce (ℓ : Level) where

open import Base.Level using (^ˡ_; ↑ˡ_)
open import Base.Size using (Size; ∞)
open import Base.Thunk using (Thunk; !)
open import Base.Func using (_$_; id; _▷_)
open import Base.Prod using (∑-syntax; _×_; _,_)
open import Base.Bool using (Bool; tt; ff)
open import Base.Option using (??_; some; none)
open import Shog.Lang.Type ℓ using (Type; _*→*_; _→*_; VTF; Vt*; Vt)
open import Shog.Lang.Expr ℓ using (Expr*; ▸_; ∇*_; λ*˙; _◁_; ★_; _←_)

private variable
  T U :  Type
  Φ :  VTF

--------------------------------------------------------------------------------
-- Evaluation Context and Redex

-- Type for the evaluation context and redex
EvctxRedex :  VTF →  Type →  Set (^ˡ ℓ)
EvctxRedex Φ T =  ∑ U , (Expr* Φ ∞ U → Expr* Φ ∞ T) × Expr* Φ ∞ U

-- Calculate the evaluation context and redex of an expression,
-- returning none for a value
evctx-redex :  Expr* Φ ∞ T →  ?? EvctxRedex Φ T
evctx-redex (∇* _) =  none
evctx-redex (λ*˙ _) =  none
evctx-redex (▸ e) =  some $ _ , id , ▸ e
evctx-redex (e ◁ e') =  some body
 where
  body :  EvctxRedex _ _
  body  with evctx-redex e'
  ... | some (_ , e'ᶜ , e'ʳ) =  _ , (λ e₀ → e ◁ e'ᶜ e₀) , e'ʳ
  ... | none  with evctx-redex e
  ...   | some (_ , eᶜ , eʳ) =  _ , (λ e₀ → eᶜ e₀ ◁ e') , eʳ
  ...   | none =  _ , id , (e ◁ e')
evctx-redex (★ e) =  some body
 where
  body :  EvctxRedex _ _
  body  with evctx-redex e
  ... | some (_ , eᶜ , eʳ) =  _ , (λ e₀ → ★ eᶜ e₀) , eʳ
  ... | none =  _ , id , ★ e
evctx-redex (e ← e') =  some body
 where
  body :  EvctxRedex _ _
  body  with  evctx-redex e'
  ... | some (_ , e'ᶜ , e'ʳ) =  _ , (λ e₀ → e ← e'ᶜ e₀) , e'ʳ
  ... | none  with evctx-redex e
  ...   | some (_ , eᶜ , eʳ) =  _ , (λ e₀ → eᶜ e₀ ← e') , eʳ
  ...   | none =  _ , id , (e ← e')

-- Judge if the expression is a value
is-value :  Expr* Φ ∞ T →  Bool
is-value e  with evctx-redex e
... | none =  tt
... | some _ =  ff
