--------------------------------------------------------------------------------
-- Heap ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syng.Model.ERA.Heap where

open import Base.Level using (0ᴸ; 1ᴸ; ↑_; ↓)
open import Base.Func using (_$_; _▷_; _∘_; _›_)
open import Base.Few using (⊤₀; absurd)
open import Base.Dec using (yes; no; _≟_; ≟-refl; upd˙)
open import Base.Eq using (_≡_; _≢_; refl; ◠_; subst)
open import Base.Option using (¿_; š_; ň; _»-¿_; _$¿_; š-inj)
open import Base.Prod using (∑-syntax; π₀; π₁; _,_; -,_; _,-)
open import Base.Nat using (ℕ; ṡ_; _<_; _+_; ṡ-sincr; 0<ṡ; <-irrefl; ≡⇒¬<;
  <-trans; +-0; +-ṡ; +-smonoʳ)
open import Base.List using (List; []; _∷_; [_]; len; _‼_; rep; ≈ᴸ-refl;
  ‼-len≡-ň; ‼-len≡-š; upd-len; upd-‼-out; upd-‼-in; rep-len)
open import Base.Ratp using (ℚ⁺; 1ᴿ⁺; _≈ᴿ⁺_; _+ᴿ⁺_; _≤1ᴿ⁺)
open import Syng.Lang.Expr using (Addr; TyVal; ⊤-; Hblo; Heap; _‼ᴴ_; updᴴ; ✓ᴴ_;
  ✓ᴴ-upd˙)
open import Syng.Model.ERA.Base using (ERA; _×ᴱᴿᴬ_; Envmᴱᴿᴬ; Envvᴱᴿᴬ; Upᴱᴿᴬ)
open import Syng.Model.ERA.Exc using (Excᴱᴿᴬ; #ˣ_; εˣ; ✓ˣ-agree; ✓ˣ-new;
  ✓ˣ-free)
open import Syng.Model.ERA.FracAg using (FracAg; _≈ᶠʳ_; _∙ᶠʳ_; FracAgᴱᴿᴬ;
  š[?]-∙ᶠʳ; ✓ᶠʳ-≤1; ✓ᶠʳ-agree; ✓ᶠʳ-agree2; ✓ᶠʳ-upd; ✓ᶠʳ-new; ✓ᶠʳ-free)
import Syng.Model.ERA.All

--------------------------------------------------------------------------------
-- Heapᴱᴿᴬ :  Heap ERA

-- Pntsᴱᴿᴬ :  Points-to token ERA

module AllPnts =  Syng.Model.ERA.All ℕ (λ _ → FracAgᴱᴿᴬ TyVal)
open AllPnts public using () renaming (
  --  Pntsᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
  ∀ᴱᴿᴬ to Pntsᴱᴿᴬ;
  --  inj˙ᴾⁿᵗˢ :  ℕ →  FracAgᴱᴿᴬ TyVal →  Pntsᴱᴿᴬ .Res
  inj˙ to inj˙ᴾⁿᵗˢ;
  inj˙-≈ to inj˙ᴾⁿᵗˢ-≈; inj˙-∙ to inj˙ᴾⁿᵗˢ-∙; ✓-inj˙ to ✓-inj˙ᴾⁿᵗˢ)

-- Hbloᴱᴿᴬ :  Heap block ERA

Hbloᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
Hbloᴱᴿᴬ =  Envmᴱᴿᴬ (Pntsᴱᴿᴬ ×ᴱᴿᴬ Excᴱᴿᴬ ℕ)
  Hblo (λ Hb → (λ i → Hb »-¿ _‼ i) , len $¿ Hb)

-- Heapᴱᴿᴬ :  Heap ERA

module AllHeap =  Syng.Model.ERA.All ℕ (λ _ → Hbloᴱᴿᴬ)
open AllHeap public using () renaming (
  --  ∀Heapᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
  ∀ᴱᴿᴬ to ∀Heapᴱᴿᴬ;
  --  inj˙ᴴᵉᵃᵖ :  ℕ →  Hbloᴱᴿᴬ .Res →  ∀Heapᴱᴿᴬ .Res
  inj˙ to inj˙ᴴᵉᵃᵖ;
  inj˙-≈ to inj˙ᴴᵉᵃᵖ-≈; inj˙-∙ to inj˙ᴴᵉᵃᵖ-∙; ✓-inj˙ to ✓-inj˙ᴴᵉᵃᵖ)

Heapᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
Heapᴱᴿᴬ =  Upᴱᴿᴬ (Envvᴱᴿᴬ ∀Heapᴱᴿᴬ ✓ᴴ_)

open ERA Pntsᴱᴿᴬ public using () renaming (Res to Resᴾⁿᵗˢ; _≈_ to _≈ᴾⁿᵗˢ_;
  _◇˜_ to _◇˜ᴾⁿᵗˢ_; ✓-resp to ✓ᴾⁿᵗˢ-resp)
open ERA Hbloᴱᴿᴬ public using () renaming (Res to Resᴴᵇˡᵒ; _≈_ to _≈ᴴᵇˡᵒ_;
  _∙_ to _∙ᴴᵇˡᵒ_; [∙∈ⁱ] to [∙ᴴᵇˡᵒ∈ⁱ]; [∙∈ⁱ⟨⟩] to [∙ᴴᵇˡᵒ∈ⁱ⟨⟩]; _✓_ to _✓ᴴᵇˡᵒ_;
  _↝_ to _↝ᴴᵇˡᵒ_; _◇˜_ to _◇˜ᴴᵇˡᵒ_; ∙-congʳ to ∙ᴴᵇˡᵒ-congʳ)
open ERA Heapᴱᴿᴬ public using () renaming (Res to Resᴴᵉᵃᵖ; _≈_ to _≈ᴴᵉᵃᵖ_;
  ε to εᴴᵉᵃᵖ; _∙_ to _∙ᴴᵉᵃᵖ_; _✓_ to _✓ᴴᵉᵃᵖ_; _↝_ to _↝ᴴᵉᵃᵖ_; ◠˜_ to ◠˜ᴴᵉᵃᵖ_;
  _◇˜_ to _◇˜ᴴᵉᵃᵖ_; [∙∈ⁱ] to [∙ᴴᵉᵃᵖ∈ⁱ]; [∙∈ⁱ⟨⟩] to [∙ᴴᵉᵃᵖ∈ⁱ⟨⟩];
  ✓-resp to ✓ᴴᵉᵃᵖ-resp)

[∙ᴴᵇˡᵒ∈ⁱ]-syntax =  [∙ᴴᵇˡᵒ∈ⁱ]
[∙ᴴᵇˡᵒ∈ⁱ⟨⟩]-syntax =  [∙ᴴᵇˡᵒ∈ⁱ⟨⟩]
[∙ᴴᵉᵃᵖ∈ⁱ]-syntax =  [∙ᴴᵉᵃᵖ∈ⁱ]
[∙ᴴᵉᵃᵖ∈ⁱ⟨⟩]-syntax =  [∙ᴴᵉᵃᵖ∈ⁱ⟨⟩]
infix 8 [∙ᴴᵇˡᵒ∈ⁱ]-syntax [∙ᴴᵇˡᵒ∈ⁱ⟨⟩]-syntax [∙ᴴᵉᵃᵖ∈ⁱ]-syntax [∙ᴴᵉᵃᵖ∈ⁱ⟨⟩]-syntax
syntax [∙ᴴᵇˡᵒ∈ⁱ]-syntax (λ ix → a) xs =  [∙ᴴᵇˡᵒ ix ∈ⁱ xs ] a
syntax [∙ᴴᵇˡᵒ∈ⁱ⟨⟩]-syntax (λ ix → a) k xs =  [∙ᴴᵇˡᵒ ix ∈ⁱ⟨ k ⟩ xs ] a
syntax [∙ᴴᵉᵃᵖ∈ⁱ]-syntax (λ ix → a) xs =  [∙ᴴᵉᵃᵖ ix ∈ⁱ xs ] a
syntax [∙ᴴᵉᵃᵖ∈ⁱ⟨⟩]-syntax (λ ix → a) k xs =  [∙ᴴᵉᵃᵖ ix ∈ⁱ⟨ k ⟩ xs ] a

private variable
  θ :  Addr
  i k n o o' :  ℕ
  p q :  ℚ⁺
  ᵗu ᵗv :  TyVal
  ᵗvs :  List TyVal
  Hb :  Hblo
  H :  Heap

--------------------------------------------------------------------------------
-- Block-level resource

infix 9 _↦⟨_⟩ᵇˡᵒ_ _↦ᵇˡᵒ_

-- ↦⟨ ⟩ᵇˡᵒ :  Block-level resource for the points-to token

_↦⟨_⟩ᵇˡᵒ_ :  ℕ →  ℚ⁺ →  TyVal →  Resᴴᵇˡᵒ
(i ↦⟨ p ⟩ᵇˡᵒ ᵗv) .π₀ =  inj˙ᴾⁿᵗˢ i $ š (p , [ ᵗv ])
(_ ↦⟨ _ ⟩ᵇˡᵒ _) .π₁ =  εˣ

-- ↦ᵇˡᵒ :  ↦⟨ ⟩ᵇˡᵒ with the fraction 1

_↦ᵇˡᵒ_ :  ℕ →  TyVal →  Resᴴᵇˡᵒ
i ↦ᵇˡᵒ ᵗv =  i ↦⟨ 1ᴿ⁺ ⟩ᵇˡᵒ ᵗv

-- freeᵇˡᵒ :  Block-level resource for the freeing token

freeᵇˡᵒ :  ℕ →  Resᴴᵇˡᵒ
freeᵇˡᵒ n .π₁ =  #ˣ n
freeᵇˡᵒ _ .π₀ _ =  ň

-- pnts :  Resource for the points-to token over an optional value

pnts :  ¿ TyVal →  FracAg TyVal
pnts (š ᵗv) =  š (1ᴿ⁺ , [ ᵗv ])
pnts ň =  ň

-- ↦ᴸᵇˡᵒ :  Block-level resource for the points-to token over a list of values

infix 9 ↦ᴸᵇˡᵒ_
↦ᴸᵇˡᵒ_ :  List TyVal →  Resᴴᵇˡᵒ
(↦ᴸᵇˡᵒ ᵗvs) .π₀ i =  pnts $ ᵗvs ‼ i
(↦ᴸᵇˡᵒ _) .π₁ =  εˣ

abstract

  -- Hodify the fraction of ↦⟨ ⟩ᵇˡᵒ

  ↦⟨⟩ᵇˡᵒ-cong :  p ≈ᴿ⁺ q  →   i ↦⟨ p ⟩ᵇˡᵒ ᵗv  ≈ᴴᵇˡᵒ  i ↦⟨ q ⟩ᵇˡᵒ ᵗv
  ↦⟨⟩ᵇˡᵒ-cong p≈q .π₀ =  inj˙ᴾⁿᵗˢ-≈ (p≈q , ≈ᴸ-refl)
  ↦⟨⟩ᵇˡᵒ-cong _ .π₁ =  refl

  -- Merge ↦⟨ ⟩ᵇˡᵒ w.r.t. +ᴿ⁺

  ↦⟨⟩ᵇˡᵒ-∙ :  i ↦⟨ p ⟩ᵇˡᵒ ᵗv ∙ᴴᵇˡᵒ i ↦⟨ q ⟩ᵇˡᵒ ᵗv  ≈ᴴᵇˡᵒ i ↦⟨ p +ᴿ⁺ q ⟩ᵇˡᵒ ᵗv
  ↦⟨⟩ᵇˡᵒ-∙ .π₁ =  refl
  ↦⟨⟩ᵇˡᵒ-∙ {p = p} {q = q} .π₀ =
    inj˙ᴾⁿᵗˢ-∙ ◇˜ᴾⁿᵗˢ inj˙ᴾⁿᵗˢ-≈ $ š[?]-∙ᶠʳ {p} {q = q}

  -- The fraction of ↦⟨ ⟩ᵇˡᵒ is no more than 1

  ↦⟨⟩ᵇˡᵒ-≤1 :  Hb ✓ᴴᵇˡᵒ i ↦⟨ p ⟩ᵇˡᵒ ᵗv →  p ≤1ᴿ⁺
  ↦⟨⟩ᵇˡᵒ-≤1 =  π₀ › ✓-inj˙ᴾⁿᵗˢ › ✓ᶠʳ-≤1

  -- Agreement of ↦⟨ ⟩ᵇˡᵒ

  ↦⟨⟩ᵇˡᵒ-agree :  Hb ✓ᴴᵇˡᵒ i ↦⟨ p ⟩ᵇˡᵒ ᵗu ∙ᴴᵇˡᵒ i ↦⟨ q ⟩ᵇˡᵒ ᵗv  →  ᵗu ≡ ᵗv
  ↦⟨⟩ᵇˡᵒ-agree =  π₀ › ✓ᴾⁿᵗˢ-resp inj˙ᴾⁿᵗˢ-∙ › ✓-inj˙ᴾⁿᵗˢ › ✓ᶠʳ-agree2

  -- Lemmas on [∙ᴴᵇˡᵒ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] i ↦ᵇˡᵒ ᵗv

  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-away :
    i < k →  ([∙ᴴᵇˡᵒ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] i ↦ᵇˡᵒ ᵗv) .π₀ i  ≡  ň
  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-away {ᵗvs = []} _ =  refl
  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-away {i} {k} {ᵗvs = _ ∷ ᵗvs'} i<k  with i ≟ k
  … | yes refl =  absurd $ <-irrefl i<k
  … | no _ =  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-away {ᵗvs = ᵗvs'} (<-trans i<k ṡ-sincr)

  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-idx :
    ([∙ᴴᵇˡᵒ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] i ↦ᵇˡᵒ ᵗv) .π₀ (k + i)  ≈ᶠʳ  pnts (ᵗvs ‼ i)
  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-idx {ᵗvs = []} =  _
  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-idx {k} {_ ∷ ᵗvs'} {0}  rewrite +-0 {k} |
    ≟-refl {a = k} | [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-away {ᵗvs = ᵗvs'} (ṡ-sincr {k}) =
    refl , ≈ᴸ-refl
  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-idx {k} {_ ∷ ᵗvs'} {ṡ i'}  with k + ṡ i' ≟ k
  … | no _  rewrite +-ṡ {k} {i'} =  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-idx {ṡ k} {ᵗvs'} {i'}
  … | yes k+ṡi'≡k =
    (≡⇒¬< (◠ k+ṡi'≡k) $ subst (_< k + ṡ i') (+-0 {k}) $ +-smonoʳ 0<ṡ) ▷ λ ()

  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-π₁ :  ([∙ᴴᵇˡᵒ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] i ↦ᵇˡᵒ ᵗv) .π₁  ≡  εˣ
  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-π₁ {ᵗvs = []} =  refl
  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-π₁ {ᵗvs = _ ∷ ᵗvs'} =  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-π₁ {ᵗvs = ᵗvs'}

  -- [∙ᴴᵇˡᵒ (i , ᵗv) ∈ⁱ ᵗvs ] i ↦ᵇˡᵒ ᵗv is equivalent to ↦ᴸᵇˡᵒ ᵗvs

  [∙∈ⁱ]↦≈↦ᴸᵇˡᵒ :  [∙ᴴᵇˡᵒ (i , ᵗv) ∈ⁱ ᵗvs ] i ↦ᵇˡᵒ ᵗv  ≈ᴴᵇˡᵒ  ↦ᴸᵇˡᵒ ᵗvs
  [∙∈ⁱ]↦≈↦ᴸᵇˡᵒ {ᵗvs} .π₁ =  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-π₁ {ᵗvs = ᵗvs}
  [∙∈ⁱ]↦≈↦ᴸᵇˡᵒ {ᵗvs} .π₀ _ =  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-idx {ᵗvs = ᵗvs}

--------------------------------------------------------------------------------
-- Heap-level resource

infix 9 _↦⟨_⟩ʳ_ _↦ʳ_

-- ↦⟨ ⟩ᵇˡᵒ :  Resource for the points-to token

_↦⟨_⟩ʳ_ :  Addr →  ℚ⁺ →  TyVal →  Resᴴᵉᵃᵖ
((o , i) ↦⟨ p ⟩ʳ ᵗv) .↓ =  inj˙ᴴᵉᵃᵖ o $ i ↦⟨ p ⟩ᵇˡᵒ ᵗv

-- ↦ᵇˡᵒ :  ↦⟨ ⟩ᵇˡᵒ with the fraction 1

_↦ʳ_ :  Addr →  TyVal →  Resᴴᵉᵃᵖ
θ ↦ʳ ᵗv =  θ ↦⟨ 1ᴿ⁺ ⟩ʳ ᵗv

-- freeʳ :  Resource for the freeing token

freeʳ :  ℕ →  ℕ →  Resᴴᵉᵃᵖ
freeʳ n o .↓ =  inj˙ᴴᵉᵃᵖ o $ freeᵇˡᵒ n

-- ↦ᴸʳ :  Resource for the points-to token over a list of values

infix 9 _↦ᴸʳ_
_↦ᴸʳ_ :  ℕ →  List TyVal →  Resᴴᵉᵃᵖ
(o ↦ᴸʳ ᵗvs) .↓ =  inj˙ᴴᵉᵃᵖ o $ ↦ᴸᵇˡᵒ ᵗvs

abstract

  -- ↑ H ✓ᴴᵉᵃᵖ εᴴᵉᵃᵖ holds for valid H

  ✓ᴴ⇒✓ᴴᵉᵃᵖ :  ✓ᴴ H →  ↑ H ✓ᴴᵉᵃᵖ εᴴᵉᵃᵖ
  ✓ᴴ⇒✓ᴴᵉᵃᵖ ✓H .↓ =  ✓H , _

  -- Hodify the fraction of ↦⟨ ⟩ʳ

  ↦⟨⟩ʳ-cong :  p ≈ᴿ⁺ q  →   θ ↦⟨ p ⟩ʳ ᵗv  ≈ᴴᵉᵃᵖ  θ ↦⟨ q ⟩ʳ ᵗv
  ↦⟨⟩ʳ-cong p≈q .↓ =  inj˙ᴴᵉᵃᵖ-≈ $ ↦⟨⟩ᵇˡᵒ-cong p≈q

  -- Merge ↦⟨ ⟩ʳ w.r.t. +ᴿ⁺

  ↦⟨⟩ʳ-∙ :  θ ↦⟨ p ⟩ʳ ᵗv ∙ᴴᵉᵃᵖ θ ↦⟨ q ⟩ʳ ᵗv  ≈ᴴᵉᵃᵖ  θ ↦⟨ p +ᴿ⁺ q ⟩ʳ ᵗv
  ↦⟨⟩ʳ-∙ =  ↑ inj˙ᴴᵉᵃᵖ-∙ ◇˜ᴴᵉᵃᵖ ↑ inj˙ᴴᵉᵃᵖ-≈ ↦⟨⟩ᵇˡᵒ-∙

  -- The fraction of ↦⟨ ⟩ʳ is no more than 1

  ↦⟨⟩ʳ-≤1 :  ↑ H ✓ᴴᵉᵃᵖ θ ↦⟨ p ⟩ʳ ᵗv →  p ≤1ᴿ⁺
  ↦⟨⟩ʳ-≤1 {H} =  ↓ › π₁ › ✓-inj˙ᴴᵉᵃᵖ › ↦⟨⟩ᵇˡᵒ-≤1 {H _}

  -- Agreement of ↦⟨ ⟩ʳ

  ↦⟨⟩ʳ-agree :  ↑ H ✓ᴴᵉᵃᵖ θ ↦⟨ p ⟩ʳ ᵗu ∙ᴴᵉᵃᵖ θ ↦⟨ q ⟩ʳ ᵗv  →  ᵗu ≡ ᵗv
  ↦⟨⟩ʳ-agree {H} =
    ✓ᴴᵉᵃᵖ-resp (↑ inj˙ᴴᵉᵃᵖ-∙) › ↓ › π₁ › ✓-inj˙ᴴᵉᵃᵖ › ↦⟨⟩ᵇˡᵒ-agree {H _}

  -- Lemmas on [∙ᴴᵉᵃᵖ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] (o , i) ↦ʳ ᵗv

  [∙∈ⁱ⟨⟩]↦ʳ-out :  o' ≢ o →
    ([∙ᴴᵉᵃᵖ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] (o , i) ↦ʳ ᵗv) .↓ o'  ≈ᴴᵇˡᵒ  ((λ _ → ň) , εˣ)
  [∙∈ⁱ⟨⟩]↦ʳ-out {ᵗvs = []} _ =  _ , refl
  [∙∈ⁱ⟨⟩]↦ʳ-out {o'} {o} {ᵗvs = _ ∷ ᵗvs'} o'≢o  with o' ≟ o
  … | yes refl =  absurd $ o'≢o refl
  … | no _ =  [∙∈ⁱ⟨⟩]↦ʳ-out {ᵗvs = ᵗvs'} o'≢o

  [∙∈ⁱ⟨⟩]↦ʳ-in :  ([∙ᴴᵉᵃᵖ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] (o , i) ↦ʳ ᵗv) .↓ o  ≈ᴴᵇˡᵒ
                    [∙ᴴᵇˡᵒ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] i ↦ᵇˡᵒ ᵗv
  [∙∈ⁱ⟨⟩]↦ʳ-in {ᵗvs = []} =  _ , refl
  [∙∈ⁱ⟨⟩]↦ʳ-in {k} {_ ∷ ᵗvs'} {o}  rewrite ≟-refl {a = o} =
    ∙ᴴᵇˡᵒ-congʳ {c = k ↦ᵇˡᵒ _} $ [∙∈ⁱ⟨⟩]↦ʳ-in {ṡ k} {ᵗvs'} {o}

  -- [∙ᴴᵉᵃᵖ (i , ᵗv) ∈ⁱ ᵗvs ] (o , i) ↦ʳ ᵗv is equivalent to o ↦ᴸʳ ᵗvs

  [∙∈ⁱ]↦≈↦ᴸʳ :  [∙ᴴᵉᵃᵖ (i , ᵗv) ∈ⁱ ᵗvs ] (o , i) ↦ʳ ᵗv  ≈ᴴᵉᵃᵖ  o ↦ᴸʳ ᵗvs
  [∙∈ⁱ]↦≈↦ᴸʳ {ᵗvs} {o} .↓ o'  with o' ≟ o
  …   | no o'≢o =  [∙∈ⁱ⟨⟩]↦ʳ-out {ᵗvs = ᵗvs} o'≢o
  …   | yes refl =  [∙∈ⁱ⟨⟩]↦ʳ-in {ᵗvs = ᵗvs} ◇˜ᴴᵇˡᵒ [∙∈ⁱ]↦≈↦ᴸᵇˡᵒ {ᵗvs = ᵗvs}

  -- Read using ↦⟨⟩ʳ

  ↦⟨⟩ʳ-read :  (↑ H , θ ↦⟨ p ⟩ʳ ᵗv)  ↝ᴴᵉᵃᵖ
                 λ (_ : H ‼ᴴ θ ≡ š ᵗv) →  ↑ H , θ ↦⟨ p ⟩ʳ ᵗv
  ↦⟨⟩ʳ-read _ ✓H✓θ↦v∙a .π₁ =  ✓H✓θ↦v∙a
  ↦⟨⟩ʳ-read {θ = o , i} (↑ a) (↑ (-, H✓θ↦v∙a)) .π₀  with H✓θ↦v∙a o .π₀ i
  … | H‼θ✓↦v∙aθ  rewrite ≟-refl {a = o} | ≟-refl {a = i} =
    ✓ᶠʳ-agree {x = a o .π₀ i} H‼θ✓↦v∙aθ

  -- Write using ↦ʳ

  ↦ʳ-write :  (↑ H , θ ↦ʳ ᵗu)  ↝ᴴᵉᵃᵖ λ (_ : ⊤₀) →  ↑ updᴴ θ ᵗv H , θ ↦ʳ ᵗv
  ↦ʳ-write _ _ .π₀ =  _
  ↦ʳ-write _ (↑ (✓H ,-)) .π₁ .↓ .π₀ =  ✓ᴴ-upd˙ ✓H
  ↦ʳ-write {H} {o , i} {ᵗv = ᵗv} _ (↑ (-, H✓θ↦u∙a)) .π₁ .↓ .π₁ o' .π₁
    with o' ≟ o | H✓θ↦u∙a o' .π₁
  … | no _ | Ho'✓ao' =  Ho'✓ao'
  … | yes refl | Ho✓i↦u∙ao  with H o
  …   | ň =  Ho✓i↦u∙ao
  …   | š ᵗus  rewrite upd-len {i} {b = ᵗv} {ᵗus} =  Ho✓i↦u∙ao
  ↦ʳ-write {H} {o , i} {ᵗv = ᵗv} (↑ a) (↑ (-, H✓θ↦u∙a)) .π₁ .↓ .π₁ o' .π₀ j
    with o' ≟ o | H✓θ↦u∙a o' .π₀ j
  … | no _ | Ho'‼j✓ao'j =  Ho'‼j✓ao'j
  … | yes refl | Ho‼j✓i↦uj∙aoj  with j ≟ i | H o | Ho‼j✓i↦uj∙aoj
  …   | no j≢i | ň | Ho‼j✓aoj =  Ho‼j✓aoj
  …   | no j≢i | š ᵗus | Ho‼j✓aoj  rewrite upd-‼-out {b = ᵗv} {ᵗus} j≢i =
    Ho‼j✓aoj
  …   | yes refl | Ho | H‼θ✓↦u∙aθ  with Ho | ✓ᶠʳ-agree {x = a o .π₀ i} H‼θ✓↦u∙aθ
  …     | š ᵗus | us‼i≡šu  rewrite upd-‼-in {as = ᵗus} {b = ᵗv} (-, us‼i≡šu) =
    ✓ᶠʳ-upd {x = a o .π₀ i} H‼θ✓↦u∙aθ

  -- Allocate to get ↦ᴸʳ and freeʳ

  ↦ᴸʳ-alloc :  H o ≡ ň →
    (↑ H , εᴴᵉᵃᵖ)  ↝ᴴᵉᵃᵖ λ (_ : ⊤₀) →
      ↑ upd˙ o (š rep n ⊤-) H  ,  o ↦ᴸʳ rep n ⊤- ∙ᴴᵉᵃᵖ freeʳ n o
  ↦ᴸʳ-alloc _ _ _ .π₀ =  _
  ↦ᴸʳ-alloc _ _ (↑ (✓H ,-)) .π₁ .↓ .π₀ =  ✓ᴴ-upd˙ ✓H
  ↦ᴸʳ-alloc {o = o} {n = n} Ho≡ň _ (↑ (-, H✓a)) .π₁ .↓ .π₁ o' .π₁
    with o' ≟ o | H✓a o' .π₁
  … | no _ | lenHo'✓ao' =  lenHo'✓ao'
  … | yes refl | ň✓ao  rewrite Ho≡ň | rep-len {n} {a = ⊤- } =  ✓ˣ-new ň✓ao
  ↦ᴸʳ-alloc {o = o} {n = n} Ho≡ň _ (↑ (-, H✓a)) .π₁ .↓ .π₁ o' .π₀ i
    with o' ≟ o | H✓a o' .π₀ i
  … | no _ | Ho'‼i✓ao'i =  Ho'‼i✓ao'i
  … | yes refl | Ho‼i✓aoi  rewrite Ho≡ň  with rep n ⊤- ‼ i
  …   | ň =  Ho‼i✓aoi
  …   | š _ =  ✓ᶠʳ-new Ho‼i✓aoi

  -- Bounds check using freeʳ

  freeʳ-š :  (↑ H , freeʳ n o)  ↝ᴴᵉᵃᵖ
               λ (_ : ∑ ᵗvs , H o ≡ š ᵗvs) →  ↑ H , freeʳ n o
  freeʳ-š _ ✓H✓freeno∙ .π₁ =  ✓H✓freeno∙
  freeʳ-š {H} {o = o} (↑ a) (↑ (-, H✓freeno∙)) .π₀  with H✓freeno∙ o .π₁
  … | lenHo✓#n∙  rewrite ≟-refl {a = o}
    with H o | ✓ˣ-agree {x = a o .π₁} lenHo✓#n∙
  …   | š _ | _ =  -, refl

  -- Free using ↦ʳ and freeʳ

  ↦ᴸʳ-free :  len ᵗvs ≡ n →
    (↑ H , o ↦ᴸʳ ᵗvs ∙ᴴᵉᵃᵖ freeʳ n o)  ↝ᴴᵉᵃᵖ λ (_ : ⊤₀) →  ↑ upd˙ o ň H , εᴴᵉᵃᵖ
  ↦ᴸʳ-free _ _ _ .π₀ =  _
  ↦ᴸʳ-free _ _ (↑ (✓H ,-)) .π₁ .↓ .π₀ =  ✓ᴴ-upd˙ ✓H
  ↦ᴸʳ-free {o = o} _ _ (↑ (-, H✓o↦vs∙fno∙a)) .π₁ .↓ .π₁ o' .π₁
    with o' ≟ o | H✓o↦vs∙fno∙a o' .π₁
  … | no _ | lenHo'✓ao' =  lenHo'✓ao'
  … | yes refl | lenHo✓↦#n∙ao =  ✓ˣ-free lenHo✓↦#n∙ao
  ↦ᴸʳ-free {H = H} {o = o} refl (↑ a) (↑ (-, H✓o↦vs∙fno∙a)) .π₁ .↓ .π₁ o' .π₀ i
    with o' ≟ o | H✓o↦vs∙fno∙a o' .π₀ i | H✓o↦vs∙fno∙a o' .π₁
  … | no _ | Ho'‼i✓ao'i | _ =  Ho'‼i✓ao'i
  … | yes refl | Ho‼i✓↦vs∙aoi | lenHo✓#n∙ao
    with H o | ✓ˣ-agree {x = a o .π₁} lenHo✓#n∙ao
  …   | š ᵗus | šlenus≡šn  with š-inj šlenus≡šn
  …     | lenus≡n  with ᵗus ‼ i |
    ‼-len≡-ň {i = i} lenus≡n | ‼-len≡-š {i = i} lenus≡n
  …     | ň | ⇒vs‼i≡ň | _  rewrite ⇒vs‼i≡ň refl =  Ho‼i✓↦vs∙aoi
  …     | š _ | _ | ⇒vs‼i≡š  with ⇒vs‼i≡š (-, refl)
  …       | -, vs‼i≡šv  rewrite vs‼i≡šv =  ✓ᶠʳ-free Ho‼i✓↦vs∙aoi
