--------------------------------------------------------------------------------
-- Memory ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Symp.Model.ERA.Mem where

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
open import Symp.Lang.Expr using (Addr; TyVal; ⊤-; Mblo; Mem; _‼ᴹ_; updᴹ; ✓ᴹ_;
  ✓ᴹ-upd˙)
open import Symp.Model.ERA.Base using (ERA; _×ᴱᴿᴬ_; Envmᴱᴿᴬ; Envvᴱᴿᴬ; Upᴱᴿᴬ)
open import Symp.Model.ERA.Exc using (Excᴱᴿᴬ; #ˣ_; εˣ; ✓ˣ-agree; ✓ˣ-new;
  ✓ˣ-free)
open import Symp.Model.ERA.FracAg using (FracAg; _≈ᶠʳ_; _∙ᶠʳ_; FracAgᴱᴿᴬ;
  š[?]-∙ᶠʳ; ✓ᶠʳ-≤1; ✓ᶠʳ-agree; ✓ᶠʳ-agree2; ✓ᶠʳ-upd; ✓ᶠʳ-new; ✓ᶠʳ-free)
import Symp.Model.ERA.All

--------------------------------------------------------------------------------
-- Memᴱᴿᴬ :  Memory ERA

-- Pntsᴱᴿᴬ :  Points-to token ERA

module AllPnts =  Symp.Model.ERA.All ℕ (λ _ → FracAgᴱᴿᴬ TyVal)
open AllPnts public using () renaming (
  --  Pntsᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
  ∀ᴱᴿᴬ to Pntsᴱᴿᴬ;
  --  inj˙ᴾⁿᵗˢ :  ℕ →  FracAgᴱᴿᴬ TyVal →  Pntsᴱᴿᴬ .Res
  inj˙ to inj˙ᴾⁿᵗˢ;
  inj˙-≈ to inj˙ᴾⁿᵗˢ-≈; inj˙-∙ to inj˙ᴾⁿᵗˢ-∙; ✓-inj˙ to ✓-inj˙ᴾⁿᵗˢ)

-- Mbloᴱᴿᴬ :  Memory block ERA

Mbloᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
Mbloᴱᴿᴬ =  Envmᴱᴿᴬ (Pntsᴱᴿᴬ ×ᴱᴿᴬ Excᴱᴿᴬ ℕ)
  Mblo (λ Mb → (λ i → Mb »-¿ _‼ i) , len $¿ Mb)

-- Memᴱᴿᴬ :  Memory ERA

module AllMem =  Symp.Model.ERA.All ℕ (λ _ → Mbloᴱᴿᴬ)
open AllMem public using () renaming (
  --  ∀Memᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
  ∀ᴱᴿᴬ to ∀Memᴱᴿᴬ;
  --  inj˙ᴹᵉᵐ :  ℕ →  Mbloᴱᴿᴬ .Res →  ∀Memᴱᴿᴬ .Res
  inj˙ to inj˙ᴹᵉᵐ;
  inj˙-≈ to inj˙ᴹᵉᵐ-≈; inj˙-∙ to inj˙ᴹᵉᵐ-∙; ✓-inj˙ to ✓-inj˙ᴹᵉᵐ)

Memᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
Memᴱᴿᴬ =  Upᴱᴿᴬ (Envvᴱᴿᴬ ∀Memᴱᴿᴬ ✓ᴹ_)

open ERA Pntsᴱᴿᴬ public using () renaming (Res to Resᴾⁿᵗˢ; _≈_ to _≈ᴾⁿᵗˢ_;
  _◇˜_ to _◇˜ᴾⁿᵗˢ_; ✓-resp to ✓ᴾⁿᵗˢ-resp)
open ERA Mbloᴱᴿᴬ public using () renaming (Res to Resᴹᵇˡᵒ; _≈_ to _≈ᴹᵇˡᵒ_;
  _∙_ to _∙ᴹᵇˡᵒ_; [∙∈ⁱ] to [∙ᴹᵇˡᵒ∈ⁱ]; [∙∈ⁱ⟨⟩] to [∙ᴹᵇˡᵒ∈ⁱ⟨⟩]; _✓_ to _✓ᴹᵇˡᵒ_;
  _↝_ to _↝ᴹᵇˡᵒ_; _◇˜_ to _◇˜ᴹᵇˡᵒ_; ∙-congʳ to ∙ᴹᵇˡᵒ-congʳ)
open ERA Memᴱᴿᴬ public using () renaming (Res to Resᴹᵉᵐ; _≈_ to _≈ᴹᵉᵐ_;
  ε to εᴹᵉᵐ; _∙_ to _∙ᴹᵉᵐ_; _✓_ to _✓ᴹᵉᵐ_; _↝_ to _↝ᴹᵉᵐ_; ◠˜_ to ◠˜ᴹᵉᵐ_;
  _◇˜_ to _◇˜ᴹᵉᵐ_; [∙∈ⁱ] to [∙ᴹᵉᵐ∈ⁱ]; [∙∈ⁱ⟨⟩] to [∙ᴹᵉᵐ∈ⁱ⟨⟩];
  ✓-resp to ✓ᴹᵉᵐ-resp)

[∙ᴹᵇˡᵒ∈ⁱ]-syntax =  [∙ᴹᵇˡᵒ∈ⁱ]
[∙ᴹᵇˡᵒ∈ⁱ⟨⟩]-syntax =  [∙ᴹᵇˡᵒ∈ⁱ⟨⟩]
[∙ᴹᵉᵐ∈ⁱ]-syntax =  [∙ᴹᵉᵐ∈ⁱ]
[∙ᴹᵉᵐ∈ⁱ⟨⟩]-syntax =  [∙ᴹᵉᵐ∈ⁱ⟨⟩]
infix 8 [∙ᴹᵇˡᵒ∈ⁱ]-syntax [∙ᴹᵇˡᵒ∈ⁱ⟨⟩]-syntax [∙ᴹᵉᵐ∈ⁱ]-syntax [∙ᴹᵉᵐ∈ⁱ⟨⟩]-syntax
syntax [∙ᴹᵇˡᵒ∈ⁱ]-syntax (λ ix → a) xs =  [∙ᴹᵇˡᵒ ix ∈ⁱ xs ] a
syntax [∙ᴹᵇˡᵒ∈ⁱ⟨⟩]-syntax (λ ix → a) k xs =  [∙ᴹᵇˡᵒ ix ∈ⁱ⟨ k ⟩ xs ] a
syntax [∙ᴹᵉᵐ∈ⁱ]-syntax (λ ix → a) xs =  [∙ᴹᵉᵐ ix ∈ⁱ xs ] a
syntax [∙ᴹᵉᵐ∈ⁱ⟨⟩]-syntax (λ ix → a) k xs =  [∙ᴹᵉᵐ ix ∈ⁱ⟨ k ⟩ xs ] a

private variable
  θ :  Addr
  i k n o o' :  ℕ
  p q :  ℚ⁺
  ᵗu ᵗv :  TyVal
  ᵗvs :  List TyVal
  Mb :  Mblo
  M :  Mem

--------------------------------------------------------------------------------
-- Block-level resource

infix 9 _↦⟨_⟩ᵇˡᵒ_ _↦ᵇˡᵒ_

-- ↦⟨ ⟩ᵇˡᵒ :  Block-level resource for the points-to token

_↦⟨_⟩ᵇˡᵒ_ :  ℕ →  ℚ⁺ →  TyVal →  Resᴹᵇˡᵒ
(i ↦⟨ p ⟩ᵇˡᵒ ᵗv) .π₀ =  inj˙ᴾⁿᵗˢ i $ š (p , [ ᵗv ])
(_ ↦⟨ _ ⟩ᵇˡᵒ _) .π₁ =  εˣ

-- ↦ᵇˡᵒ :  ↦⟨ ⟩ᵇˡᵒ with the fraction 1

_↦ᵇˡᵒ_ :  ℕ →  TyVal →  Resᴹᵇˡᵒ
i ↦ᵇˡᵒ ᵗv =  i ↦⟨ 1ᴿ⁺ ⟩ᵇˡᵒ ᵗv

-- freeᵇˡᵒ :  Block-level resource for the freeing token

freeᵇˡᵒ :  ℕ →  Resᴹᵇˡᵒ
freeᵇˡᵒ n .π₁ =  #ˣ n
freeᵇˡᵒ _ .π₀ _ =  ň

-- pnts :  Resource for the points-to token over an optional value

pnts :  ¿ TyVal →  FracAg TyVal
pnts (š ᵗv) =  š (1ᴿ⁺ , [ ᵗv ])
pnts ň =  ň

-- ↦ᴸᵇˡᵒ :  Block-level resource for the points-to token over a list of values

infix 9 ↦ᴸᵇˡᵒ_
↦ᴸᵇˡᵒ_ :  List TyVal →  Resᴹᵇˡᵒ
(↦ᴸᵇˡᵒ ᵗvs) .π₀ i =  pnts $ ᵗvs ‼ i
(↦ᴸᵇˡᵒ _) .π₁ =  εˣ

abstract

  -- Modify the fraction of ↦⟨ ⟩ᵇˡᵒ

  ↦⟨⟩ᵇˡᵒ-cong :  p ≈ᴿ⁺ q  →   i ↦⟨ p ⟩ᵇˡᵒ ᵗv  ≈ᴹᵇˡᵒ  i ↦⟨ q ⟩ᵇˡᵒ ᵗv
  ↦⟨⟩ᵇˡᵒ-cong p≈q .π₀ =  inj˙ᴾⁿᵗˢ-≈ (p≈q , ≈ᴸ-refl)
  ↦⟨⟩ᵇˡᵒ-cong _ .π₁ =  refl

  -- Merge ↦⟨ ⟩ᵇˡᵒ w.r.t. +ᴿ⁺

  ↦⟨⟩ᵇˡᵒ-∙ :  i ↦⟨ p ⟩ᵇˡᵒ ᵗv ∙ᴹᵇˡᵒ i ↦⟨ q ⟩ᵇˡᵒ ᵗv  ≈ᴹᵇˡᵒ i ↦⟨ p +ᴿ⁺ q ⟩ᵇˡᵒ ᵗv
  ↦⟨⟩ᵇˡᵒ-∙ .π₁ =  refl
  ↦⟨⟩ᵇˡᵒ-∙ {p = p} {q = q} .π₀ =
    inj˙ᴾⁿᵗˢ-∙ ◇˜ᴾⁿᵗˢ inj˙ᴾⁿᵗˢ-≈ $ š[?]-∙ᶠʳ {p} {q = q}

  -- The fraction of ↦⟨ ⟩ᵇˡᵒ is no more than 1

  ↦⟨⟩ᵇˡᵒ-≤1 :  Mb ✓ᴹᵇˡᵒ i ↦⟨ p ⟩ᵇˡᵒ ᵗv →  p ≤1ᴿ⁺
  ↦⟨⟩ᵇˡᵒ-≤1 =  π₀ › ✓-inj˙ᴾⁿᵗˢ › ✓ᶠʳ-≤1

  -- Agreement of ↦⟨ ⟩ᵇˡᵒ

  ↦⟨⟩ᵇˡᵒ-agree :  Mb ✓ᴹᵇˡᵒ i ↦⟨ p ⟩ᵇˡᵒ ᵗu ∙ᴹᵇˡᵒ i ↦⟨ q ⟩ᵇˡᵒ ᵗv  →  ᵗu ≡ ᵗv
  ↦⟨⟩ᵇˡᵒ-agree =  π₀ › ✓ᴾⁿᵗˢ-resp inj˙ᴾⁿᵗˢ-∙ › ✓-inj˙ᴾⁿᵗˢ › ✓ᶠʳ-agree2

  -- Lemmas on [∙ᴹᵇˡᵒ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] i ↦ᵇˡᵒ ᵗv

  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-away :
    i < k →  ([∙ᴹᵇˡᵒ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] i ↦ᵇˡᵒ ᵗv) .π₀ i  ≡  ň
  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-away {ᵗvs = []} _ =  refl
  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-away {i} {k} {ᵗvs = _ ∷ ᵗvs'} i<k  with i ≟ k
  … | yes refl =  absurd $ <-irrefl i<k
  … | no _ =  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-away {ᵗvs = ᵗvs'} (<-trans i<k ṡ-sincr)

  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-idx :
    ([∙ᴹᵇˡᵒ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] i ↦ᵇˡᵒ ᵗv) .π₀ (k + i)  ≈ᶠʳ  pnts (ᵗvs ‼ i)
  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-idx {ᵗvs = []} =  _
  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-idx {k} {_ ∷ ᵗvs'} {0}  rewrite +-0 {k} |
    ≟-refl {a = k} | [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-away {ᵗvs = ᵗvs'} (ṡ-sincr {k}) =
    refl , ≈ᴸ-refl
  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-idx {k} {_ ∷ ᵗvs'} {ṡ i'}  with k + ṡ i' ≟ k
  … | no _  rewrite +-ṡ {k} {i'} =  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-idx {ṡ k} {ᵗvs'} {i'}
  … | yes k+ṡi'≡k =
    (≡⇒¬< (◠ k+ṡi'≡k) $ subst (_< k + ṡ i') (+-0 {k}) $ +-smonoʳ 0<ṡ) ▷ λ ()

  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-π₁ :  ([∙ᴹᵇˡᵒ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] i ↦ᵇˡᵒ ᵗv) .π₁  ≡  εˣ
  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-π₁ {ᵗvs = []} =  refl
  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-π₁ {ᵗvs = _ ∷ ᵗvs'} =  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-π₁ {ᵗvs = ᵗvs'}

  -- [∙ᴹᵇˡᵒ (i , ᵗv) ∈ⁱ ᵗvs ] i ↦ᵇˡᵒ ᵗv is equivalent to ↦ᴸᵇˡᵒ ᵗvs

  [∙∈ⁱ]↦≈↦ᴸᵇˡᵒ :  [∙ᴹᵇˡᵒ (i , ᵗv) ∈ⁱ ᵗvs ] i ↦ᵇˡᵒ ᵗv  ≈ᴹᵇˡᵒ  ↦ᴸᵇˡᵒ ᵗvs
  [∙∈ⁱ]↦≈↦ᴸᵇˡᵒ {ᵗvs} .π₁ =  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-π₁ {ᵗvs = ᵗvs}
  [∙∈ⁱ]↦≈↦ᴸᵇˡᵒ {ᵗvs} .π₀ _ =  [∙∈ⁱ⟨⟩]↦ᵇˡᵒ-idx {ᵗvs = ᵗvs}

--------------------------------------------------------------------------------
-- Memory-level resource

infix 9 _↦⟨_⟩ʳ_ _↦ʳ_

-- ↦⟨ ⟩ᵇˡᵒ :  Resource for the points-to token

_↦⟨_⟩ʳ_ :  Addr →  ℚ⁺ →  TyVal →  Resᴹᵉᵐ
((o , i) ↦⟨ p ⟩ʳ ᵗv) .↓ =  inj˙ᴹᵉᵐ o $ i ↦⟨ p ⟩ᵇˡᵒ ᵗv

-- ↦ᵇˡᵒ :  ↦⟨ ⟩ᵇˡᵒ with the fraction 1

_↦ʳ_ :  Addr →  TyVal →  Resᴹᵉᵐ
θ ↦ʳ ᵗv =  θ ↦⟨ 1ᴿ⁺ ⟩ʳ ᵗv

-- freeʳ :  Resource for the freeing token

freeʳ :  ℕ →  ℕ →  Resᴹᵉᵐ
freeʳ n o .↓ =  inj˙ᴹᵉᵐ o $ freeᵇˡᵒ n

-- ↦ᴸʳ :  Resource for the points-to token over a list of values

infix 9 _↦ᴸʳ_
_↦ᴸʳ_ :  ℕ →  List TyVal →  Resᴹᵉᵐ
(o ↦ᴸʳ ᵗvs) .↓ =  inj˙ᴹᵉᵐ o $ ↦ᴸᵇˡᵒ ᵗvs

abstract

  -- ↑ M ✓ᴹᵉᵐ εᴹᵉᵐ holds for valid M

  ✓ᴹ⇒✓ᴹᵉᵐ :  ✓ᴹ M →  ↑ M ✓ᴹᵉᵐ εᴹᵉᵐ
  ✓ᴹ⇒✓ᴹᵉᵐ ✓M .↓ =  ✓M , _

  -- Modify the fraction of ↦⟨ ⟩ʳ

  ↦⟨⟩ʳ-cong :  p ≈ᴿ⁺ q  →   θ ↦⟨ p ⟩ʳ ᵗv  ≈ᴹᵉᵐ  θ ↦⟨ q ⟩ʳ ᵗv
  ↦⟨⟩ʳ-cong p≈q .↓ =  inj˙ᴹᵉᵐ-≈ $ ↦⟨⟩ᵇˡᵒ-cong p≈q

  -- Merge ↦⟨ ⟩ʳ w.r.t. +ᴿ⁺

  ↦⟨⟩ʳ-∙ :  θ ↦⟨ p ⟩ʳ ᵗv ∙ᴹᵉᵐ θ ↦⟨ q ⟩ʳ ᵗv  ≈ᴹᵉᵐ  θ ↦⟨ p +ᴿ⁺ q ⟩ʳ ᵗv
  ↦⟨⟩ʳ-∙ =  ↑ inj˙ᴹᵉᵐ-∙ ◇˜ᴹᵉᵐ ↑ inj˙ᴹᵉᵐ-≈ ↦⟨⟩ᵇˡᵒ-∙

  -- The fraction of ↦⟨ ⟩ʳ is no more than 1

  ↦⟨⟩ʳ-≤1 :  ↑ M ✓ᴹᵉᵐ θ ↦⟨ p ⟩ʳ ᵗv →  p ≤1ᴿ⁺
  ↦⟨⟩ʳ-≤1 {M} =  ↓ › π₁ › ✓-inj˙ᴹᵉᵐ › ↦⟨⟩ᵇˡᵒ-≤1 {M _}

  -- Agreement of ↦⟨ ⟩ʳ

  ↦⟨⟩ʳ-agree :  ↑ M ✓ᴹᵉᵐ θ ↦⟨ p ⟩ʳ ᵗu ∙ᴹᵉᵐ θ ↦⟨ q ⟩ʳ ᵗv  →  ᵗu ≡ ᵗv
  ↦⟨⟩ʳ-agree {M} =
    ✓ᴹᵉᵐ-resp (↑ inj˙ᴹᵉᵐ-∙) › ↓ › π₁ › ✓-inj˙ᴹᵉᵐ › ↦⟨⟩ᵇˡᵒ-agree {M _}

  -- Lemmas on [∙ᴹᵉᵐ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] (o , i) ↦ʳ ᵗv

  [∙∈ⁱ⟨⟩]↦ʳ-out :  o' ≢ o →
    ([∙ᴹᵉᵐ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] (o , i) ↦ʳ ᵗv) .↓ o'  ≈ᴹᵇˡᵒ  ((λ _ → ň) , εˣ)
  [∙∈ⁱ⟨⟩]↦ʳ-out {ᵗvs = []} _ =  _ , refl
  [∙∈ⁱ⟨⟩]↦ʳ-out {o'} {o} {ᵗvs = _ ∷ ᵗvs'} o'≢o  with o' ≟ o
  … | yes refl =  absurd $ o'≢o refl
  … | no _ =  [∙∈ⁱ⟨⟩]↦ʳ-out {ᵗvs = ᵗvs'} o'≢o

  [∙∈ⁱ⟨⟩]↦ʳ-in :  ([∙ᴹᵉᵐ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] (o , i) ↦ʳ ᵗv) .↓ o  ≈ᴹᵇˡᵒ
                    [∙ᴹᵇˡᵒ (i , ᵗv) ∈ⁱ⟨ k ⟩ ᵗvs ] i ↦ᵇˡᵒ ᵗv
  [∙∈ⁱ⟨⟩]↦ʳ-in {ᵗvs = []} =  _ , refl
  [∙∈ⁱ⟨⟩]↦ʳ-in {k} {_ ∷ ᵗvs'} {o}  rewrite ≟-refl {a = o} =
    ∙ᴹᵇˡᵒ-congʳ {c = k ↦ᵇˡᵒ _} $ [∙∈ⁱ⟨⟩]↦ʳ-in {ṡ k} {ᵗvs'} {o}

  -- [∙ᴹᵉᵐ (i , ᵗv) ∈ⁱ ᵗvs ] (o , i) ↦ʳ ᵗv is equivalent to o ↦ᴸʳ ᵗvs

  [∙∈ⁱ]↦≈↦ᴸʳ :  [∙ᴹᵉᵐ (i , ᵗv) ∈ⁱ ᵗvs ] (o , i) ↦ʳ ᵗv  ≈ᴹᵉᵐ  o ↦ᴸʳ ᵗvs
  [∙∈ⁱ]↦≈↦ᴸʳ {ᵗvs} {o} .↓ o'  with o' ≟ o
  …   | no o'≢o =  [∙∈ⁱ⟨⟩]↦ʳ-out {ᵗvs = ᵗvs} o'≢o
  …   | yes refl =  [∙∈ⁱ⟨⟩]↦ʳ-in {ᵗvs = ᵗvs} ◇˜ᴹᵇˡᵒ [∙∈ⁱ]↦≈↦ᴸᵇˡᵒ {ᵗvs = ᵗvs}

  -- Read using ↦⟨⟩ʳ

  ↦⟨⟩ʳ-read :  (↑ M , θ ↦⟨ p ⟩ʳ ᵗv)  ↝ᴹᵉᵐ
                 λ (_ : M ‼ᴹ θ ≡ š ᵗv) →  ↑ M , θ ↦⟨ p ⟩ʳ ᵗv
  ↦⟨⟩ʳ-read _ ✓M✓θ↦v∙a .π₁ =  ✓M✓θ↦v∙a
  ↦⟨⟩ʳ-read {θ = o , i} (↑ a) (↑ (-, M✓θ↦v∙a)) .π₀  with M✓θ↦v∙a o .π₀ i
  … | M‼θ✓↦v∙aθ  rewrite ≟-refl {a = o} | ≟-refl {a = i} =
    ✓ᶠʳ-agree {x = a o .π₀ i} M‼θ✓↦v∙aθ

  -- Write using ↦ʳ

  ↦ʳ-write :  (↑ M , θ ↦ʳ ᵗu)  ↝ᴹᵉᵐ λ (_ : ⊤₀) →  ↑ updᴹ θ ᵗv M , θ ↦ʳ ᵗv
  ↦ʳ-write _ _ .π₀ =  _
  ↦ʳ-write _ (↑ (✓M ,-)) .π₁ .↓ .π₀ =  ✓ᴹ-upd˙ ✓M
  ↦ʳ-write {M} {o , i} {ᵗv = ᵗv} _ (↑ (-, M✓θ↦u∙a)) .π₁ .↓ .π₁ o' .π₁
    with o' ≟ o | M✓θ↦u∙a o' .π₁
  … | no _ | Mo'✓ao' =  Mo'✓ao'
  … | yes refl | Mo✓i↦u∙ao  with M o
  …   | ň =  Mo✓i↦u∙ao
  …   | š ᵗus  rewrite upd-len {i} {b = ᵗv} {ᵗus} =  Mo✓i↦u∙ao
  ↦ʳ-write {M} {o , i} {ᵗv = ᵗv} (↑ a) (↑ (-, M✓θ↦u∙a)) .π₁ .↓ .π₁ o' .π₀ j
    with o' ≟ o | M✓θ↦u∙a o' .π₀ j
  … | no _ | Mo'‼j✓ao'j =  Mo'‼j✓ao'j
  … | yes refl | Mo‼j✓i↦uj∙aoj  with j ≟ i | M o | Mo‼j✓i↦uj∙aoj
  …   | no j≢i | ň | Mo‼j✓aoj =  Mo‼j✓aoj
  …   | no j≢i | š ᵗus | Mo‼j✓aoj  rewrite upd-‼-out {b = ᵗv} {ᵗus} j≢i =
    Mo‼j✓aoj
  …   | yes refl | Mo | M‼θ✓↦u∙aθ  with Mo | ✓ᶠʳ-agree {x = a o .π₀ i} M‼θ✓↦u∙aθ
  …     | š ᵗus | us‼i≡šu  rewrite upd-‼-in {as = ᵗus} {b = ᵗv} (-, us‼i≡šu) =
    ✓ᶠʳ-upd {x = a o .π₀ i} M‼θ✓↦u∙aθ

  -- Allocate to get ↦ᴸʳ and freeʳ

  ↦ᴸʳ-alloc :  M o ≡ ň →
    (↑ M , εᴹᵉᵐ)  ↝ᴹᵉᵐ λ (_ : ⊤₀) →
      ↑ upd˙ o (š rep n ⊤-) M  ,  o ↦ᴸʳ rep n ⊤- ∙ᴹᵉᵐ freeʳ n o
  ↦ᴸʳ-alloc _ _ _ .π₀ =  _
  ↦ᴸʳ-alloc _ _ (↑ (✓M ,-)) .π₁ .↓ .π₀ =  ✓ᴹ-upd˙ ✓M
  ↦ᴸʳ-alloc {o = o} {n = n} Mo≡ň _ (↑ (-, M✓a)) .π₁ .↓ .π₁ o' .π₁
    with o' ≟ o | M✓a o' .π₁
  … | no _ | lenMo'✓ao' =  lenMo'✓ao'
  … | yes refl | ň✓ao  rewrite Mo≡ň | rep-len {n} {a = ⊤- } =  ✓ˣ-new ň✓ao
  ↦ᴸʳ-alloc {o = o} {n = n} Mo≡ň _ (↑ (-, M✓a)) .π₁ .↓ .π₁ o' .π₀ i
    with o' ≟ o | M✓a o' .π₀ i
  … | no _ | Mo'‼i✓ao'i =  Mo'‼i✓ao'i
  … | yes refl | Mo‼i✓aoi  rewrite Mo≡ň  with rep n ⊤- ‼ i
  …   | ň =  Mo‼i✓aoi
  …   | š _ =  ✓ᶠʳ-new Mo‼i✓aoi

  -- Bounds check using freeʳ

  freeʳ-š :  (↑ M , freeʳ n o)  ↝ᴹᵉᵐ
               λ (_ : ∑ ᵗvs , M o ≡ š ᵗvs) →  ↑ M , freeʳ n o
  freeʳ-š _ ✓M✓freeno∙ .π₁ =  ✓M✓freeno∙
  freeʳ-š {M} {o = o} (↑ a) (↑ (-, M✓freeno∙)) .π₀  with M✓freeno∙ o .π₁
  … | lenMo✓#n∙  rewrite ≟-refl {a = o}
    with M o | ✓ˣ-agree {x = a o .π₁} lenMo✓#n∙
  …   | š _ | _ =  -, refl

  -- Free using ↦ʳ and freeʳ

  ↦ᴸʳ-free :  len ᵗvs ≡ n →
    (↑ M , o ↦ᴸʳ ᵗvs ∙ᴹᵉᵐ freeʳ n o)  ↝ᴹᵉᵐ λ (_ : ⊤₀) →  ↑ upd˙ o ň M , εᴹᵉᵐ
  ↦ᴸʳ-free _ _ _ .π₀ =  _
  ↦ᴸʳ-free _ _ (↑ (✓M ,-)) .π₁ .↓ .π₀ =  ✓ᴹ-upd˙ ✓M
  ↦ᴸʳ-free {o = o} _ _ (↑ (-, M✓o↦vs∙fno∙a)) .π₁ .↓ .π₁ o' .π₁
    with o' ≟ o | M✓o↦vs∙fno∙a o' .π₁
  … | no _ | lenMo'✓ao' =  lenMo'✓ao'
  … | yes refl | lenMo✓↦#n∙ao =  ✓ˣ-free lenMo✓↦#n∙ao
  ↦ᴸʳ-free {M = M} {o = o} refl (↑ a) (↑ (-, M✓o↦vs∙fno∙a)) .π₁ .↓ .π₁ o' .π₀ i
    with o' ≟ o | M✓o↦vs∙fno∙a o' .π₀ i | M✓o↦vs∙fno∙a o' .π₁
  … | no _ | Mo'‼i✓ao'i | _ =  Mo'‼i✓ao'i
  … | yes refl | Mo‼i✓↦vs∙aoi | lenMo✓#n∙ao
    with M o | ✓ˣ-agree {x = a o .π₁} lenMo✓#n∙ao
  …   | š ᵗus | šlenus≡šn  with š-inj šlenus≡šn
  …     | lenus≡n  with ᵗus ‼ i |
    ‼-len≡-ň {i = i} lenus≡n | ‼-len≡-š {i = i} lenus≡n
  …     | ň | ⇒vs‼i≡ň | _  rewrite ⇒vs‼i≡ň refl =  Mo‼i✓↦vs∙aoi
  …     | š _ | _ | ⇒vs‼i≡š  with ⇒vs‼i≡š (-, refl)
  …       | -, vs‼i≡šv  rewrite vs‼i≡šv =  ✓ᶠʳ-free Mo‼i✓↦vs∙aoi