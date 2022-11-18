--------------------------------------------------------------------------------
-- Borrow ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syng.Model.ERA.Bor where

open import Base.Level using (1ᴸ)
open import Base.Func using (_$_)
open import Base.Few using (⊤₀)
open import Base.Eq using (_≡_; refl)
open import Base.Dec using (upd˙)
open import Base.Bool using (𝔹; tt; ff)
open import Base.Option using (¿_; š_; ň)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_; _,-)
open import Base.Nat using (ℕ; ṡ_; _<_)
open import Base.Ratp using (ℚ⁺)
open import Syng.Logic.Prop using (Lft; SProp∞)
open import Syng.Model.ERA.Base using (ERA; _×ᴱᴿᴬ_; Envmᴱᴿᴬ)
open import Syng.Model.ERA.Exc using (Excᴱᴿᴬ; εˣ; #ˣ_; ň-✓ˣ)
import Syng.Model.ERA.Bnd

--------------------------------------------------------------------------------
-- Borᴱᴿᴬ :  Borrow ERA

-- Borbᴱᴿᴬ :  Borrow box ERA

Envᴮᵒʳᵇ :  Set₁
Envᴮᵒʳᵇ =  ¿ (¿ ℚ⁺ × 𝔹 × Lft × SProp∞ × SProp∞)

lenvᴮᵒʳᵇ :  Envᴮᵒʳᵇ →  ¿ (¿ ℚ⁺ × Lft × SProp∞)
lenvᴮᵒʳᵇ (š (pˇ , -, α , P , _)) =  š (pˇ , α , P)
lenvᴮᵒʳᵇ ň =  ň

renvᴮᵒʳᵇ :  Envᴮᵒʳᵇ →  ¿ (𝔹 × Lft × SProp∞)
renvᴮᵒʳᵇ (š (-, b , α , -, Q)) =  š (b , α , Q)
renvᴮᵒʳᵇ ň =  ň

Borbᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
Borbᴱᴿᴬ =  Envmᴱᴿᴬ (Excᴱᴿᴬ (¿ ℚ⁺ × Lft × SProp∞) ×ᴱᴿᴬ Excᴱᴿᴬ (𝔹 × Lft × SProp∞))
  Envᴮᵒʳᵇ λ E → lenvᴮᵒʳᵇ E , renvᴮᵒʳᵇ E

private variable
  E :  Envᴮᵒʳᵇ
  pˇ qˇ :  ¿ ℚ⁺
  b c :  𝔹
  α :  Lft
  P P' Q :  SProp∞

open ERA Borbᴱᴿᴬ public using () renaming (_↝_ to _↝ᴮᵒʳᵇ_)

abstract

  lenvᴮᵒʳᵇ-upd :  (E , #ˣ (pˇ , α , P) , εˣ)  ↝ᴮᵒʳᵇ
                    λ ((b , Q , _) : ∑ b , ∑ Q , E ≡ š (pˇ , b , α , P , Q)) →
                      š (qˇ , b , α , P' , Q) , #ˣ (qˇ , α , P') , εˣ
  lenvᴮᵒʳᵇ-upd {š _} (εˣ ,-) (refl , ✓#bαQ) =  (-, -, refl) , refl , ✓#bαQ

  renvᴮᵒʳᵇ-upd :  (E , εˣ , #ˣ (b , α , Q))  ↝ᴮᵒʳᵇ
                    λ ((pˇ , P , _) : ∑ pˇ , ∑ P , E ≡ š (pˇ , b , α , P , Q)) →
                      š (pˇ , c , α , P , Q) , εˣ , #ˣ (c , α , Q)
  renvᴮᵒʳᵇ-upd {š _} (-, εˣ) (✓#pˇαP , refl) =  (-, -, refl) , ✓#pˇαP , refl

-- Borᴱᴿᴬ :  Borrow ERA

module BndBor =  Syng.Model.ERA.Bnd Borbᴱᴿᴬ ň
  (λ (ň✓x , ň✓y) → ň-✓ˣ ň✓x , ň-✓ˣ ň✓y)
open BndBor public using () renaming (
  --  Borᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  Bndᴱᴿᴬ to Borᴱᴿᴬ;
  inj˙ to inj˙ᴮᵒʳ; inj˙-∙ to inj˙ᴮᵒʳ-∙;
  ↝ᴮⁿᵈ-new to ↝ᴮᵒʳ-new; inj˙-↝ᴮⁿᵈ to inj˙-↝ᴮᵒʳ)

open ERA Borᴱᴿᴬ public using () renaming (Res to Resᴮᵒʳ; _∙_ to _∙ᴮᵒʳ_;
  ε to εᴮᵒʳ; Env to Envᴮᵒʳ; _✓_ to _✓ᴮᵒʳ_; _↝_ to _↝ᴮᵒʳ_; ◠˜_ to ◠˜ᴮᵒʳ_;
  ↝-respʳ to ↝ᴮᵒʳ-respʳ; ↝-ε to ↝ᴮᵒʳ-ε)

-- Empty environment for Borᴱᴿᴬ

∅ᴮᵒʳ :  Envᴮᵒʳ
∅ᴮᵒʳ =  (λ _ → ň) , 0

-- Resource for the mutable borrow token

borᵐ :  ℕ →  Lft →  SProp∞ →  Resᴮᵒʳ
borᵐ i α P =  inj˙ᴮᵒʳ i (#ˣ (ň , α , P) , εˣ)

-- Resource for the open mutable borrow token

oborᵐ :  ℕ →  Lft →  ℚ⁺ →  SProp∞ →  Resᴮᵒʳ
oborᵐ i α p P =  inj˙ᴮᵒʳ i (#ˣ (š p , α , P) , εˣ)

-- Resource for the lending token

lend :  ℕ →  Lft →  SProp∞ →  Resᴮᵒʳ
lend i α P =  inj˙ᴮᵒʳ i (εˣ , #ˣ (tt , α , P))

private variable
  E˙ :  ℕ → Envᴮᵒʳᵇ
  i n :  ℕ
  p :  ℚ⁺

abstract

  -- ∅ᴮᵒʳ with εᴮᵒʳ is valid

  ∅ᴮᵒʳ-✓ε :  ∅ᴮᵒʳ ✓ᴮᵒʳ εᴮᵒʳ
  ∅ᴮᵒʳ-✓ε =  (λ _ _ → refl) ,-

  -- Create borᵐ and lend at a fresh index

  borᵐ-new :
    ((E˙ , n) , εᴮᵒʳ)  ↝ᴮᵒʳ λ (_ : ⊤₀) →
      (upd˙ n (š (ň , tt , α , P , P)) E˙ , ṡ n) , borᵐ n α P ∙ᴮᵒʳ lend n α P
  borᵐ-new =
    ↝ᴮᵒʳ-respʳ {a = εᴮᵒʳ} (◠˜ᴮᵒʳ inj˙ᴮᵒʳ-∙) $ ↝ᴮᵒʳ-new (refl , refl)

  -- Turn borᵐ into oborᵐ to update ¿ ℚ⁺ from ň to š p

  borᵐ-open :  ((E˙ , n) , borᵐ i α P)  ↝ᴮᵒʳ
    λ ((-, b , Q , _) :  i < n  ×  (∑ b , ∑ Q , E˙ i ≡ š (ň , b , α , P , Q))) →
    (upd˙ i (š (š p , b , α , P , Q)) E˙ , n) , oborᵐ i α p P
  borᵐ-open =  inj˙-↝ᴮᵒʳ (λ ()) lenvᴮᵒʳᵇ-upd

  -- Turn oborᵐ into borᵐ to update ¿ ℚ⁺ from š p to ň

  oborᵐ-close :  ((E˙ , n) , oborᵐ i α p P)  ↝ᴮᵒʳ
    λ ((-, b , Q , _) :
      i < n  ×  (∑ b , ∑ Q , E˙ i ≡ š (š p , b , α , P , Q))) →
    (upd˙ i (š (ň , b , α , P' , Q)) E˙ , n) , borᵐ i α P'
  oborᵐ-close =  inj˙-↝ᴮᵒʳ (λ ()) lenvᴮᵒʳᵇ-upd

  -- Consume lend to update 𝔹 from tt to ff

  lend-back :  ((E˙ , n) , lend i α Q)  ↝ᴮᵒʳ
    λ ((-, pˇ , P , _) :
      i < n  ×  (∑ pˇ , ∑ P , E˙ i ≡ š (pˇ , tt , α , P , Q))) →
    (upd˙ i (š (pˇ , ff , α , P , Q)) E˙ , n) , εᴮᵒʳ
  lend-back =  ↝ᴮᵒʳ-ε {a = lend _ _ _} {b˙ = λ _ → inj˙ᴮᵒʳ _ _} $
    inj˙-↝ᴮᵒʳ {bˣ = λ _ → εˣ , #ˣ _} (λ ()) renvᴮᵒʳᵇ-upd
