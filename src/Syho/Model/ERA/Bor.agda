--------------------------------------------------------------------------------
-- Borrow ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Bor where

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
open import Syho.Logic.Prop using (Lft; Prop∞)
open import Syho.Model.ERA.Base using (ERA; _×ᴱᴿᴬ_; Envmᴱᴿᴬ)
open import Syho.Model.ERA.Exc using (Excᴱᴿᴬ; εˣ; #ˣ_; ň-✓ˣ)
import Syho.Model.ERA.Bnd

--------------------------------------------------------------------------------
-- Borᴱᴿᴬ :  Borrow ERA

-- Borbᴱᴿᴬ :  Borrow box ERA

Envᴮᵒʳᵇ :  Set₁
Envᴮᵒʳᵇ =  ¿ (¿ ℚ⁺ × 𝔹 × Lft × Prop∞)

lenvᴮᵒʳᵇ :  Envᴮᵒʳᵇ →  ¿ (¿ ℚ⁺ × Lft × Prop∞)
lenvᴮᵒʳᵇ (š (pˇ , b , α , P)) =  š (pˇ , α , P)
lenvᴮᵒʳᵇ ň =  ň

renvᴮᵒʳᵇ :  Envᴮᵒʳᵇ →  ¿ (𝔹 × Lft × Prop∞)
renvᴮᵒʳᵇ (š (pˇ , b , α , P)) =  š (b , α , P)
renvᴮᵒʳᵇ ň =  ň

Borbᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
Borbᴱᴿᴬ =  Envmᴱᴿᴬ (Excᴱᴿᴬ (¿ ℚ⁺ × Lft × Prop∞) ×ᴱᴿᴬ Excᴱᴿᴬ (𝔹 × Lft × Prop∞))
  Envᴮᵒʳᵇ λ E → lenvᴮᵒʳᵇ E , renvᴮᵒʳᵇ E

private variable
  E :  Envᴮᵒʳᵇ
  pˇ qˇ :  ¿ ℚ⁺
  b c :  𝔹
  α :  Lft
  P :  Prop∞

open ERA Borbᴱᴿᴬ public using () renaming (_↝_ to _↝ᴮᵒʳᵇ_)

abstract

  lenvᴮᵒʳᵇ-upd :  (E , #ˣ (pˇ , α , P) , εˣ)  ↝ᴮᵒʳᵇ
                    λ ((b ,-) : ∑ b , E ≡ š (pˇ , b , α , P)) →
                      š (qˇ , b , α , P) , #ˣ (qˇ , α , P) , εˣ
  lenvᴮᵒʳᵇ-upd {š _} (εˣ ,-) (refl , ✓#bαP) =  (-, refl) , refl , ✓#bαP

  renvᴮᵒʳᵇ-upd :  (E , εˣ , #ˣ (b , α , P))  ↝ᴮᵒʳᵇ
                    λ ((pˇ ,-) : ∑ pˇ , E ≡ š (pˇ , b , α , P)) →
                      š (pˇ , c , α , P) , εˣ , #ˣ (c , α , P)
  renvᴮᵒʳᵇ-upd {š _} (-, εˣ) (✓#pˇαP , refl) =  (-, refl) , ✓#pˇαP , refl

-- Borᴱᴿᴬ :  Borrow ERA

module BndBor =  Syho.Model.ERA.Bnd Borbᴱᴿᴬ ň
  (λ (ň✓x , ň✓y) → ň-✓ˣ ň✓x , ň-✓ˣ ň✓y)
open BndBor public using () renaming (
  --  Borᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
  Bndᴱᴿᴬ to Borᴱᴿᴬ;
  inj˙ to inj˙ᴮᵒʳ; inj˙-∙ to inj˙ᴮᵒʳ-∙;
  ↝ᴮⁿᵈ-new to ↝ᴮᵒʳ-new; inj˙-↝ᴮⁿᵈ to inj˙-↝ᴮᵒʳ)

open ERA Borᴱᴿᴬ public using () renaming (Res to Resᴮᵒʳ; _∙_ to _∙ᴮᵒʳ_;
  ε to εᴮᵒʳ; Env to Envᴮᵒʳ; _✓_ to _✓ᴮᵒʳ_; _↝_ to _↝ᴮᵒʳ_; ◠˜_ to ◠˜ᴮᵒʳ_;
  ε-min to εᴮᵒʳ-min; ↝-respʳ to ↝ᴮᵒʳ-respʳ; ↝-monoʳ to ↝ᴮᵒʳ-monoʳ)

-- Resource for the mutable borrow token

borᵐ :  ℕ →  Lft →  Prop∞ →  Resᴮᵒʳ
borᵐ i α P =  inj˙ᴮᵒʳ i (#ˣ (ň , α , P) , εˣ)

-- Resource for the open mutable borrow token

oborᵐ :  ℕ →  Lft →  ℚ⁺ →  Prop∞ →  Resᴮᵒʳ
oborᵐ i α p P =  inj˙ᴮᵒʳ i (#ˣ (š p , α , P) , εˣ)

-- Resource for the lending token

lend :  ℕ →  Lft →  Prop∞ →  Resᴮᵒʳ
lend i α P =  inj˙ᴮᵒʳ i (εˣ , #ˣ (tt , α , P))

private variable
  E˙ :  ℕ → Envᴮᵒʳᵇ
  i n :  ℕ
  p :  ℚ⁺

abstract

  -- Empty environment for Borᴱᴿᴬ

  empᴮᵒʳ :  Envᴮᵒʳ
  empᴮᵒʳ =  (λ _ → ň) , 0

  -- empᴮᵒʳ with εᴮᵒʳ is valid

  empᴮᵒʳ-✓ε :  empᴮᵒʳ ✓ᴮᵒʳ εᴮᵒʳ
  empᴮᵒʳ-✓ε =  (λ _ _ → refl) ,-

  -- Create borᵐ and lend at a fresh new index

  borᵐ-lend-new :
    ((E˙ , n) , εᴮᵒʳ)  ↝ᴮᵒʳ λ (_ : ⊤₀) →
      (upd˙ n (š (ň , tt , α , P)) E˙ , ṡ n) , borᵐ n α P ∙ᴮᵒʳ lend n α P
  borᵐ-lend-new =
    ↝ᴮᵒʳ-respʳ {a = εᴮᵒʳ} (◠˜ᴮᵒʳ inj˙ᴮᵒʳ-∙) $ ↝ᴮᵒʳ-new (refl , refl)

  -- Turn borᵐ into oborᵐ to update ¿ ℚ⁺ from ň to š p

  borᵐ-open :
    ((E˙ , n) , borᵐ i α P)  ↝ᴮᵒʳ
      λ ((-, (b ,-)) :  i < n  ×  (∑ b , E˙ i ≡ š (ň , b , α , P))) →
        (upd˙ i (š (š p , b , α , P)) E˙ , n) , oborᵐ i α p P
  borᵐ-open =  inj˙-↝ᴮᵒʳ (λ ()) lenvᴮᵒʳᵇ-upd

  -- Turn oborᵐ into borᵐ to update ¿ ℚ⁺ from š p to ň

  oborᵐ-close :
    ((E˙ , n) , oborᵐ i α p P)  ↝ᴮᵒʳ
      λ ((-, (b ,-)) :  i < n  ×  (∑ b , E˙ i ≡ š (š p , b , α , P))) →
        (upd˙ i (š (ň , b , α , P)) E˙ , n) , borᵐ i α P
  oborᵐ-close =  inj˙-↝ᴮᵒʳ (λ ()) lenvᴮᵒʳᵇ-upd

  -- Consume lend to update 𝔹 from tt to ff

  lend-back :
    ((E˙ , n) , lend i α P)  ↝ᴮᵒʳ
      λ ((-, (pˇ ,-)) :  i < n  ×  (∑ pˇ , E˙ i ≡ š (pˇ , tt , α , P))) →
        (upd˙ i (š (pˇ , ff , α , P)) E˙ , n) , εᴮᵒʳ
  lend-back =  ↝ᴮᵒʳ-monoʳ {b˙ = λ _ → inj˙ᴮᵒʳ _ _} {a = lend _ _ _} εᴮᵒʳ-min $
    inj˙-↝ᴮᵒʳ {bˣ = λ _ → εˣ , #ˣ _} (λ ()) renvᴮᵒʳᵇ-upd
