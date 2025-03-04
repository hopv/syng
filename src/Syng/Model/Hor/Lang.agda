--------------------------------------------------------------------------------
-- Language-specific lemmas on the weakest preconditions
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syng.Model.Hor.Lang where

open import Base.Level using (Level)
open import Base.Func using (_$_; _▷_; _›_)
open import Base.Few using (absurd)
open import Base.Eq using (refl; ◠_)
open import Base.Dec using (Inh; auto)
open import Base.Size using (𝕊; ∞; !; §_)
open import Base.Bool using (𝔹; tt; ff)
open import Base.Prod using (_,_; -,_)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Base.Sety using (Setʸ; ⸨_⸩ʸ)
open import Syng.Lang.Expr using (Type; Expr∞; Expr˂∞; ∇_; Val; V⇒E)
open import Syng.Lang.Ktxred using (Redex; ndᴿ; [_]ᴿ⟨_⟩; [_]ᴿ○; [_]ᴿ●; forkᴿ;
  Ktx; _ᴷ◁_; _ᴷ∘ᴷ_; val/ktxred; ᴷ∘ᴷ-ᴷ◁; val/ktxred-ĩ₀; val/ktxred-ktx)
open import Syng.Lang.Reduce using (nd⇒; []⇒; fork⇒; redᴷᴿ)
open import Syng.Model.Prop.Base using (SPropᵒ; substᵒ; _⊨_; ∀ᵒ∈-syntax; _∗ᵒ_;
  _-∗ᵒ_; ∗ᵒ-mono; ∗ᵒ-monoˡ; ∗ᵒ-monoʳ; ∗ᵒ-comm; ∗ᵒ?-intro; -∗ᵒ-monoʳ; -∗ᵒ-introˡ;
  -∗ᵒ-applyˡ; ∗ᵒThunkᵒ-out)
open import Syng.Model.Prop.Names using ([⊤]ᴺᵒ)
open import Syng.Model.Fupd.Interp using (⇛ˢ-mono; ⇛ᴺᵒ-mono; ⇛ˢ-intro; ⇛ˢ-join)
open import Syng.Model.Hor.Wp using (ᵃ⟨_⟩ᵒ; ⁺⟨_⟩ᴾᵒ; ⁺⟨_⟩ᵀᵒ; ⁺⟨_⟩∞ᵒ; ⟨_⟩ᴾᵒ;
  ⟨_⟩ᵀᵒ; ⟨_⟩∞ᵒ; ⟨_⟩ᴾᵒ˂; ⟨_⟩∞ᵒ˂ʳ; ⟨_⟩ᴾᵒ⊤; ⟨_⟩ᴾᵒ⊤˂; ⟨_⟩ᵀᵒ⊤; ⁺⟨⟩ᴾᵒ-val⁻¹;
  ⁺⟨⟩ᵀᵒ-val⁻¹; ⁺⟨⟩∞ᵒ-val⁻¹; ⁺⟨⟩ᴾᵒ-kr; ⁺⟨⟩ᵀᵒ-kr; ⁺⟨⟩∞ᵒ-kr; ⁺⟨⟩ᴾᵒ-kr⁻¹;
  ⁺⟨⟩ᵀᵒ-kr⁻¹; ⁺⟨⟩∞ᵒ-kr⁻¹; ⁺⟨⟩ᴾᵒ-mono; ⁺⟨⟩ᴾᵒ-size; ⟨¿⟩ᵀᵒ⊤˂-size; ⇛ᴺᵒ-⁺⟨⟩ᴾᵒ;
  ⇛ᴺᵒ-⁺⟨⟩ᵀᵒ; ⇛ᴺᵒ-⁺⟨⟩∞ᵒ)

private variable
  ł :  Level
  ι ι' :  𝕊
  b :  𝔹
  Xʸ :  Setʸ
  X :  Set₀
  v x :  X
  T U :  Type
  Pᵒ :  SPropᵒ ł
  Pᵒ˙ :  X →  SPropᵒ ł
  e :  Expr∞ T
  e˙ :  X →  Expr∞ T
  red :  Redex T
  K :  Ktx T U

--------------------------------------------------------------------------------
-- Language-specific lemmas on the weakest preconditions

abstract

  -- Compose ᵃ⟨⟩ᵒ and ⟨⟩ᴾ/ᵀᵒ
  -- The inner weakest precondition is under the thunk for ⟨⟩ᴾᵒ

  ᵃ⟨⟩ᴺᵒ-⟨⟩ᴾᵒ :  [⊤]ᴺᵒ -∗ᵒ ᵃ⟨ red ⟩ᵒ (λ v → [⊤]ᴺᵒ ∗ᵒ ⟨ K ᴷ◁ V⇒E v ⟩ᴾᵒ˂ ι Pᵒ˙)  ⊨
                  ⁺⟨ ĩ₁ (-, K , red) ⟩ᴾᵒ ι Pᵒ˙
  ᵃ⟨⟩ᴺᵒ-⟨⟩ᴾᵒ =  -∗ᵒ-monoʳ (λ big H → big H ▷ ⇛ˢ-mono λ ((-, -, redH⇒) , big) →
    (-, -, redᴷᴿ redH⇒) , λ{ _ eˇ H' b (redᴷᴿ eeˇH'⇐b) → big _ eˇ H'
    (-, eeˇH'⇐b) ▷ λ{ (-, (refl , refl) , big) →
    big ▷ ⇛ˢ-mono (∗ᵒ-monoʳ $ ∗ᵒ?-intro _) }}) › ⁺⟨⟩ᴾᵒ-kr

  ᵃ⟨⟩ᴺᵒ-⟨⟩ᵀᵒ :  [⊤]ᴺᵒ -∗ᵒ ᵃ⟨ red ⟩ᵒ (λ v → [⊤]ᴺᵒ ∗ᵒ ⟨ K ᴷ◁ V⇒E v ⟩ᵀᵒ ∞ Pᵒ˙)  ⊨
                  ⁺⟨ ĩ₁ (-, K , red) ⟩ᵀᵒ ∞ Pᵒ˙
  ᵃ⟨⟩ᴺᵒ-⟨⟩ᵀᵒ =  -∗ᵒ-monoʳ (λ big H → big H ▷ ⇛ˢ-mono λ ((-, -, redH⇒) , big) →
    (-, -, redᴷᴿ redH⇒) , λ{ _ eˇ H' b (redᴷᴿ eeˇH'⇐b) →
    big _ eˇ H' (-, eeˇH'⇐b) ▷ λ{ (-, (refl , refl) , big) →
    big ▷ ⇛ˢ-mono (∗ᵒ-monoʳ $ §_ › ∗ᵒ?-intro _) }}) › ⁺⟨⟩ᵀᵒ-kr

  -- Compose ᵃ⟨⟩ᵒ and ⟨⟩∞ᵒ

  ᵃ⟨⟩ᴺᵒ-⟨⟩∞ᵒ :  [⊤]ᴺᵒ -∗ᵒ ᵃ⟨ red ⟩ᵒ (λ v → [⊤]ᴺᵒ ∗ᵒ ⟨ K ᴷ◁ V⇒E v ⟩∞ᵒ ∞ ι)  ⊨
                  ⁺⟨ ĩ₁ (-, K , red) ⟩∞ᵒ ∞ ι
  ᵃ⟨⟩ᴺᵒ-⟨⟩∞ᵒ =  -∗ᵒ-monoʳ (λ big H → big H ▷ ⇛ˢ-mono λ ((-, -, redH⇒) , big) →
    (-, -, redᴷᴿ redH⇒) , λ _ eˇ H' → λ{
    ff (redᴷᴿ eeˇH'⇐○) → big _ eˇ H' (-, eeˇH'⇐○) ▷
      λ{ (-, (refl , refl) , big) → big ▷
      ⇛ˢ-mono (∗ᵒ-monoʳ $ §_ › ∗ᵒ?-intro _) };
    tt (redᴷᴿ eeˇH'⇐●) → big _ eˇ H' (-, eeˇH'⇐●) ▷
      λ{ (-, (refl , refl) , big) → big ▷
      ⇛ˢ-mono (∗ᵒ-monoʳ $ (λ big → λ{ .! → big }) › ∗ᵒ?-intro _) }}) › ⁺⟨⟩∞ᵒ-kr

  -- Bind for ⟨⟩ᴾ/ᵀᵒ

  ⟨⟩ᴾᵒ-bind :  ⟨ e ⟩ᴾᵒ ι (λ v → ⟨ K ᴷ◁ V⇒E v ⟩ᴾᵒ ι Pᵒ˙)  ⊨  ⟨ K ᴷ◁ e ⟩ᴾᵒ ι Pᵒ˙
  ⟨⟩ᴾᵒ-bind {e = e} {K = K}
    with val/ktxred e | val/ktxred-ĩ₀ {e = e} | val/ktxred-ktx {e = e}
  … | ĩ₀ _ | ⇒e⇒v | _  rewrite ⇒e⇒v refl =  ⁺⟨⟩ᴾᵒ-val⁻¹ › ⇛ᴺᵒ-⁺⟨⟩ᴾᵒ
  … | ĩ₁ (-, K' , _) | _ | ⇒Ke≡KK'red  rewrite ⇒Ke≡KK'red {K = K} refl =
    ⁺⟨⟩ᴾᵒ-kr⁻¹ › -∗ᵒ-monoʳ (λ big H → big H ▷ ⇛ˢ-mono
    λ{ ((-, -, redᴷᴿ redH⇒) , big) → (-, -, redᴷᴿ redH⇒) ,
    λ{ _ eˇ H' b (redᴷᴿ e'eˇH'⇐b) → big _ eˇ H' b (redᴷᴿ e'eˇH'⇐b) ▷ ⇛ˢ-mono
    (∗ᵒ-monoʳ $ ∗ᵒ-monoˡ λ big → λ{ .! {ι'} → big .! ▷
    ⁺⟨⟩ᴾᵒ-mono (λ _ → ⁺⟨⟩ᴾᵒ-size) ▷ ⟨⟩ᴾᵒ-bind ▷
    substᵒ (λ e⁺ → ⟨ e⁺ ⟩ᴾᵒ ι' _) (◠ ᴷ∘ᴷ-ᴷ◁ {K = K}) }) }}) › ⁺⟨⟩ᴾᵒ-kr

  ⟨⟩ᵀᵒ-bind :  ⟨ e ⟩ᵀᵒ ι (λ v → ⟨ K ᴷ◁ V⇒E v ⟩ᵀᵒ ∞ Pᵒ˙)  ⊨  ⟨ K ᴷ◁ e ⟩ᵀᵒ ∞ Pᵒ˙
  ⟨⟩ᵀᵒ-bind {e = e} {K = K}
    with val/ktxred e | val/ktxred-ĩ₀ {e = e} | val/ktxred-ktx {e = e}
  … | ĩ₀ _ | ⇒e⇒v | _  rewrite ⇒e⇒v refl =  ⁺⟨⟩ᵀᵒ-val⁻¹ › ⇛ᴺᵒ-⁺⟨⟩ᵀᵒ
  … | ĩ₁ (-, K' , _) | _ | ⇒Ke≡KK'red  rewrite ⇒Ke≡KK'red {K = K} refl =
    ⁺⟨⟩ᵀᵒ-kr⁻¹ › -∗ᵒ-monoʳ (λ big H → big H ▷ ⇛ˢ-mono λ{
    ((-, -, redᴷᴿ redH⇒) , big) → (-, -, redᴷᴿ redH⇒) ,
    λ{ _ eˇ H' b (redᴷᴿ e'eˇH'⇐b) → big _ eˇ H' b (redᴷᴿ e'eˇH'⇐b) ▷ ⇛ˢ-mono
    (∗ᵒ-monoʳ $ ∗ᵒ-monoʳ (⟨¿⟩ᵀᵒ⊤˂-size {ι = ∞} {eˇ = eˇ}) ›
    ∗ᵒ-monoˡ λ{ (§ big) → § (⟨⟩ᵀᵒ-bind big ▷
    substᵒ (λ e⁺ → ⟨ e⁺ ⟩ᵀᵒ ∞ _) (◠ ᴷ∘ᴷ-ᴷ◁ {K = K})) }) }}) › ⁺⟨⟩ᵀᵒ-kr

  ⟨⟩∞ᵒ-bind :  ⟨ e ⟩∞ᵒ ι ι'  ⊨  ⟨ K ᴷ◁ e ⟩∞ᵒ ∞ ι'
  ⟨⟩∞ᵒ-bind {e = e} {ι' = ι'} {K = K}
    with val/ktxred e | val/ktxred-ĩ₀ {e = e} | val/ktxred-ktx {e = e}
  … | ĩ₀ _ | ⇒e⇒v | _  rewrite ⇒e⇒v refl =
    ⁺⟨⟩∞ᵒ-val⁻¹ › ⇛ᴺᵒ-mono absurd › ⇛ᴺᵒ-⁺⟨⟩∞ᵒ
  … | ĩ₁ (-, K' , _) | _ | ⇒Ke≡KK'red  rewrite ⇒Ke≡KK'red {K = K} refl =
    ⁺⟨⟩∞ᵒ-kr⁻¹ › -∗ᵒ-monoʳ (λ big H → big H ▷ ⇛ˢ-mono λ{
    ((-, -, redᴷᴿ redH⇒) , big) → (-, -, redᴷᴿ redH⇒) , λ _ eˇ H' → λ{
    ff (redᴷᴿ e'eˇH'⇐○) → big _ eˇ H' ff (redᴷᴿ e'eˇH'⇐○) ▷ ⇛ˢ-mono
      (∗ᵒ-monoʳ $ ∗ᵒ-monoʳ (⟨¿⟩ᵀᵒ⊤˂-size {ι = ∞} {eˇ = eˇ}) ›
      ∗ᵒ-monoˡ λ{ (§ big) → § (⟨⟩∞ᵒ-bind {K = K} big ▷
      substᵒ (λ e⁺ → ⟨ e⁺ ⟩∞ᵒ ∞ ι') (◠ ᴷ∘ᴷ-ᴷ◁ {K = K})) });
    tt (redᴷᴿ e'eˇH'⇐●) → big _ eˇ H' tt (redᴷᴿ e'eˇH'⇐●) ▷ ⇛ˢ-mono
      (∗ᵒ-monoʳ $ ∗ᵒ-monoʳ (⟨¿⟩ᵀᵒ⊤˂-size {ι = ∞} {eˇ = eˇ}) ›
      ∗ᵒ-monoˡ λ big → λ{ .! {ι'⁻} → big .! ▷ ⟨⟩∞ᵒ-bind {K = K} ▷
      substᵒ (λ e⁺ → ⟨ e⁺ ⟩∞ᵒ ∞ ι'⁻) (◠ ᴷ∘ᴷ-ᴷ◁ {K = K}) }) }}) › ⁺⟨⟩∞ᵒ-kr

  ⟨⟩ᵀᵒ-⟨⟩∞ᵒ-bind :  ⟨ e ⟩ᵀᵒ ι (λ v → ⟨ K ᴷ◁ V⇒E v ⟩∞ᵒ ∞ ι')  ⊨
                    ⟨ K ᴷ◁ e ⟩∞ᵒ ∞ ι'
  ⟨⟩ᵀᵒ-⟨⟩∞ᵒ-bind {e = e} {K = K} {ι' = ι'}
    with val/ktxred e | val/ktxred-ĩ₀ {e = e} | val/ktxred-ktx {e = e}
  … | ĩ₀ _ | ⇒e⇒v | _  rewrite ⇒e⇒v refl =  ⁺⟨⟩ᵀᵒ-val⁻¹ › ⇛ᴺᵒ-⁺⟨⟩∞ᵒ
  … | ĩ₁ (-, K' , _) | _ | ⇒Ke≡KK'red  rewrite ⇒Ke≡KK'red {K = K} refl =
    ⁺⟨⟩ᵀᵒ-kr⁻¹ › -∗ᵒ-monoʳ (λ big H → big H ▷ ⇛ˢ-mono λ{
    ((-, -, redᴷᴿ redH⇒) , big) → (-, -, redᴷᴿ redH⇒) , λ _ eˇ H' → λ{
    ff (redᴷᴿ e'eˇH'⇐○) → big _ eˇ H' _ (redᴷᴿ e'eˇH'⇐○) ▷ ⇛ˢ-mono
      (∗ᵒ-monoʳ $ ∗ᵒ-monoʳ (⟨¿⟩ᵀᵒ⊤˂-size {ι = ∞} {eˇ = eˇ}) ›
      ∗ᵒ-monoˡ λ{ (§ big) → § (⟨⟩ᵀᵒ-⟨⟩∞ᵒ-bind big ▷
      substᵒ (λ e⁺ → ⟨ e⁺ ⟩∞ᵒ ∞ ι') (◠ ᴷ∘ᴷ-ᴷ◁ {K = K})) });
    tt (redᴷᴿ e'eˇH'⇐●) → big _ eˇ H' _ (redᴷᴿ e'eˇH'⇐●) ▷ ⇛ˢ-mono
      (∗ᵒ-monoʳ $ ∗ᵒ-monoʳ (⟨¿⟩ᵀᵒ⊤˂-size {ι = ∞} {eˇ = eˇ}) ›
      ∗ᵒ-monoˡ λ{ (§ big) → λ{ .! {ι'⁻} → big ▷ ⟨⟩ᵀᵒ-⟨⟩∞ᵒ-bind {K = K} ▷
      substᵒ (λ e⁺ → ⟨ e⁺ ⟩∞ᵒ ∞ ι'⁻) (◠ ᴷ∘ᴷ-ᴷ◁ {K = K}) }}) }}) › ⁺⟨⟩∞ᵒ-kr

  -- nd by ᵃ⟨⟩ᵒ

  ᵃ⟨⟩ᵒ-nd :  {{Inh ⸨ Xʸ ⸩ʸ}} →  Pᵒ ⊨ ᵃ⟨ ndᴿ {Xʸ} ⟩ᵒ λ _ → Pᵒ
  ᵃ⟨⟩ᵒ-nd {{InhX}} Pa H =  ⇛ˢ-intro ((-, -, nd⇒ $ auto {{InhX}}) ,
    λ{ _ _ _ (-, nd⇒ _) → -, (refl , refl) , ⇛ˢ-intro Pa })

  -- Pure reduction by ⁺⟨⟩ᴾ/ᵀᵒ
  -- The premise is under the thunk for ⁺⟨⟩ᴾᵒ

  ⁺⟨⟩ᴾᵒ-[] :  ⟨ K ᴷ◁ e ⟩ᴾᵒ˂ ι Pᵒ˙  ⊨  ⁺⟨ ĩ₁ (-, K , [ e ]ᴿ⟨ b ⟩) ⟩ᴾᵒ ι Pᵒ˙
  ⁺⟨⟩ᴾᵒ-[] =  -∗ᵒ-introˡ (λ _ big _ → ⇛ˢ-intro ((-, -, redᴷᴿ []⇒) ,
    λ{ _ _ _ _ (redᴷᴿ []⇒) → ⇛ˢ-intro $ big ▷ ∗ᵒ-monoʳ (∗ᵒ?-intro _) })) ›
    ⁺⟨⟩ᴾᵒ-kr

  ⁺⟨⟩ᵀᵒ-[] :  ⟨ K ᴷ◁ e ⟩ᵀᵒ ι Pᵒ˙  ⊨  ⁺⟨ ĩ₁ (-, K , [ e ]ᴿ⟨ b ⟩) ⟩ᵀᵒ ∞ Pᵒ˙
  ⁺⟨⟩ᵀᵒ-[] =  -∗ᵒ-introˡ (λ _ big _ → ⇛ˢ-intro ((-, -, redᴷᴿ []⇒) ,
    λ{ _ _ _ _ (redᴷᴿ []⇒) → ⇛ˢ-intro $ big ▷ ∗ᵒ-monoʳ (§_ › ∗ᵒ?-intro _) })) ›
    ⁺⟨⟩ᵀᵒ-kr

  -- Pure reduction by ⁺⟨⟩∞ᵒ
  -- The premise is under the thunk when the reduction triggers an event

  ⁺⟨⟩∞ᵒ-[]○ :  ⟨ K ᴷ◁ e ⟩∞ᵒ ι ι'  ⊨  ⁺⟨ ĩ₁ (-, K , [ e ]ᴿ○) ⟩∞ᵒ ∞ ι'
  ⁺⟨⟩∞ᵒ-[]○ =  -∗ᵒ-introˡ (λ _ big _ → ⇛ˢ-intro ((-, -, redᴷᴿ []⇒) ,
    λ{ _ _ _ ff (redᴷᴿ []⇒) → ⇛ˢ-intro $ big ▷ ∗ᵒ-monoʳ (§_ › ∗ᵒ?-intro _) })) ›
    ⁺⟨⟩∞ᵒ-kr

  ⁺⟨⟩∞ᵒ-[]● :  ⟨ K ᴷ◁ e ⟩∞ᵒ˂ʳ ι'  ⊨  ⁺⟨ ĩ₁ (-, K , [ e ]ᴿ●) ⟩∞ᵒ ι ι'
  ⁺⟨⟩∞ᵒ-[]● =  -∗ᵒ-introˡ (λ _ big _ → ⇛ˢ-intro ((-, -, redᴷᴿ []⇒) ,
    λ{ _ _ _ tt (redᴷᴿ []⇒) → ⇛ˢ-intro $ big ▷ ∗ᵒ-monoʳ (∗ᵒ?-intro _) })) ›
    ⁺⟨⟩∞ᵒ-kr

  -- fork by ⁺⟨⟩ᴾ/ᵀᵒ / ⁺⟨⟩∞ᵒ
  -- The premise is under the thunk for ⁺⟨⟩ᴾᵒ

  ⁺⟨⟩ᴾᵒ-fork :  ⟨ e ⟩ᴾᵒ⊤˂ ι  ∗ᵒ  ⟨ K ᴷ◁ ∇ _ ⟩ᴾᵒ˂ ι Pᵒ˙  ⊨
                  ⁺⟨ ĩ₁ (-, K , forkᴿ e) ⟩ᴾᵒ ι Pᵒ˙
  ⁺⟨⟩ᴾᵒ-fork =  -∗ᵒ-introˡ (λ _ big _ → ⇛ˢ-intro ((-, -, redᴷᴿ fork⇒) ,
    λ{ _ _ _ _ (redᴷᴿ fork⇒) → ⇛ˢ-intro $ big ▷ ∗ᵒ-monoʳ ∗ᵒ-comm })) › ⁺⟨⟩ᴾᵒ-kr

  ⁺⟨⟩ᵀᵒ-fork :  ⟨ e ⟩ᵀᵒ⊤ ι'  ∗ᵒ  ⟨ K ᴷ◁ ∇ _ ⟩ᵀᵒ ι Pᵒ˙  ⊨
                  ⁺⟨ ĩ₁ (-, K , forkᴿ e) ⟩ᵀᵒ ∞ Pᵒ˙
  ⁺⟨⟩ᵀᵒ-fork =  -∗ᵒ-introˡ (λ _ big _ → ⇛ˢ-intro ((-, -, redᴷᴿ fork⇒) ,
    λ{ _ _ _ _ (redᴷᴿ fork⇒) → ⇛ˢ-intro $ big ▷
    ∗ᵒ-monoʳ (∗ᵒ-comm › ∗ᵒ-mono §_ $ §_ {ι = ∞}) })) › ⁺⟨⟩ᵀᵒ-kr

  ⁺⟨⟩∞ᵒ-fork :  ⟨ e ⟩ᵀᵒ⊤ ι  ∗ᵒ  ⟨ K ᴷ◁ ∇ _ ⟩∞ᵒ ι ι'  ⊨
                  ⁺⟨ ĩ₁ (-, K , forkᴿ e) ⟩∞ᵒ ∞ ι'
  ⁺⟨⟩∞ᵒ-fork =  -∗ᵒ-introˡ (λ _ big _ → ⇛ˢ-intro ((-, -, redᴷᴿ fork⇒) ,
    λ{ _ _ _ ff (redᴷᴿ fork⇒) → ⇛ˢ-intro $ big ▷
    ∗ᵒ-monoʳ (∗ᵒ-comm › ∗ᵒ-mono §_ $ §_ {ι = ∞}) })) › ⁺⟨⟩∞ᵒ-kr
