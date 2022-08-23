--------------------------------------------------------------------------------
-- Prove semantic soundness of the pure sequent
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Pure where

open import Base.Size using (Size; ∞)
open import Base.Func using (_$_; _›_; id)
open import Base.Thunk using (!)
open import Base.Few using (0₂; 1₂; binary; absurd)
open import Base.Prod using (_,_; proj₀; proj₁)
open import Syho.Logic.Prop using (Prop'; ∀₁˙; ∃₁˙; _∧_; _→'_; _∗_; _-∗_; ⤇_;
  □_; ○_; _↪[_]⇛_; _↪⟨_⟩ᴾ_; _↪⟨_⟩ᵀ[_]_; _↦⟨_⟩_; Free; Basic; ∀₁-Basic; ∃₁-Basic;
  →-Basic; ∗-Basic; -∗-Basic; ⤇-Basic; □-Basic; ↦⟨⟩-Basic; Free-Basic)
open import Syho.Logic.Core using (_⊢[_]_; ⊢-refl; _»_; ∀₁-intro; ∃₁-elim;
  ∀₁-elim; ∃₁-intro; choice₁; →-intro; →-elim; ⊤∗-elim; ⊤∗-intro; ∗-comm;
  ∗-assocˡ; ∗-monoˡ; -∗-intro; -∗-elim; ⤇-mono; ⤇-intro; ⤇-join; ⤇-eatˡ;
  ⤇-∃-out; □-mono; □-elim; □-dup; □ˡ-∧⇒∗; □-∀-in; □-∃-out)
open import Syho.Logic.Ind using (○-mono; ○-eatˡ; ↪⇛-suc; ↪⇛-eatˡ⁻ˡᵘ; ↪⇛-eatˡ⁻ʳ;
  ↪⇛-monoʳᵘ; ↪⇛-frameˡ; ○⇒↪⇛; ↪⟨⟩ᴾ-eatˡ⁻ˡᵘ; ↪⟨⟩ᴾ-eatˡ⁻ʳ; ↪⟨⟩ᴾ-monoʳᵘ;
  ↪⟨⟩ᴾ-frameˡ; ○⇒↪⟨⟩ᴾ; ↪⟨⟩ᵀ-suc; ↪⟨⟩ᵀ-eatˡ⁻ˡᵘ; ↪⟨⟩ᵀ-eatˡ⁻ʳ; ↪⟨⟩ᵀ-monoʳᵘ;
  ↪⟨⟩ᵀ-frameˡ; ○⇒↪⟨⟩ᵀ)
open import Syho.Model.ERA.Glob using (Globᴱᴿᴬ)
open import Syho.Model.Prop using (Propᵒ; Monoᵒ; _⊨✓_; _⊨_; ∀₁ᵒ-syntax;
  ∃₁ᵒ-syntax; ⊤ᵒ; _→ᵒ_; _∗ᵒ_; _-∗ᵒ_; ⤇ᵒ_; □ᵒ_; ⊨⇒⊨✓; ∀₁ᵒ-Mono; ∀₁ᵒ-mono;
  ∃₁ᵒ-Mono; ∃₁ᵒ-mono; →ᵒ-Mono; →ᵒ-mono; →ᵒ-intro; →ᵒ-elim; ∗ᵒ-Mono; ∗ᵒ-mono;
  ∗ᵒ-monoˡ; ∗ᵒ-mono✓ˡ; ?∗ᵒ-intro; ∗ᵒ-elimʳ; ∗ᵒ-comm; ∗ᵒ-assocˡ; -∗ᵒ-Mono;
  -∗ᵒ-mono; -∗ᵒ-intro; -∗ᵒ-elim; ⤇ᵒ-Mono; ⤇ᵒ-mono; ⤇ᵒ-mono✓; ⤇ᵒ-intro; ⤇ᵒ-join;
  ⤇ᵒ-eatˡ; ⤇ᵒ-∃₁ᵒ-out; □ᵒ-Mono; □ᵒ-mono; □ᵒ-mono✓; □ᵒ-elim; □ᵒ-dup; □ᵒˡ-×ᵒ⇒∗ᵒ)
open import Syho.Model.Ind using (○ᵒ_; _↪[_]⇛ᵒ_; _↪⟨_⟩ᴾᵒ_; _↪⟨_⟩ᵀ[_]ᵒ_; ○ᵒ-Mono;
  ○ᵒ-mono; ○ᵒ-eatˡ; ↪⇛ᵒ-Mono; ↪⇛ᵒ-suc; ↪⇛ᵒ-eatˡ⁻ˡᵘ; ↪⇛ᵒ-eatˡ⁻ʳ; ↪⇛ᵒ-monoʳᵘ;
  ↪⇛ᵒ-frameˡ; ○ᵒ⇒↪⇛ᵒ; ↪⟨⟩ᴾᵒ-Mono; ↪⟨⟩ᴾᵒ-eatˡ⁻ˡᵘ; ↪⟨⟩ᴾᵒ-eatˡ⁻ʳ; ↪⟨⟩ᴾᵒ-monoʳᵘ;
  ↪⟨⟩ᴾᵒ-frameˡ; ○ᵒ⇒↪⟨⟩ᴾᵒ; ↪⟨⟩ᵀᵒ-Mono; ↪⟨⟩ᵀᵒ-suc; ↪⟨⟩ᵀᵒ-eatˡ⁻ˡᵘ; ↪⟨⟩ᵀᵒ-eatˡ⁻ʳ;
  ↪⟨⟩ᵀᵒ-monoʳᵘ; ↪⟨⟩ᵀᵒ-frameˡ; ○ᵒ⇒↪⟨⟩ᵀᵒ)
open import Syho.Model.Basic using (⸨_⸩ᴮ)

private variable
  P Q R S T :  Prop' ∞

--------------------------------------------------------------------------------
-- ⸨ ⸩ :  Interpreting propositions

⸨_⸩ :  Prop' ∞ →  Propᵒ
⸨ ∀₁˙ P˙ ⸩ =  ∀₁ᵒ x , ⸨ P˙ x ⸩
⸨ ∃₁˙ P˙ ⸩ =  ∃₁ᵒ x , ⸨ P˙ x ⸩
⸨ P →' Q ⸩ =  ⸨ P ⸩ →ᵒ ⸨ Q ⸩
⸨ P ∗ Q ⸩ =  ⸨ P ⸩ ∗ᵒ ⸨ Q ⸩
⸨ P -∗ Q ⸩ =  ⸨ P ⸩ -∗ᵒ ⸨ Q ⸩
⸨ ⤇ P ⸩ =  ⤇ᵒ ⸨ P ⸩
⸨ □ P ⸩ =  □ᵒ ⸨ P ⸩
⸨ ○ P˂ ⸩ =  ○ᵒ P˂ .!
⸨ P˂ ↪[ i ]⇛ Q˂ ⸩ =  P˂ .! ↪[ i ]⇛ᵒ Q˂ .!
⸨ P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ ⸩ =  P˂ .! ↪⟨ e ⟩ᴾᵒ λ v → Q˂ᵛ v .!
⸨ P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ ⸩ =  P˂ .! ↪⟨ e ⟩ᵀ[ i ]ᵒ λ v → Q˂ᵛ v .!
⸨ _ ↦⟨ _ ⟩ _ ⸩ =  ⊤ᵒ  -- For now
⸨ Free _ _ ⸩ =  ⊤ᵒ  -- For now

abstract

  -- ⸨ ⸩ᴮ agrees with ⸨ ⸩
  -- ⸨⸩-ᴮ⇒ and ⸨⸩-⇒ᴮ are mutually recursive

  ⸨⸩-ᴮ⇒ :  {{_ : Basic P}} →  ⸨ P ⸩ᴮ ⊨ ⸨ P ⸩
  ⸨⸩-⇒ᴮ :  {{_ : Basic P}} →  ⸨ P ⸩ ⊨ ⸨ P ⸩ᴮ

  ⸨⸩-ᴮ⇒ {{∀₁-Basic BasicP˙}} {a} =  ∀₁ᵒ-mono (λ x → ⸨⸩-ᴮ⇒ {{BasicP˙ x}} {a}) {a}
  ⸨⸩-ᴮ⇒ {{∃₁-Basic BasicP˙}} {a} =  ∃₁ᵒ-mono (λ x → ⸨⸩-ᴮ⇒ {{BasicP˙ x}} {a}) {a}
  ⸨⸩-ᴮ⇒ {{→-Basic {P} {Q}}} =  →ᵒ-mono (⸨⸩-⇒ᴮ {P}) (⸨⸩-ᴮ⇒ {Q})
  ⸨⸩-ᴮ⇒ {{∗-Basic {P} {Q}}} =  ∗ᵒ-mono (⸨⸩-ᴮ⇒ {P}) (⸨⸩-ᴮ⇒ {Q})
  ⸨⸩-ᴮ⇒ {{ -∗-Basic {P} {Q}}} =  -∗ᵒ-mono (⸨⸩-⇒ᴮ {P}) (λ{a} → ⸨⸩-ᴮ⇒ {Q} {a})
  ⸨⸩-ᴮ⇒ {{⤇-Basic {P}}} =  ⤇ᵒ-mono (⸨⸩-ᴮ⇒ {P})
  ⸨⸩-ᴮ⇒ {{□-Basic {P}}} =  □ᵒ-mono (λ{a} → ⸨⸩-ᴮ⇒ {P} {a})
  ⸨⸩-ᴮ⇒ {{↦⟨⟩-Basic}} =  _
  ⸨⸩-ᴮ⇒ {{Free-Basic}} =  _

  ⸨⸩-⇒ᴮ {{∀₁-Basic BasicP˙}} =  ∀₁ᵒ-mono (λ x {a} → ⸨⸩-⇒ᴮ {{BasicP˙ x}} {a})
  ⸨⸩-⇒ᴮ {{∃₁-Basic BasicP˙}} =  ∃₁ᵒ-mono (λ x {a} → ⸨⸩-⇒ᴮ {{BasicP˙ x}} {a})
  ⸨⸩-⇒ᴮ {{→-Basic {P} {Q}}} =  →ᵒ-mono (⸨⸩-ᴮ⇒ {P}) (⸨⸩-⇒ᴮ {Q})
  ⸨⸩-⇒ᴮ {{∗-Basic {P} {Q}}} =  ∗ᵒ-mono (⸨⸩-⇒ᴮ {P}) (⸨⸩-⇒ᴮ {Q})
  ⸨⸩-⇒ᴮ {{ -∗-Basic {P} {Q}}} =  -∗ᵒ-mono (⸨⸩-ᴮ⇒ {P}) (λ{a} → ⸨⸩-⇒ᴮ {Q} {a})
  ⸨⸩-⇒ᴮ {{⤇-Basic {P}}} =  ⤇ᵒ-mono (⸨⸩-⇒ᴮ {P})
  ⸨⸩-⇒ᴮ {{□-Basic {P}}} =  □ᵒ-mono (λ{a} → ⸨⸩-⇒ᴮ {P} {a})
  ⸨⸩-⇒ᴮ {{↦⟨⟩-Basic}} =  _
  ⸨⸩-⇒ᴮ {{Free-Basic}} =  _

  --  ⸨ P ⸩ satisfies monotonicity

  ⸨⸩-Mono :  Monoᵒ ⸨ P ⸩
  ⸨⸩-Mono {∀₁˙ P˙} =  ∀₁ᵒ-Mono (λ x → ⸨⸩-Mono {P˙ x})
  ⸨⸩-Mono {∃₁˙ P˙} =  ∃₁ᵒ-Mono (λ x → ⸨⸩-Mono {P˙ x})
  ⸨⸩-Mono {_ →' _} =  →ᵒ-Mono
  ⸨⸩-Mono {_ ∗ _} =  ∗ᵒ-Mono
  ⸨⸩-Mono {_ -∗ Q} =  -∗ᵒ-Mono {Qᵒ = ⸨ Q ⸩}
  ⸨⸩-Mono {⤇ _} =  ⤇ᵒ-Mono
  ⸨⸩-Mono {□ P} =  □ᵒ-Mono (⸨⸩-Mono {P})
  ⸨⸩-Mono {○ _} =  ○ᵒ-Mono
  ⸨⸩-Mono {_ ↪[ _ ]⇛ _} =  ↪⇛ᵒ-Mono
  ⸨⸩-Mono {_ ↪⟨ _ ⟩ᴾ _} =  ↪⟨⟩ᴾᵒ-Mono
  ⸨⸩-Mono {_ ↪⟨ _ ⟩ᵀ[ _ ] _} =  ↪⟨⟩ᵀᵒ-Mono
  ⸨⸩-Mono {_ ↦⟨ _ ⟩ _} =  _
  ⸨⸩-Mono {Free _ _} =  _

--------------------------------------------------------------------------------
-- ⊢⇒⊨✓ :  Semantic soundness of the pure sequent

abstract

  ⊢⇒⊨✓ :  P ⊢[ ∞ ] Q →  ⸨ P ⸩ ⊨✓ ⸨ Q ⸩

  -- ⊢-refl :  P ⊢[ ∞ ] P

  ⊢⇒⊨✓ ⊢-refl _ =  id

  -- _»_ :  P ⊢[ ∞ ] Q →  Q ⊢[ ∞ ] R →  P ⊢[ ∞ ] R

  ⊢⇒⊨✓ (P⊢Q » Q⊢R) E✓a =  ⊢⇒⊨✓ P⊢Q E✓a › ⊢⇒⊨✓ Q⊢R E✓a

  -- ∀₁-intro :  (∀₁ x → P ⊢[ ∞ ] Q˙ x) →  P ⊢[ ∞ ] ∀₁˙ Q˙

  ⊢⇒⊨✓ (∀₁-intro ∀xP⊢Qx) E✓a Pa x =  ⊢⇒⊨✓ (∀xP⊢Qx x) E✓a Pa

  -- ∃₁-elim :  (∀₁ x → P˙ x ⊢[ ∞ ] Q) →  ∃₁˙ P˙ ⊢[ ∞ ] Q

  ⊢⇒⊨✓ (∃₁-elim ∀xPx⊢Q) E✓a (x , Pxa) =  ⊢⇒⊨✓ (∀xPx⊢Q x) E✓a Pxa

  -- ∀₁-elim :  ∀ x →  ∀₁˙ P˙ ⊢[ ∞ ] P˙ x

  ⊢⇒⊨✓ (∀₁-elim x) _ ∀Pa =  ∀Pa x

  -- ∃₁-intro :  ∀ x →  P˙ x ⊢[ ∞ ] ∃₁˙ P˙

  ⊢⇒⊨✓ (∃₁-intro x) _ Px =  x , Px

  -- choice₁ :  ∀₁ x , ∃₁ y , P˙˙ x y ⊢[ ∞ ] ∃₁ y˙ , ∀₁ x , P˙˙ x (y˙ x)

  -- It can be proved axiom-free thanks to the logic's predicativity

  ⊢⇒⊨✓ choice₁ _ ∀x∃₁yPxy .proj₀ x =  ∀x∃₁yPxy x .proj₀
  ⊢⇒⊨✓ choice₁ _ ∀x∃₁yPxy .proj₁ x =  ∀x∃₁yPxy x .proj₁

  -- →-intro :  P ∧ Q ⊢[ ∞ ] R →  Q ⊢[ ∞ ] P →' R

  ⊢⇒⊨✓ (→-intro {Q = Q} P∧Q⊢R) _ =
    →ᵒ-intro (⸨⸩-Mono {Q}) (λ E✓a (Pa , Qa) → ⊢⇒⊨✓ P∧Q⊢R E✓a $ binary Pa Qa)

  -- →-elim :  Q ⊢[ ∞ ] P →' R →  P ∧ Q ⊢[ ∞ ] R

  ⊢⇒⊨✓ (→-elim Q⊢P→R) E✓a P∧Qa =  →ᵒ-elim (⊢⇒⊨✓ Q⊢P→R) E✓a (P∧Qa 0₂ , P∧Qa 1₂)

  -- ⊤∗-elim :  ⊤' ∗ P ⊢[ ∞ ] P

  ⊢⇒⊨✓ (⊤∗-elim {P}) _ =  ∗ᵒ-elimʳ $ ⸨⸩-Mono {P}

  -- ⊤∗-intro :  P ⊢[ ∞ ] ⊤' ∗ P

  ⊢⇒⊨✓ ⊤∗-intro _ =  ?∗ᵒ-intro absurd

  -- ∗-comm :  P ∗ Q ⊢[ ∞ ] Q ∗ P

  ⊢⇒⊨✓ ∗-comm _ =  ∗ᵒ-comm

  -- ∗-assocˡ :  (P ∗ Q) ∗ R ⊢[ ∞ ] P ∗ (Q ∗ R)

  ⊢⇒⊨✓ ∗-assocˡ _ =  ∗ᵒ-assocˡ

  -- ∗-monoˡ :  P ⊢[ ∞ ] Q →  P ∗ R ⊢[ ∞ ] Q ∗ R

  ⊢⇒⊨✓ (∗-monoˡ P⊢Q) =  ∗ᵒ-mono✓ˡ (⊢⇒⊨✓ P⊢Q)

  -- -∗-intro :  P ∗ Q ⊢[ ∞ ] R →  Q ⊢[ ∞ ] P -∗ R

  ⊢⇒⊨✓ (-∗-intro P∗Q⊢R) _ =  -∗ᵒ-intro $ ⊢⇒⊨✓ P∗Q⊢R

  -- -∗-elim :  Q ⊢[ ∞ ] P -∗ R →  P ∗ Q ⊢[ ∞ ] R

  ⊢⇒⊨✓ (-∗-elim {R = R} Q⊢P-∗R) =  -∗ᵒ-elim (⸨⸩-Mono {R}) $ ⊢⇒⊨✓ Q⊢P-∗R

  -- ⤇-mono :  P ⊢[ ∞ ] Q →  ⤇ P ⊢[ ∞ ] ⤇ Q

  ⊢⇒⊨✓ (⤇-mono P⊢Q) _ =  ⤇ᵒ-mono✓ $ ⊢⇒⊨✓ P⊢Q

  -- ⤇-intro :  P ⊢[ ∞ ] ⤇ P

  ⊢⇒⊨✓ ⤇-intro _ =  ⤇ᵒ-intro

  -- ⤇-join :  ⤇ ⤇ P ⊢[ ∞ ] ⤇ P

  ⊢⇒⊨✓ ⤇-join _ =  ⤇ᵒ-join

  -- ⤇-eatˡ :  P ∗ ⤇ Q ⊢[ ∞ ] ⤇ (P ∗ Q)

  ⊢⇒⊨✓ ⤇-eatˡ _ =  ⤇ᵒ-eatˡ

  -- ⤇-∃-out :  ⤇ (∃₁ _ ∈ X , P) ⊢[ ∞ ] ∃₁ _ ∈ X , ⤇ P

  ⊢⇒⊨✓ ⤇-∃-out =  ⤇ᵒ-∃₁ᵒ-out

  -- □-mono :  P ⊢[ ∞ ] Q →  □ P ⊢[ ∞ ] □ Q

  ⊢⇒⊨✓ (□-mono P⊢Q) =  □ᵒ-mono✓ $ ⊢⇒⊨✓ P⊢Q

  -- □-elim :  □ P ⊢[ ∞ ] P

  ⊢⇒⊨✓ (□-elim {P}) _ =  □ᵒ-elim $ ⸨⸩-Mono {P}

  -- □-dup :  □ P ⊢[ ∞ ] □ □ P

  ⊢⇒⊨✓ (□-dup {P}) _ =   □ᵒ-dup $ ⸨⸩-Mono {P}

  -- □ˡ-∧⇒∗ :  □ P ∧ Q ⊢[ ∞ ] □ P ∗ Q

  ⊢⇒⊨✓ (□ˡ-∧⇒∗ {P}) _ □P∧Qa =
    □ᵒˡ-×ᵒ⇒∗ᵒ (⸨⸩-Mono {P}) (□P∧Qa 0₂ , □P∧Qa 1₂)

  -- □-∀-in :  ∀₁˙ (□_ ∘ P˙) ⊢[ ∞ ] □ ∀₁˙ P˙

  ⊢⇒⊨✓ □-∀-in _ =  id

  -- □-∃-out :  □ ∃₁˙ P˙ ⊢[ ∞ ] ∃₁˙ (□_ ∘ P˙)

  ⊢⇒⊨✓ □-∃-out _ =  id

  -- ○-mono :  P˂ .! ⊢[< ι ] Q˂ .! →  ○ P˂ ⊢[ ι ] ○ Q˂

  ⊢⇒⊨✓ (○-mono P⊢Q) _ =  ○ᵒ-mono $ P⊢Q .!

  -- ○-eatˡ :  {{Basic Q}} →  Q ∗ ○ P˂ ⊢[ ι ] ○ ¡ (Q ∗ P˂ .!)

  ⊢⇒⊨✓ (○-eatˡ {Q}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {Q}) › ○ᵒ-eatˡ

  -- ↪⇛-suc :  P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P˂ ↪[ suc i ]⇛ Q˂
  ⊢⇒⊨✓ ↪⇛-suc _ =  ↪⇛ᵒ-suc

  -- ↪⇛-eatˡ⁻ˡᵘ :  {{Basic R}} →  R ∗ P'˂ .! ⊢[< ι ][ i ]⇛ P˂ .! →
  --               R ∗ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ]  P'˂ ↪[ i ]⇛ Q˂

  ⊢⇒⊨✓ (↪⇛-eatˡ⁻ˡᵘ {R} R∗P'⊢⇛P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⇛ᵒ-eatˡ⁻ˡᵘ $ R∗P'⊢⇛P .!

  -- ↪⇛-eatˡ⁻ʳ :  {{Basic R}} →
  --   R ∗ (P˂ ↪[ i ]⇛ Q˂)  ⊢[ ι ]  P˂ ↪[ i ]⇛ ¡ (R ∗ Q˂ .!)

  ⊢⇒⊨✓ (↪⇛-eatˡ⁻ʳ {R}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⇛ᵒ-eatˡ⁻ʳ

  -- ↪⇛-monoʳᵘ :  Q˂ .! ⊢[< ι ][ i ]⇛ Q'˂ .! →
  --              P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  P˂ ↪[ i ]⇛ Q'˂

  ⊢⇒⊨✓ (↪⇛-monoʳᵘ Q⊢⇛Q') _ =  ↪⇛ᵒ-monoʳᵘ $ Q⊢⇛Q' .!

  -- ↪⇛-frameˡ :  P˂ ↪[ i ]⇛ Q˂  ⊢[ ι ]  ¡ (R ∗ P˂ .!) ↪[ i ]⇛ ¡ (R ∗ Q˂ .!)

  ⊢⇒⊨✓ ↪⇛-frameˡ _ =  ↪⇛ᵒ-frameˡ

  -- ○⇒↪⇛ :  P˂ .! ∗ R˂ .! ⊢[< ι ][ i ]⇛ Q˂ .! →  ○ R˂  ⊢[ ι ]  P˂ ↪[ i ]⇛ Q˂

  ⊢⇒⊨✓ (○⇒↪⇛ P∗R⊢⇛Q) _ =  ○ᵒ⇒↪⇛ᵒ $ P∗R⊢⇛Q .!

  -- ↪⟨⟩ᴾ-eatˡ⁻ˡᵘ :  {{Basic R}} →  (R ∗ P'˂ .! ⊢[< ι ][ i ]⇛ P˂ .!) →
  --                 R ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ)  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᴾ Q˂ᵛ

  ⊢⇒⊨✓ (↪⟨⟩ᴾ-eatˡ⁻ˡᵘ {R} R∗P'⊢⇛P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⟨⟩ᴾᵒ-eatˡ⁻ˡᵘ $ R∗P'⊢⇛P .!

  -- ↪⟨⟩ᴾ-eatˡ⁻ʳ :  {{Basic R}} →
  --   R ∗ (P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ)  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ λ v → ¡ (R ∗ Q˂ᵛ v .!)

  ⊢⇒⊨✓ (↪⟨⟩ᴾ-eatˡ⁻ʳ {R}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⟨⟩ᴾᵒ-eatˡ⁻ʳ

  -- ↪⟨⟩ᴾ-monoʳᵘ :  (∀ v →  Q˂ᵛ v .! ⊢[< ι ][ i ]⇛ Q'˂ᵛ v .!) →
  --                P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q'˂ᵛ

  ⊢⇒⊨✓ (↪⟨⟩ᴾ-monoʳᵘ ∀vQ⊢⇛Q') _ =  ↪⟨⟩ᴾᵒ-monoʳᵘ $ λ v → ∀vQ⊢⇛Q' v .!

  -- ↪⟨⟩ᴾ-frameˡ :  P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ  ⊢[ ι ]
  --                  ¡ (R ∗ P˂ .!) ↪⟨ e ⟩ᴾ λ v → ¡ (R ∗ Q˂ᵛ v .!)

  ⊢⇒⊨✓ ↪⟨⟩ᴾ-frameˡ _ =  ↪⟨⟩ᴾᵒ-frameˡ

  -- ○⇒↪⟨⟩ᴾ :  P˂ .! ∗ R˂ .! ⊢[< ι ]⟨ e ⟩ᴾ (λ v → Q˂ᵛ v .!) →
  --           ○ R˂  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᴾ Q˂ᵛ

  ⊢⇒⊨✓ (○⇒↪⟨⟩ᴾ P∗R⊢⟨e⟩Q) _ =  ○ᵒ⇒↪⟨⟩ᴾᵒ $ P∗R⊢⟨e⟩Q .!

  -- ↪⟨⟩ᵀ-suc :  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ suc i ] Q˂ᵛ

  ⊢⇒⊨✓ ↪⟨⟩ᵀ-suc _ =  ↪⟨⟩ᵀᵒ-suc

  -- ↪⟨⟩ᵀ-eatˡ⁻ˡᵘ :  {{Basic R}} →  (R ∗ P'˂ .! ⊢[< ι ][ j ]⇛ P˂ .!) →
  --                 R ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ)  ⊢[ ι ]  P'˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ

  ⊢⇒⊨✓ (↪⟨⟩ᵀ-eatˡ⁻ˡᵘ {R} R∗P'⊢⇛P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⟨⟩ᵀᵒ-eatˡ⁻ˡᵘ $ R∗P'⊢⇛P .!

  -- ↪⟨⟩ᵀ-eatˡ⁻ʳ :  {{Basic R}} →
  --   R ∗ (P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ)  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] λ v → ¡ (R ∗ Q˂ᵛ v .!)

  ⊢⇒⊨✓ (↪⟨⟩ᵀ-eatˡ⁻ʳ {R}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ↪⟨⟩ᵀᵒ-eatˡ⁻ʳ

  -- ↪⟨⟩ᵀ-monoʳᵘ :  (∀ v →  Q˂ᵛ v .! ⊢[< ι ][ j ]⇛ Q'˂ᵛ v .!) →
  --                P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q'˂ᵛ

  ⊢⇒⊨✓ (↪⟨⟩ᵀ-monoʳᵘ ∀vQ⊢⇛Q') _ =  ↪⟨⟩ᵀᵒ-monoʳᵘ $ λ v → ∀vQ⊢⇛Q' v .!

  -- ↪⟨⟩ᵀ-frameˡ :  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ  ⊢[ ι ]
  --                  ¡ (R ∗ P˂ .!) ↪⟨ e ⟩ᵀ[ i ] λ v → ¡ (R ∗ Q˂ᵛ v .!)

  ⊢⇒⊨✓ ↪⟨⟩ᵀ-frameˡ _ =  ↪⟨⟩ᵀᵒ-frameˡ

  -- ○⇒↪⟨⟩ᵀ :  P˂ .! ∗ R˂ .! ⊢[< ι ]⟨ e ⟩ᵀ[ i ] (λ v → Q˂ᵛ v .!) →
  --           ○ R˂  ⊢[ ι ]  P˂ ↪⟨ e ⟩ᵀ[ i ] Q˂ᵛ

  ⊢⇒⊨✓ (○⇒↪⟨⟩ᵀ P∗R⊢⟨e⟩Q) _ =  ○ᵒ⇒↪⟨⟩ᵀᵒ $ P∗R⊢⟨e⟩Q .!
