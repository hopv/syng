--------------------------------------------------------------------------------
-- Lifetime ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Lft where

open import Base.Level using (0ᴸ; 1ᴸ; ↑_; ↓)
open import Base.Func using (_$_; id)
open import Base.Few using (⊤; ⊥; ¬_; absurd)
open import Base.Eq using (_≡_; refl; ◠_; _◇_; cong)
open import Base.Dec using (yes; no; _≟_; ≟-refl)
open import Base.Prod using (∑-syntax; _×_; π₀; π₁; _,_; -,_; _,-)
open import Base.Nat using (ℕ; ṡ_; ≤-refl; <⇒≤; <-irrefl; Cofin˙; ∀≥˙-upd˙-ṡ;
  Cofin˙-resp)
open import Base.RatPos using (ℚ⁺; 1ᴿ⁺; _+ᴿ⁺_; _≤1ᴿ⁺; +ᴿ⁺-comm; +ᴿ⁺-assocˡ;
  1≤1ᴿ⁺; ≤1ᴿ⁺-rem)
open import Syho.Logic.Prop using (Lft)
open import Syho.Model.ERA.Base using (ERA; Valmᴱᴿᴬ; Upᴱᴿᴬ)
import Syho.Model.ERA.All

open ERA using (Res; _≈_; _∙_; ε; ⌞_⌟; Env; _✓_; refl˜; ◠˜_; _◇˜_; ∙-congˡ;
  ∙-unitˡ; ∙-comm; ∙-assocˡ; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem; ✓-resp; ✓-rem)

--------------------------------------------------------------------------------
-- Lftb :  Lifetime box, a resource for a single lifetime

infix 8 #ᴸᵇ_
data  Lftb :  Set₀  where
  -- Undefined
  εᴸᵇ :  Lftb
  -- Alive with the fraction
  #ᴸᵇ_ :  ℚ⁺ →  Lftb
  -- Dead
  †ᴸᵇ :  Lftb
  -- Invalid
  ↯ᴸᵇ :  Lftb

private variable
  α :  Lft
  p q :  ℚ⁺
  a b c :  Lftb
  a˙ b˙ :  Lft →  Lftb

-- Composition of Lftb

infixr 7 _∙ᴸᵇ_
_∙ᴸᵇ_ :  Lftb →  Lftb →  Lftb
εᴸᵇ ∙ᴸᵇ a =  a
↯ᴸᵇ ∙ᴸᵇ _ =  ↯ᴸᵇ
a ∙ᴸᵇ εᴸᵇ =  a
_ ∙ᴸᵇ ↯ᴸᵇ =  ↯ᴸᵇ
#ᴸᵇ p ∙ᴸᵇ #ᴸᵇ q =  #ᴸᵇ (p +ᴿ⁺ q)
†ᴸᵇ ∙ᴸᵇ †ᴸᵇ =  †ᴸᵇ
_ ∙ᴸᵇ _ =  ↯ᴸᵇ

-- Core of Lftb

⌞_⌟ᴸᵇ :  Lftb →  Lftb
⌞ †ᴸᵇ ⌟ᴸᵇ =  †ᴸᵇ
⌞ ↯ᴸᵇ ⌟ᴸᵇ =  ↯ᴸᵇ
⌞ _ ⌟ᴸᵇ =  εᴸᵇ

-- Validity of Lftb

infix 4 ✓ᴸᵇ_
✓ᴸᵇ_ :  Lftb →  Set₀
✓ᴸᵇ ↯ᴸᵇ =  ⊥
✓ᴸᵇ (#ᴸᵇ p) =  p ≤1ᴿ⁺
✓ᴸᵇ _ =  ⊤

abstract

  -- a ∙ᴸᵇ εᴸᵇ equals a

  ∙ᴸᵇ-ε :  a ∙ᴸᵇ εᴸᵇ ≡ a
  ∙ᴸᵇ-ε {εᴸᵇ} =  refl
  ∙ᴸᵇ-ε {#ᴸᵇ _} =  refl
  ∙ᴸᵇ-ε {†ᴸᵇ} =  refl
  ∙ᴸᵇ-ε {↯ᴸᵇ} =  refl

  -- a ∙ᴸᵇ ↯ᴸᵇ equals ↯ᴸᵇ

  ∙ᴸᵇ-↯ :  a ∙ᴸᵇ ↯ᴸᵇ ≡ ↯ᴸᵇ
  ∙ᴸᵇ-↯ {εᴸᵇ} =  refl
  ∙ᴸᵇ-↯ {#ᴸᵇ _} =  refl
  ∙ᴸᵇ-↯ {†ᴸᵇ} =  refl
  ∙ᴸᵇ-↯ {↯ᴸᵇ} =  refl

  -- ∙ᴸᵇ is commutative

  ∙ᴸᵇ-comm :  a ∙ᴸᵇ b  ≡  b ∙ᴸᵇ a
  ∙ᴸᵇ-comm {a} {εᴸᵇ}  rewrite ∙ᴸᵇ-ε {a} =  refl
  ∙ᴸᵇ-comm {εᴸᵇ} {b}  rewrite ∙ᴸᵇ-ε {b} =  refl
  ∙ᴸᵇ-comm {a} {↯ᴸᵇ}  rewrite ∙ᴸᵇ-↯ {a} =  refl
  ∙ᴸᵇ-comm {↯ᴸᵇ} {b}  rewrite ∙ᴸᵇ-↯ {b} =  refl
  ∙ᴸᵇ-comm {#ᴸᵇ p} {#ᴸᵇ _} =  cong #ᴸᵇ_ $ +ᴿ⁺-comm {p}
  ∙ᴸᵇ-comm {#ᴸᵇ _} {†ᴸᵇ} =  refl
  ∙ᴸᵇ-comm {†ᴸᵇ} {#ᴸᵇ _} =  refl
  ∙ᴸᵇ-comm {†ᴸᵇ} {†ᴸᵇ} =  refl

  -- ∙ᴸᵇ is associative

  ∙ᴸᵇ-assocˡ :  (a ∙ᴸᵇ b) ∙ᴸᵇ c  ≡  a ∙ᴸᵇ (b ∙ᴸᵇ c)
  ∙ᴸᵇ-assocˡ {εᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {↯ᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {†ᴸᵇ} {εᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {†ᴸᵇ} {↯ᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {†ᴸᵇ} {†ᴸᵇ} {εᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {†ᴸᵇ} {†ᴸᵇ} {↯ᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {†ᴸᵇ} {†ᴸᵇ} {†ᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {†ᴸᵇ} {†ᴸᵇ} {#ᴸᵇ _} =  refl
  ∙ᴸᵇ-assocˡ {†ᴸᵇ} {#ᴸᵇ _} {εᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {†ᴸᵇ} {#ᴸᵇ _} {↯ᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {†ᴸᵇ} {#ᴸᵇ _} {†ᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {†ᴸᵇ} {#ᴸᵇ _} {#ᴸᵇ _} =  refl
  ∙ᴸᵇ-assocˡ {#ᴸᵇ _} {εᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {#ᴸᵇ _} {↯ᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {#ᴸᵇ _} {†ᴸᵇ} {εᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {#ᴸᵇ _} {†ᴸᵇ} {↯ᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {#ᴸᵇ _} {†ᴸᵇ} {†ᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {#ᴸᵇ _} {†ᴸᵇ} {#ᴸᵇ _} =  refl
  ∙ᴸᵇ-assocˡ {#ᴸᵇ _} {#ᴸᵇ _} {εᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {#ᴸᵇ _} {#ᴸᵇ _} {↯ᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {#ᴸᵇ _} {#ᴸᵇ _} {†ᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {#ᴸᵇ p} {#ᴸᵇ q} {#ᴸᵇ _} =  cong #ᴸᵇ_ $ +ᴿ⁺-assocˡ {p} {q}

  -- When ⌞⌟ᴸᵇ's argument gets added, ⌞⌟ᴸᵇ's result gets added

  ⌞⌟ᴸᵇ-add :  ∑ a' ,  ⌞ a ∙ᴸᵇ b ⌟ᴸᵇ  ≡  a' ∙ᴸᵇ ⌞ b ⌟ᴸᵇ
  ⌞⌟ᴸᵇ-add {εᴸᵇ} =  εᴸᵇ ,  refl
  ⌞⌟ᴸᵇ-add {↯ᴸᵇ} =  ↯ᴸᵇ ,  refl
  ⌞⌟ᴸᵇ-add {#ᴸᵇ _} {εᴸᵇ} =  εᴸᵇ ,  refl
  ⌞⌟ᴸᵇ-add {#ᴸᵇ _} {#ᴸᵇ _} =  εᴸᵇ ,  refl
  ⌞⌟ᴸᵇ-add {#ᴸᵇ _} {†ᴸᵇ} =  ↯ᴸᵇ ,  refl
  ⌞⌟ᴸᵇ-add {#ᴸᵇ _} {↯ᴸᵇ} =  εᴸᵇ ,  refl
  ⌞⌟ᴸᵇ-add {†ᴸᵇ} {εᴸᵇ} =  †ᴸᵇ ,  refl
  ⌞⌟ᴸᵇ-add {†ᴸᵇ} {#ᴸᵇ _} =  ↯ᴸᵇ ,  refl
  ⌞⌟ᴸᵇ-add {†ᴸᵇ} {†ᴸᵇ} =  εᴸᵇ ,  refl
  ⌞⌟ᴸᵇ-add {†ᴸᵇ} {↯ᴸᵇ} =  εᴸᵇ ,  refl

  -- ⌞ a ⌟ᴸᵇ is absorbed by a

  ⌞⌟ᴸᵇ-unitˡ :  ⌞ a ⌟ᴸᵇ ∙ᴸᵇ a  ≡  a
  ⌞⌟ᴸᵇ-unitˡ {εᴸᵇ} =  refl
  ⌞⌟ᴸᵇ-unitˡ {#ᴸᵇ _} =  refl
  ⌞⌟ᴸᵇ-unitˡ {†ᴸᵇ} =  refl
  ⌞⌟ᴸᵇ-unitˡ {↯ᴸᵇ} =  refl

  -- ⌞ ⌟ᴸᵇ is idempotent

  ⌞⌟ᴸᵇ-idem :  ⌞ ⌞ a ⌟ᴸᵇ ⌟ᴸᵇ  ≡  ⌞ a ⌟ᴸᵇ
  ⌞⌟ᴸᵇ-idem {εᴸᵇ} =  refl
  ⌞⌟ᴸᵇ-idem {#ᴸᵇ _} =  refl
  ⌞⌟ᴸᵇ-idem {†ᴸᵇ} =  refl
  ⌞⌟ᴸᵇ-idem {↯ᴸᵇ} =  refl

  -- ✓ᴸᵇ is preserved by removal w.r.t. ∙ᴸᵇ

  ✓ᴸᵇ-rem :  ✓ᴸᵇ a ∙ᴸᵇ b →  ✓ᴸᵇ b
  ✓ᴸᵇ-rem {εᴸᵇ} =  id
  ✓ᴸᵇ-rem {_} {εᴸᵇ} _ =  _
  ✓ᴸᵇ-rem {_} {†ᴸᵇ} _ =  _
  ✓ᴸᵇ-rem {#ᴸᵇ p} {#ᴸᵇ _} p+q≤1 =  ≤1ᴿ⁺-rem {p} p+q≤1

--------------------------------------------------------------------------------
-- Lftbᴱᴿᴬ :  Lifetime box ERA

Lftbᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
Lftbᴱᴿᴬ .Res =  Lftb
Lftbᴱᴿᴬ ._≈_ =  _≡_
Lftbᴱᴿᴬ ._∙_ =  _∙ᴸᵇ_
Lftbᴱᴿᴬ .ε =  εᴸᵇ
Lftbᴱᴿᴬ .⌞_⌟ =  ⌞_⌟ᴸᵇ
Lftbᴱᴿᴬ .Env =  ⊤
Lftbᴱᴿᴬ ._✓_ _ =  ✓ᴸᵇ_
Lftbᴱᴿᴬ .refl˜ =  refl
Lftbᴱᴿᴬ .◠˜_ =  ◠_
Lftbᴱᴿᴬ ._◇˜_ =  _◇_
Lftbᴱᴿᴬ .∙-congˡ refl =  refl
Lftbᴱᴿᴬ .∙-unitˡ =  refl
Lftbᴱᴿᴬ .∙-comm {a} =  ∙ᴸᵇ-comm {a}
Lftbᴱᴿᴬ .∙-assocˡ {a} =  ∙ᴸᵇ-assocˡ {a}
Lftbᴱᴿᴬ .⌞⌟-cong refl =  refl
Lftbᴱᴿᴬ .⌞⌟-add {a} =  ⌞⌟ᴸᵇ-add {a}
Lftbᴱᴿᴬ .⌞⌟-unitˡ =  ⌞⌟ᴸᵇ-unitˡ
Lftbᴱᴿᴬ .⌞⌟-idem =  ⌞⌟ᴸᵇ-idem
Lftbᴱᴿᴬ .✓-resp refl =  id
Lftbᴱᴿᴬ .✓-rem {a = a} =  ✓ᴸᵇ-rem {a}

--------------------------------------------------------------------------------
-- Lftᴱᴿᴬ :  Lifetime ERA

-- ∙ᴸᵇ˙ :  Compose Lft → Lftb

infix 7 _∙ᴸᵇ˙_
_∙ᴸᵇ˙_ :  (Lft → Lftb) →  (Lft → Lftb) →  (Lft → Lftb)
(a˙ ∙ᴸᵇ˙ b˙) i =  a˙ i ∙ᴸᵇ b˙ i

-- Cofinεᴸᵇ a˙ :  a˙ i ≡ εᴸᵇ holds for all but finitely many i's

Cofinεᴸᵇ :  (Lft → Lftb) →  Set₀
Cofinεᴸᵇ =  Cofin˙ (λ _ → _≡ εᴸᵇ)

abstract

  -- Cofinεᴸᵇ is preserved by removal w.r.t. ∙ᴸᵇ˙

  Cofinεᴸᵇ˙-rem :  Cofinεᴸᵇ (a˙ ∙ᴸᵇ˙ b˙) →  Cofinεᴸᵇ b˙
  Cofinεᴸᵇ˙-rem {a˙} {b˙} (n ,-) .π₀ =  n
  Cofinεᴸᵇ˙-rem {a˙} {b˙} (-, i≥n⇒ai∙bi≡ε) .π₁ i i≥n
    with a˙ i | b˙ i | i≥n⇒ai∙bi≡ε i i≥n
  … | εᴸᵇ | εᴸᵇ | refl =  refl
  … | ↯ᴸᵇ | _ | ()

-- Construct Lftᴱᴿᴬ

module AllLft =  Syho.Model.ERA.All Lft (λ _ → Lftbᴱᴿᴬ)
open AllLft public using () renaming (
  --  ∀Lftᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
  ∀ᴱᴿᴬ to ∀Lftᴱᴿᴬ;
  --  inj˙ᴸᵇ :  Lft →  Lftb →  Lft →  Lftb
  inj˙ to inj˙ᴸᵇ; inj˙-∙ to inj˙ᴸᵇ-∙; inj˙-⌞⌟ to inj˙ᴸᵇ-⌞⌟)

Lftᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
Lftᴱᴿᴬ =  Upᴱᴿᴬ (Valmᴱᴿᴬ ∀Lftᴱᴿᴬ (λ _ → Cofinεᴸᵇ)
  (Cofin˙-resp {F = λ _ → _≡ εᴸᵇ}) (λ{_} {a˙} → Cofinεᴸᵇ˙-rem {a˙}))

open ERA Lftᴱᴿᴬ public using () renaming (Res to Resᴸᶠᵗ; _≈_ to _≈ᴸᶠᵗ_;
  _∙_ to _∙ᴸᶠᵗ_; ε to εᴸᶠᵗ; ⌞_⌟ to ⌞_⌟ᴸᶠᵗ; _✓_ to _✓ᴸᶠᵗ_; _↝_ to _↝ᴸᶠᵗ_;
  ◠˜_ to ◠˜ᴸᶠᵗ_)

-- [ ]ᴸ⟨ ⟩ʳ :  Resource for the lifetime token

[_]ᴸ⟨_⟩ʳ :  Lft →  ℚ⁺ →  Resᴸᶠᵗ
[ α ]ᴸ⟨ p ⟩ʳ .↓ =  inj˙ᴸᵇ α $ #ᴸᵇ p

[_]ᴸʳ :  Lft →  Resᴸᶠᵗ
[ α ]ᴸʳ =  [ α ]ᴸ⟨ 1ᴿ⁺ ⟩ʳ

-- †ᴸʳ :  Resource for the dead lifetime token

infix 8 †ᴸʳ_
†ᴸʳ_ :  Lft →  Resᴸᶠᵗ
(†ᴸʳ α) .↓ =  inj˙ᴸᵇ α †ᴸᵇ

abstract

  -- εᴸᶠᵗ is valid

  ✓ᴸᶠᵗε :  _ ✓ᴸᶠᵗ εᴸᶠᵗ
  ✓ᴸᶠᵗε .↓ =  (0 , λ _ _ → refl) ,-

  -- Merge [ ]ᴸ⟨ ⟩ʳ with ∙ᴸᶠᵗ

  []ᴸ⟨⟩ʳ-∙ :  [ α ]ᴸ⟨ p ⟩ʳ ∙ᴸᶠᵗ [ α ]ᴸ⟨ q ⟩ʳ  ≈ᴸᶠᵗ  [ α ]ᴸ⟨ p +ᴿ⁺ q ⟩ʳ
  []ᴸ⟨⟩ʳ-∙ .↓ =  inj˙ᴸᵇ-∙

  -- The fraction of [ ]ᴸ⟨ ⟩ʳ is no more than 1

  []ᴸ⟨⟩ʳ-≤1 :  _ ✓ᴸᶠᵗ [ α ]ᴸ⟨ p ⟩ʳ →  p ≤1ᴿ⁺
  []ᴸ⟨⟩ʳ-≤1 {α} (↑ (-, ✓αp))  with ✓αp α
  … | ✓#p  rewrite ≟-refl {a = α} =  ✓#p

  -- †ᴸʳ absorbs ⌞ ⌟ᴸᶠᵗ

  †ᴸʳ-⌞⌟ :  ⌞ †ᴸʳ α ⌟ᴸᶠᵗ  ≈ᴸᶠᵗ  †ᴸʳ α
  †ᴸʳ-⌞⌟ .↓ =  inj˙ᴸᵇ-⌞⌟

  -- [ α ]ᴸ⟨ p ⟩ʳ and †ᴸʳ α cannot coexist

  []ᴸ⟨⟩ʳ-†ᴸʳ-no :  ¬ _ ✓ᴸᶠᵗ [ α ]ᴸ⟨ p ⟩ʳ ∙ᴸᶠᵗ †ᴸʳ α
  []ᴸ⟨⟩ʳ-†ᴸʳ-no {α} (↑ (-, ✓αp∙†α))  with ✓αp∙†α α
  … | ✓#p∙†  rewrite ≟-refl {a = α} =  ✓#p∙†

  -- Allocate a new lifetime

  []ᴸʳ-new :  (-, εᴸᶠᵗ)  ↝ᴸᶠᵗ λ α →  -, [ α ]ᴸʳ
  []ᴸʳ-new _ (↑ ((α ,-) ,-)) .π₀ =  α
  []ᴸʳ-new _ (↑ ((α ,-) ,-)) .π₁ .↓ .π₀ .π₀ =  ṡ α
  []ᴸʳ-new _ (↑ ((α , ≥α⇒≡ε) ,-)) .π₁ .↓ .π₀ .π₁ β β>α
    rewrite ≥α⇒≡ε β (<⇒≤ β>α)  with β ≟ α
  … | no _ =  refl
  … | yes refl =  absurd $ <-irrefl β>α
  []ᴸʳ-new _ (↑ ((α , ≥α⇒≡ε) , ✓c)) .π₁ .↓ .π₁ β  with β ≟ α
  … | no _ =  ✓c β
  … | yes refl  rewrite ≥α⇒≡ε α ≤-refl =  1≤1ᴿ⁺
