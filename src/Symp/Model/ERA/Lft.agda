--------------------------------------------------------------------------------
-- Lifetime ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Syho.Model.ERA.Lft where

open import Base.Level using (0ᴸ; 1ᴸ; ↑_; ↓)
open import Base.Func using (_$_; id)
open import Base.Few using (⊤; ⊤₀; ⊥; ¬_; absurd)
open import Base.Eq using (_≡_; refl; cong)
open import Base.Dec using (≟-refl)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_; _,-)
open import Base.Nat using (ℕ)
open import Base.Ratp using (ℚ⁺; _≈ᴿ⁺_; 1ᴿ⁺; _+ᴿ⁺_; _≤1ᴿ⁺; ≈ᴿ⁺-refl; ≈ᴿ⁺-sym;
  ≈ᴿ⁺-trans; +ᴿ⁺-congˡ; +ᴿ⁺-comm; +ᴿ⁺-assocʳ; ≤1ᴿ⁺-resp; 1≤1ᴿ⁺; ≤1ᴿ⁺-rem;
  ¬1+?≤1ᴿ⁺)
open import Syho.Model.ERA.Base using (ERA; Valmᴱᴿᴬ; Upᴱᴿᴬ)
import Syho.Model.ERA.Fin

open ERA using (Res; _≈_; _∙_; ε; ⌞_⌟; Env; _✓_; refl˜; ◠˜_; _◇˜_; ∙-congˡ;
  ∙-unitˡ; ∙-comm; ∙-assocʳ; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem; ✓-resp; ✓-rem)

private
  Lft :  Set₀
  Lft =  ℕ

--------------------------------------------------------------------------------
-- Lftb :  Lifetime box, a resource for a single lifetime

infix 8 #ᴸᶠᵗᵇ_
data  Lftb :  Set₀  where
  -- Undefined
  εᴸᶠᵗᵇ :  Lftb
  -- Alive with the fraction
  #ᴸᶠᵗᵇ_ :  ℚ⁺ →  Lftb
  -- Dead
  †ᴸᶠᵗᵇ :  Lftb
  -- Invalid
  ↯ᴸᶠᵗᵇ :  Lftb

private variable
  α :  Lft
  p q :  ℚ⁺
  a b c :  Lftb
  a˙ b˙ :  Lft →  Lftb

-- Equivalence of Lftb

infix 4 _≈ᴸᶠᵗᵇ_
_≈ᴸᶠᵗᵇ_ :  Lftb →  Lftb →  Set₀
εᴸᶠᵗᵇ ≈ᴸᶠᵗᵇ εᴸᶠᵗᵇ =  ⊤
#ᴸᶠᵗᵇ p ≈ᴸᶠᵗᵇ #ᴸᶠᵗᵇ q =  p ≈ᴿ⁺ q
†ᴸᶠᵗᵇ ≈ᴸᶠᵗᵇ †ᴸᶠᵗᵇ =  ⊤
↯ᴸᶠᵗᵇ ≈ᴸᶠᵗᵇ ↯ᴸᶠᵗᵇ =  ⊤
_ ≈ᴸᶠᵗᵇ _ =  ⊥

-- Product of Lftb

infixr 7 _∙ᴸᶠᵗᵇ_
_∙ᴸᶠᵗᵇ_ :  Lftb →  Lftb →  Lftb
εᴸᶠᵗᵇ ∙ᴸᶠᵗᵇ a =  a
↯ᴸᶠᵗᵇ ∙ᴸᶠᵗᵇ _ =  ↯ᴸᶠᵗᵇ
a ∙ᴸᶠᵗᵇ εᴸᶠᵗᵇ =  a
_ ∙ᴸᶠᵗᵇ ↯ᴸᶠᵗᵇ =  ↯ᴸᶠᵗᵇ
#ᴸᶠᵗᵇ p ∙ᴸᶠᵗᵇ #ᴸᶠᵗᵇ q =  #ᴸᶠᵗᵇ (p +ᴿ⁺ q)
†ᴸᶠᵗᵇ ∙ᴸᶠᵗᵇ †ᴸᶠᵗᵇ =  †ᴸᶠᵗᵇ
_ ∙ᴸᶠᵗᵇ _ =  ↯ᴸᶠᵗᵇ

-- Core of Lftb

⌞_⌟ᴸᶠᵗᵇ :  Lftb →  Lftb
⌞ †ᴸᶠᵗᵇ ⌟ᴸᶠᵗᵇ =  †ᴸᶠᵗᵇ
⌞ ↯ᴸᶠᵗᵇ ⌟ᴸᶠᵗᵇ =  ↯ᴸᶠᵗᵇ
⌞ _ ⌟ᴸᶠᵗᵇ =  εᴸᶠᵗᵇ

-- Validity of Lftb

infix 4 ✓ᴸᶠᵗᵇ_
✓ᴸᶠᵗᵇ_ :  Lftb →  Set₀
✓ᴸᶠᵗᵇ ↯ᴸᶠᵗᵇ =  ⊥
✓ᴸᶠᵗᵇ (#ᴸᶠᵗᵇ p) =  p ≤1ᴿ⁺
✓ᴸᶠᵗᵇ _ =  ⊤

abstract

  -- ≈ᴸᶠᵗᵇ is reflexive

  ≈ᴸᶠᵗᵇ-refl :  a ≈ᴸᶠᵗᵇ a
  ≈ᴸᶠᵗᵇ-refl {εᴸᶠᵗᵇ} =  _
  ≈ᴸᶠᵗᵇ-refl {#ᴸᶠᵗᵇ p} =  ≈ᴿ⁺-refl {p}
  ≈ᴸᶠᵗᵇ-refl {†ᴸᶠᵗᵇ} =  _
  ≈ᴸᶠᵗᵇ-refl {↯ᴸᶠᵗᵇ} =  _

  ≡⇒≈ᴸᶠᵗᵇ :  a ≡ b →  a ≈ᴸᶠᵗᵇ b
  ≡⇒≈ᴸᶠᵗᵇ refl =  ≈ᴸᶠᵗᵇ-refl

  -- ≈ᴸᶠᵗᵇ is symmetric

  ≈ᴸᶠᵗᵇ-sym :  a ≈ᴸᶠᵗᵇ b →  b ≈ᴸᶠᵗᵇ a
  ≈ᴸᶠᵗᵇ-sym {εᴸᶠᵗᵇ} {εᴸᶠᵗᵇ} _ =  _
  ≈ᴸᶠᵗᵇ-sym {#ᴸᶠᵗᵇ p} {#ᴸᶠᵗᵇ q} p≈q =  ≈ᴿ⁺-sym {p} {q} p≈q
  ≈ᴸᶠᵗᵇ-sym {†ᴸᶠᵗᵇ} {†ᴸᶠᵗᵇ} _ =  _
  ≈ᴸᶠᵗᵇ-sym {↯ᴸᶠᵗᵇ} {↯ᴸᶠᵗᵇ} _ =  _

  -- ≈ᴸᶠᵗᵇ is transitive

  ≈ᴸᶠᵗᵇ-trans :  a ≈ᴸᶠᵗᵇ b →  b ≈ᴸᶠᵗᵇ c →  a ≈ᴸᶠᵗᵇ c
  ≈ᴸᶠᵗᵇ-trans {εᴸᶠᵗᵇ} {εᴸᶠᵗᵇ} {εᴸᶠᵗᵇ} _ _ =  _
  ≈ᴸᶠᵗᵇ-trans {#ᴸᶠᵗᵇ p} {#ᴸᶠᵗᵇ q} {#ᴸᶠᵗᵇ r} p≈q q≈r =
    ≈ᴿ⁺-trans {p} {q} {r} p≈q q≈r
  ≈ᴸᶠᵗᵇ-trans {†ᴸᶠᵗᵇ} {†ᴸᶠᵗᵇ} {†ᴸᶠᵗᵇ} _ _ =  _
  ≈ᴸᶠᵗᵇ-trans {↯ᴸᶠᵗᵇ} {↯ᴸᶠᵗᵇ} {↯ᴸᶠᵗᵇ} _ _ =  _

  -- a ∙ᴸᶠᵗᵇ εᴸᶠᵗᵇ equals a

  ∙ᴸᶠᵗᵇ-ε :  a ∙ᴸᶠᵗᵇ εᴸᶠᵗᵇ ≡ a
  ∙ᴸᶠᵗᵇ-ε {εᴸᶠᵗᵇ} =  refl
  ∙ᴸᶠᵗᵇ-ε {#ᴸᶠᵗᵇ _} =  refl
  ∙ᴸᶠᵗᵇ-ε {†ᴸᶠᵗᵇ} =  refl
  ∙ᴸᶠᵗᵇ-ε {↯ᴸᶠᵗᵇ} =  refl

  -- a ∙ᴸᶠᵗᵇ ↯ᴸᶠᵗᵇ equals ↯ᴸᶠᵗᵇ

  ∙ᴸᶠᵗᵇ-↯ :  a ∙ᴸᶠᵗᵇ ↯ᴸᶠᵗᵇ ≡ ↯ᴸᶠᵗᵇ
  ∙ᴸᶠᵗᵇ-↯ {εᴸᶠᵗᵇ} =  refl
  ∙ᴸᶠᵗᵇ-↯ {#ᴸᶠᵗᵇ _} =  refl
  ∙ᴸᶠᵗᵇ-↯ {†ᴸᶠᵗᵇ} =  refl
  ∙ᴸᶠᵗᵇ-↯ {↯ᴸᶠᵗᵇ} =  refl

  -- ∙ᴸᶠᵗᵇ preserves ≈ᴸᶠᵗᵇ

  ∙ᴸᶠᵗᵇ-congˡ :  a ≈ᴸᶠᵗᵇ b  →   a ∙ᴸᶠᵗᵇ c  ≈ᴸᶠᵗᵇ  b ∙ᴸᶠᵗᵇ c
  ∙ᴸᶠᵗᵇ-congˡ {εᴸᶠᵗᵇ} {εᴸᶠᵗᵇ} _ =  ≈ᴸᶠᵗᵇ-refl
  ∙ᴸᶠᵗᵇ-congˡ {†ᴸᶠᵗᵇ} {†ᴸᶠᵗᵇ} _ =  ≈ᴸᶠᵗᵇ-refl
  ∙ᴸᶠᵗᵇ-congˡ {↯ᴸᶠᵗᵇ} {↯ᴸᶠᵗᵇ} _ =  _
  ∙ᴸᶠᵗᵇ-congˡ {a} {b} {εᴸᶠᵗᵇ} a≈b  rewrite ∙ᴸᶠᵗᵇ-ε {a} | ∙ᴸᶠᵗᵇ-ε {b} =  a≈b
  ∙ᴸᶠᵗᵇ-congˡ {a} {b} {↯ᴸᶠᵗᵇ} a≈b  rewrite ∙ᴸᶠᵗᵇ-↯ {a} | ∙ᴸᶠᵗᵇ-↯ {b} =  _
  ∙ᴸᶠᵗᵇ-congˡ {#ᴸᶠᵗᵇ p} {#ᴸᶠᵗᵇ q} {#ᴸᶠᵗᵇ r} p≈q =  +ᴿ⁺-congˡ {p} {q} {r} p≈q
  ∙ᴸᶠᵗᵇ-congˡ {#ᴸᶠᵗᵇ _} {#ᴸᶠᵗᵇ _} {†ᴸᶠᵗᵇ} _ =  _

  -- ∙ᴸᶠᵗᵇ is commutative

  ∙ᴸᶠᵗᵇ-comm :  a ∙ᴸᶠᵗᵇ b  ≡  b ∙ᴸᶠᵗᵇ a
  ∙ᴸᶠᵗᵇ-comm {a} {εᴸᶠᵗᵇ}  rewrite ∙ᴸᶠᵗᵇ-ε {a} =  refl
  ∙ᴸᶠᵗᵇ-comm {εᴸᶠᵗᵇ} {b}  rewrite ∙ᴸᶠᵗᵇ-ε {b} =  refl
  ∙ᴸᶠᵗᵇ-comm {a} {↯ᴸᶠᵗᵇ}  rewrite ∙ᴸᶠᵗᵇ-↯ {a} =  refl
  ∙ᴸᶠᵗᵇ-comm {↯ᴸᶠᵗᵇ} {b}  rewrite ∙ᴸᶠᵗᵇ-↯ {b} =  refl
  ∙ᴸᶠᵗᵇ-comm {#ᴸᶠᵗᵇ p} {#ᴸᶠᵗᵇ _} =  cong #ᴸᶠᵗᵇ_ $ +ᴿ⁺-comm {p}
  ∙ᴸᶠᵗᵇ-comm {#ᴸᶠᵗᵇ _} {†ᴸᶠᵗᵇ} =  refl
  ∙ᴸᶠᵗᵇ-comm {†ᴸᶠᵗᵇ} {#ᴸᶠᵗᵇ _} =  refl
  ∙ᴸᶠᵗᵇ-comm {†ᴸᶠᵗᵇ} {†ᴸᶠᵗᵇ} =  refl

  -- ∙ᴸᶠᵗᵇ is associative

  ∙ᴸᶠᵗᵇ-assocʳ :  (a ∙ᴸᶠᵗᵇ b) ∙ᴸᶠᵗᵇ c  ≡  a ∙ᴸᶠᵗᵇ (b ∙ᴸᶠᵗᵇ c)
  ∙ᴸᶠᵗᵇ-assocʳ {εᴸᶠᵗᵇ} =  refl
  ∙ᴸᶠᵗᵇ-assocʳ {↯ᴸᶠᵗᵇ} =  refl
  ∙ᴸᶠᵗᵇ-assocʳ {a} {εᴸᶠᵗᵇ}  rewrite ∙ᴸᶠᵗᵇ-ε {a} =  refl
  ∙ᴸᶠᵗᵇ-assocʳ {a} {b} {εᴸᶠᵗᵇ}  rewrite ∙ᴸᶠᵗᵇ-ε {a ∙ᴸᶠᵗᵇ b} | ∙ᴸᶠᵗᵇ-ε {b} =
    refl
  ∙ᴸᶠᵗᵇ-assocʳ {a} {↯ᴸᶠᵗᵇ}  rewrite ∙ᴸᶠᵗᵇ-↯ {a} =  refl
  ∙ᴸᶠᵗᵇ-assocʳ {a} {b} {↯ᴸᶠᵗᵇ}
    rewrite ∙ᴸᶠᵗᵇ-↯ {a ∙ᴸᶠᵗᵇ b} | ∙ᴸᶠᵗᵇ-↯ {b} | ∙ᴸᶠᵗᵇ-↯ {a} =  refl
  ∙ᴸᶠᵗᵇ-assocʳ {†ᴸᶠᵗᵇ} {†ᴸᶠᵗᵇ} {†ᴸᶠᵗᵇ} =  refl
  ∙ᴸᶠᵗᵇ-assocʳ {†ᴸᶠᵗᵇ} {†ᴸᶠᵗᵇ} {#ᴸᶠᵗᵇ _} =  refl
  ∙ᴸᶠᵗᵇ-assocʳ {†ᴸᶠᵗᵇ} {#ᴸᶠᵗᵇ _} {†ᴸᶠᵗᵇ} =  refl
  ∙ᴸᶠᵗᵇ-assocʳ {†ᴸᶠᵗᵇ} {#ᴸᶠᵗᵇ _} {#ᴸᶠᵗᵇ _} =  refl
  ∙ᴸᶠᵗᵇ-assocʳ {#ᴸᶠᵗᵇ _} {†ᴸᶠᵗᵇ} {†ᴸᶠᵗᵇ} =  refl
  ∙ᴸᶠᵗᵇ-assocʳ {#ᴸᶠᵗᵇ _} {†ᴸᶠᵗᵇ} {#ᴸᶠᵗᵇ _} =  refl
  ∙ᴸᶠᵗᵇ-assocʳ {#ᴸᶠᵗᵇ _} {#ᴸᶠᵗᵇ _} {†ᴸᶠᵗᵇ} =  refl
  ∙ᴸᶠᵗᵇ-assocʳ {#ᴸᶠᵗᵇ p} {#ᴸᶠᵗᵇ q} {#ᴸᶠᵗᵇ _} =  cong #ᴸᶠᵗᵇ_ $ +ᴿ⁺-assocʳ {p} {q}

  -- ≈ᴸᶠᵗᵇ εᴸᶠᵗᵇ is preserved by removal w.r.t. ∙ᴸᶠᵗᵇ

  ≈ᴸᶠᵗᵇε-rem :  a ∙ᴸᶠᵗᵇ b ≈ᴸᶠᵗᵇ εᴸᶠᵗᵇ →  b ≈ᴸᶠᵗᵇ εᴸᶠᵗᵇ
  ≈ᴸᶠᵗᵇε-rem {εᴸᶠᵗᵇ} {εᴸᶠᵗᵇ} _ =  _
  ≈ᴸᶠᵗᵇε-rem {↯ᴸᶠᵗᵇ} ()

  -- ⌞⌟ᴸᶠᵗᵇ preserves ≈ᴸᶠᵗᵇ

  ⌞⌟ᴸᶠᵗᵇ-cong :  a ≈ᴸᶠᵗᵇ b  →   ⌞ a ⌟ᴸᶠᵗᵇ  ≈ᴸᶠᵗᵇ  ⌞ b ⌟ᴸᶠᵗᵇ
  ⌞⌟ᴸᶠᵗᵇ-cong {εᴸᶠᵗᵇ} {εᴸᶠᵗᵇ} _ =  _
  ⌞⌟ᴸᶠᵗᵇ-cong {#ᴸᶠᵗᵇ _} {#ᴸᶠᵗᵇ _} _ =  _
  ⌞⌟ᴸᶠᵗᵇ-cong {†ᴸᶠᵗᵇ} {†ᴸᶠᵗᵇ} _ =  _
  ⌞⌟ᴸᶠᵗᵇ-cong {↯ᴸᶠᵗᵇ} {↯ᴸᶠᵗᵇ} _ =  _

  -- When ⌞⌟ᴸᶠᵗᵇ's argument gets added, ⌞⌟ᴸᶠᵗᵇ's result gets added

  ⌞⌟ᴸᶠᵗᵇ-add :  ∑ a' ,  ⌞ a ∙ᴸᶠᵗᵇ b ⌟ᴸᶠᵗᵇ  ≡  a' ∙ᴸᶠᵗᵇ ⌞ b ⌟ᴸᶠᵗᵇ
  ⌞⌟ᴸᶠᵗᵇ-add {εᴸᶠᵗᵇ} =  εᴸᶠᵗᵇ ,  refl
  ⌞⌟ᴸᶠᵗᵇ-add {↯ᴸᶠᵗᵇ} =  ↯ᴸᶠᵗᵇ ,  refl
  ⌞⌟ᴸᶠᵗᵇ-add {#ᴸᶠᵗᵇ _} {εᴸᶠᵗᵇ} =  εᴸᶠᵗᵇ ,  refl
  ⌞⌟ᴸᶠᵗᵇ-add {#ᴸᶠᵗᵇ _} {#ᴸᶠᵗᵇ _} =  εᴸᶠᵗᵇ ,  refl
  ⌞⌟ᴸᶠᵗᵇ-add {#ᴸᶠᵗᵇ _} {†ᴸᶠᵗᵇ} =  ↯ᴸᶠᵗᵇ ,  refl
  ⌞⌟ᴸᶠᵗᵇ-add {#ᴸᶠᵗᵇ _} {↯ᴸᶠᵗᵇ} =  εᴸᶠᵗᵇ ,  refl
  ⌞⌟ᴸᶠᵗᵇ-add {†ᴸᶠᵗᵇ} {εᴸᶠᵗᵇ} =  †ᴸᶠᵗᵇ ,  refl
  ⌞⌟ᴸᶠᵗᵇ-add {†ᴸᶠᵗᵇ} {#ᴸᶠᵗᵇ _} =  ↯ᴸᶠᵗᵇ ,  refl
  ⌞⌟ᴸᶠᵗᵇ-add {†ᴸᶠᵗᵇ} {†ᴸᶠᵗᵇ} =  εᴸᶠᵗᵇ ,  refl
  ⌞⌟ᴸᶠᵗᵇ-add {†ᴸᶠᵗᵇ} {↯ᴸᶠᵗᵇ} =  εᴸᶠᵗᵇ ,  refl

  -- ⌞ a ⌟ᴸᶠᵗᵇ is absorbed by a

  ⌞⌟ᴸᶠᵗᵇ-unitˡ :  ⌞ a ⌟ᴸᶠᵗᵇ ∙ᴸᶠᵗᵇ a  ≡  a
  ⌞⌟ᴸᶠᵗᵇ-unitˡ {εᴸᶠᵗᵇ} =  refl
  ⌞⌟ᴸᶠᵗᵇ-unitˡ {#ᴸᶠᵗᵇ _} =  refl
  ⌞⌟ᴸᶠᵗᵇ-unitˡ {†ᴸᶠᵗᵇ} =  refl
  ⌞⌟ᴸᶠᵗᵇ-unitˡ {↯ᴸᶠᵗᵇ} =  refl

  -- ⌞ ⌟ᴸᶠᵗᵇ is idempotent

  ⌞⌟ᴸᶠᵗᵇ-idem :  ⌞ ⌞ a ⌟ᴸᶠᵗᵇ ⌟ᴸᶠᵗᵇ  ≡  ⌞ a ⌟ᴸᶠᵗᵇ
  ⌞⌟ᴸᶠᵗᵇ-idem {εᴸᶠᵗᵇ} =  refl
  ⌞⌟ᴸᶠᵗᵇ-idem {#ᴸᶠᵗᵇ _} =  refl
  ⌞⌟ᴸᶠᵗᵇ-idem {†ᴸᶠᵗᵇ} =  refl
  ⌞⌟ᴸᶠᵗᵇ-idem {↯ᴸᶠᵗᵇ} =  refl

  -- ✓ᴸᶠᵗᵇ respects ≈ᴸᶠᵗᵇ

  ✓ᴸᶠᵗᵇ-resp :  a ≈ᴸᶠᵗᵇ b →  ✓ᴸᶠᵗᵇ a →  ✓ᴸᶠᵗᵇ b
  ✓ᴸᶠᵗᵇ-resp {εᴸᶠᵗᵇ} {εᴸᶠᵗᵇ} _ _ =  _
  ✓ᴸᶠᵗᵇ-resp {#ᴸᶠᵗᵇ p} {#ᴸᶠᵗᵇ q} p≈q p≤1 =  ≤1ᴿ⁺-resp {p} {q} p≈q p≤1
  ✓ᴸᶠᵗᵇ-resp {†ᴸᶠᵗᵇ} {†ᴸᶠᵗᵇ} _ _ =  _

  -- ✓ᴸᶠᵗᵇ is preserved by removal w.r.t. ∙ᴸᶠᵗᵇ

  ✓ᴸᶠᵗᵇ-rem :  ✓ᴸᶠᵗᵇ a ∙ᴸᶠᵗᵇ b →  ✓ᴸᶠᵗᵇ b
  ✓ᴸᶠᵗᵇ-rem {εᴸᶠᵗᵇ} =  id
  ✓ᴸᶠᵗᵇ-rem {_} {εᴸᶠᵗᵇ} _ =  _
  ✓ᴸᶠᵗᵇ-rem {_} {†ᴸᶠᵗᵇ} _ =  _
  ✓ᴸᶠᵗᵇ-rem {#ᴸᶠᵗᵇ p} {#ᴸᶠᵗᵇ q} p+q≤1 =  ≤1ᴿ⁺-rem {p} {q} p+q≤1

--------------------------------------------------------------------------------
-- Lftbᴱᴿᴬ :  Lifetime box ERA

Lftbᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
Lftbᴱᴿᴬ .Res =  Lftb
Lftbᴱᴿᴬ ._≈_ =  _≈ᴸᶠᵗᵇ_
Lftbᴱᴿᴬ ._∙_ =  _∙ᴸᶠᵗᵇ_
Lftbᴱᴿᴬ .ε =  εᴸᶠᵗᵇ
Lftbᴱᴿᴬ .⌞_⌟ =  ⌞_⌟ᴸᶠᵗᵇ
Lftbᴱᴿᴬ .Env =  ⊤
Lftbᴱᴿᴬ ._✓_ _ =  ✓ᴸᶠᵗᵇ_
Lftbᴱᴿᴬ .refl˜ =  ≈ᴸᶠᵗᵇ-refl
Lftbᴱᴿᴬ .◠˜_ a≈b =  ≈ᴸᶠᵗᵇ-sym a≈b
Lftbᴱᴿᴬ ._◇˜_ a≈b b≈c =  ≈ᴸᶠᵗᵇ-trans a≈b b≈c
Lftbᴱᴿᴬ .∙-congˡ =  ∙ᴸᶠᵗᵇ-congˡ
Lftbᴱᴿᴬ .∙-unitˡ =  ≈ᴸᶠᵗᵇ-refl
Lftbᴱᴿᴬ .∙-comm {a} =  ≡⇒≈ᴸᶠᵗᵇ $ ∙ᴸᶠᵗᵇ-comm {a}
Lftbᴱᴿᴬ .∙-assocʳ {a} =  ≡⇒≈ᴸᶠᵗᵇ $ ∙ᴸᶠᵗᵇ-assocʳ {a}
Lftbᴱᴿᴬ .⌞⌟-cong =  ⌞⌟ᴸᶠᵗᵇ-cong
Lftbᴱᴿᴬ .⌞⌟-add {a}  with ⌞⌟ᴸᶠᵗᵇ-add {a}
… | a' , ≡a'∙ =  a' , ≡⇒≈ᴸᶠᵗᵇ ≡a'∙
Lftbᴱᴿᴬ .⌞⌟-unitˡ =  ≡⇒≈ᴸᶠᵗᵇ $ ⌞⌟ᴸᶠᵗᵇ-unitˡ
Lftbᴱᴿᴬ .⌞⌟-idem =  ≡⇒≈ᴸᶠᵗᵇ $ ⌞⌟ᴸᶠᵗᵇ-idem
Lftbᴱᴿᴬ .✓-resp =  ✓ᴸᶠᵗᵇ-resp
Lftbᴱᴿᴬ .✓-rem {a = a} =  ✓ᴸᶠᵗᵇ-rem {a}

open ERA Lftbᴱᴿᴬ public using () renaming (_↝_ to _↝ᴸᶠᵗᵇ_)

abstract

  -- Turn #ᴸᶠᵗᵇ 1ᴿ⁺ into †ᴸᶠᵗᵇ

  #ᴸᶠᵗᵇ-kill :  (-, #ᴸᶠᵗᵇ 1ᴿ⁺)  ↝ᴸᶠᵗᵇ λ (_ : ⊤₀) →  -,  †ᴸᶠᵗᵇ
  #ᴸᶠᵗᵇ-kill εᴸᶠᵗᵇ _ =  _
  #ᴸᶠᵗᵇ-kill (#ᴸᶠᵗᵇ p) 1+p≤1 =  absurd $ ¬1+?≤1ᴿ⁺ {p} 1+p≤1

--------------------------------------------------------------------------------
-- Lftᴱᴿᴬ :  Lifetime ERA

module FinLft =  Syho.Model.ERA.Fin Lftbᴱᴿᴬ (λ{a} → ≈ᴸᶠᵗᵇε-rem {a})
open FinLft public using () renaming (
  --  Lft'ᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
  Finᴱᴿᴬ to Lft'ᴱᴿᴬ;
  --  inj˙ᴸᶠᵗ :  Lft →  Lftb →  Lft →  Lftb
  inj˙ to inj˙ᴸᶠᵗ;
  inj˙-≈ to inj˙ᴸᶠᵗ-≈; inj˙-∙ to inj˙ᴸᶠᵗ-∙; inj˙-⌞⌟ to inj˙ᴸᶠᵗ-⌞⌟;
  ↝ᶠⁱⁿ-new to ↝ᴸᶠᵗ-new; inj˙-↝ᶠⁱⁿ to inj˙-↝ᴸᶠᵗ)

Lftᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
Lftᴱᴿᴬ =  Upᴱᴿᴬ Lft'ᴱᴿᴬ

open ERA Lftᴱᴿᴬ public using () renaming (Res to Resᴸᶠᵗ; _≈_ to _≈ᴸᶠᵗ_;
  _∙_ to _∙ᴸᶠᵗ_; ε to εᴸᶠᵗ; ⌞_⌟ to ⌞_⌟ᴸᶠᵗ; _✓_ to _✓ᴸᶠᵗ_; _↝_ to _↝ᴸᶠᵗ_;
  ◠˜_ to ◠˜ᴸᶠᵗ_)

-- [ ]ᴸ⟨ ⟩ʳ :  Resource for the lifetime token

[_]ᴸ⟨_⟩ʳ :  Lft →  ℚ⁺ →  Resᴸᶠᵗ
[ α ]ᴸ⟨ p ⟩ʳ .↓ =  inj˙ᴸᶠᵗ α $ #ᴸᶠᵗᵇ p

[_]ᴸʳ :  Lft →  Resᴸᶠᵗ
[ α ]ᴸʳ =  [ α ]ᴸ⟨ 1ᴿ⁺ ⟩ʳ

-- †ᴸʳ :  Resource for the dead lifetime token

infix 8 †ᴸʳ_
†ᴸʳ_ :  Lft →  Resᴸᶠᵗ
(†ᴸʳ α) .↓ =  inj˙ᴸᶠᵗ α †ᴸᶠᵗᵇ

abstract

  -- εᴸᶠᵗ is valid

  ✓ᴸᶠᵗε :  _ ✓ᴸᶠᵗ εᴸᶠᵗ
  ✓ᴸᶠᵗε .↓ =  (0 ,-) ,-

  -- Modify the fraction of [ ]ᴸ⟨ ⟩ʳ

  []ᴸ⟨⟩ʳ-cong :  p ≈ᴿ⁺ q  →   [ α ]ᴸ⟨ p ⟩ʳ  ≈ᴸᶠᵗ  [ α ]ᴸ⟨ q ⟩ʳ
  []ᴸ⟨⟩ʳ-cong p≈q .↓ =  inj˙ᴸᶠᵗ-≈ p≈q

  -- Merge [ ]ᴸ⟨ ⟩ʳ w.r.t. +ᴿ⁺

  []ᴸ⟨⟩ʳ-∙ :  [ α ]ᴸ⟨ p ⟩ʳ ∙ᴸᶠᵗ [ α ]ᴸ⟨ q ⟩ʳ  ≈ᴸᶠᵗ  [ α ]ᴸ⟨ p +ᴿ⁺ q ⟩ʳ
  []ᴸ⟨⟩ʳ-∙ .↓ =  inj˙ᴸᶠᵗ-∙

  -- The fraction of [ ]ᴸ⟨ ⟩ʳ is no more than 1

  []ᴸ⟨⟩ʳ-≤1 :  _ ✓ᴸᶠᵗ [ α ]ᴸ⟨ p ⟩ʳ →  p ≤1ᴿ⁺
  []ᴸ⟨⟩ʳ-≤1 {α} (↑ (-, ✓αp))  with ✓αp α
  … | ✓#p  rewrite ≟-refl {a = α} =  ✓#p

  -- †ᴸʳ absorbs ⌞ ⌟ᴸᶠᵗ

  †ᴸʳ-⌞⌟ :  ⌞ †ᴸʳ α ⌟ᴸᶠᵗ  ≈ᴸᶠᵗ  †ᴸʳ α
  †ᴸʳ-⌞⌟ .↓ =  inj˙ᴸᶠᵗ-⌞⌟

  -- [ α ]ᴸ⟨ p ⟩ʳ and †ᴸʳ α cannot coexist

  []ᴸ⟨⟩ʳ-†ᴸʳ-no :  ¬ _ ✓ᴸᶠᵗ [ α ]ᴸ⟨ p ⟩ʳ ∙ᴸᶠᵗ †ᴸʳ α
  []ᴸ⟨⟩ʳ-†ᴸʳ-no {α} (↑ (-, ✓αp∙†α))  with ✓αp∙†α α
  … | ✓#p∙†  rewrite ≟-refl {a = α} =  ✓#p∙†

  -- Allocate a new lifetime

  []ᴸʳ-new :  (-, εᴸᶠᵗ)  ↝ᴸᶠᵗ λ α →  -, [ α ]ᴸʳ
  []ᴸʳ-new (↑ b˙) (↑ ✓b)  with ↝ᴸᶠᵗ-new 1≤1ᴿ⁺ b˙ ✓b
  … | α , ✓[α]∙b =  α , ↑ ✓[α]∙b

  -- Kill a lifetime consuming a full lifetime token

  []ᴸʳ-kill :  (-, [ α ]ᴸʳ)  ↝ᴸᶠᵗ λ (_ : ⊤₀) →  -,  †ᴸʳ α
  []ᴸʳ-kill (↑ b˙) (↑ ✓[α]∙b)  with inj˙-↝ᴸᶠᵗ (λ ()) #ᴸᶠᵗᵇ-kill b˙ ✓[α]∙b
  … | -, ✓†α∙b =  -, ↑ ✓†α∙b
