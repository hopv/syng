--------------------------------------------------------------------------------
-- Lifetime ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Syho.Model.ERA.Lft where

open import Base.Level using (0ᴸ; 1ᴸ; ↑_; ↓)
open import Base.Func using (_$_; id)
open import Base.Few using (⊤; ⊥; ¬_; absurd)
open import Base.Eq using (_≡_; refl; cong)
open import Base.Dec using (≟-refl)
open import Base.Prod using (∑-syntax; _×_; _,_; -,_; _,-)
open import Base.Nat using (ℕ)
open import Base.Ratp using (ℚ⁺; _≈ᴿ⁺_; 1ᴿ⁺; _+ᴿ⁺_; _≤1ᴿ⁺; ≈ᴿ⁺-refl; ≈ᴿ⁺-sym;
  ≈ᴿ⁺-trans; +ᴿ⁺-congˡ; +ᴿ⁺-comm; +ᴿ⁺-assocˡ; ≤1ᴿ⁺-resp; 1≤1ᴿ⁺; ≤1ᴿ⁺-rem)
open import Syho.Model.ERA.Base using (ERA; Valmᴱᴿᴬ; Upᴱᴿᴬ)
import Syho.Model.ERA.Fin

open ERA using (Res; _≈_; _∙_; ε; ⌞_⌟; Env; _✓_; refl˜; ◠˜_; _◇˜_; ∙-congˡ;
  ∙-unitˡ; ∙-comm; ∙-assocˡ; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem; ✓-resp; ✓-rem)

private
  Lft :  Set₀
  Lft =  ℕ

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

-- Equivalence of Lftb

infix 4 _≈ᴸᵇ_
_≈ᴸᵇ_ :  Lftb →  Lftb →  Set₀
εᴸᵇ ≈ᴸᵇ εᴸᵇ =  ⊤
#ᴸᵇ p ≈ᴸᵇ #ᴸᵇ q =  p ≈ᴿ⁺ q
†ᴸᵇ ≈ᴸᵇ †ᴸᵇ =  ⊤
↯ᴸᵇ ≈ᴸᵇ ↯ᴸᵇ =  ⊤
_ ≈ᴸᵇ _ =  ⊥

-- Product of Lftb

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

  -- ≈ᴸᵇ is reflexive

  ≈ᴸᵇ-refl :  a ≈ᴸᵇ a
  ≈ᴸᵇ-refl {εᴸᵇ} =  _
  ≈ᴸᵇ-refl {#ᴸᵇ p} =  ≈ᴿ⁺-refl {p}
  ≈ᴸᵇ-refl {†ᴸᵇ} =  _
  ≈ᴸᵇ-refl {↯ᴸᵇ} =  _

  ≡⇒≈ᴸᵇ :  a ≡ b →  a ≈ᴸᵇ b
  ≡⇒≈ᴸᵇ refl =  ≈ᴸᵇ-refl

  -- ≈ᴸᵇ is symmetric

  ≈ᴸᵇ-sym :  a ≈ᴸᵇ b →  b ≈ᴸᵇ a
  ≈ᴸᵇ-sym {εᴸᵇ} {εᴸᵇ} _ =  _
  ≈ᴸᵇ-sym {#ᴸᵇ p} {#ᴸᵇ q} p≈q =  ≈ᴿ⁺-sym {p} {q} p≈q
  ≈ᴸᵇ-sym {†ᴸᵇ} {†ᴸᵇ} _ =  _
  ≈ᴸᵇ-sym {↯ᴸᵇ} {↯ᴸᵇ} _ =  _

  -- ≈ᴸᵇ is transitive

  ≈ᴸᵇ-trans :  a ≈ᴸᵇ b →  b ≈ᴸᵇ c →  a ≈ᴸᵇ c
  ≈ᴸᵇ-trans {εᴸᵇ} {εᴸᵇ} {εᴸᵇ} _ _ =  _
  ≈ᴸᵇ-trans {#ᴸᵇ p} {#ᴸᵇ q} {#ᴸᵇ r} p≈q q≈r =  ≈ᴿ⁺-trans {p} {q} {r} p≈q q≈r
  ≈ᴸᵇ-trans {†ᴸᵇ} {†ᴸᵇ} {†ᴸᵇ} _ _ =  _
  ≈ᴸᵇ-trans {↯ᴸᵇ} {↯ᴸᵇ} {↯ᴸᵇ} _ _ =  _

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

  -- ∙ᴸᵇ preserves ≈ᴸᵇ

  ∙ᴸᵇ-congˡ :  a ≈ᴸᵇ b  →   a ∙ᴸᵇ c  ≈ᴸᵇ  b ∙ᴸᵇ c
  ∙ᴸᵇ-congˡ {εᴸᵇ} {εᴸᵇ} _ =  ≈ᴸᵇ-refl
  ∙ᴸᵇ-congˡ {†ᴸᵇ} {†ᴸᵇ} _ =  ≈ᴸᵇ-refl
  ∙ᴸᵇ-congˡ {↯ᴸᵇ} {↯ᴸᵇ} _ =  _
  ∙ᴸᵇ-congˡ {a} {b} {εᴸᵇ} a≈b  rewrite ∙ᴸᵇ-ε {a} | ∙ᴸᵇ-ε {b} =  a≈b
  ∙ᴸᵇ-congˡ {a} {b} {↯ᴸᵇ} a≈b  rewrite ∙ᴸᵇ-↯ {a} | ∙ᴸᵇ-↯ {b} =  _
  ∙ᴸᵇ-congˡ {#ᴸᵇ p} {#ᴸᵇ q} {#ᴸᵇ r} p≈q =  +ᴿ⁺-congˡ {p} {q} {r} p≈q
  ∙ᴸᵇ-congˡ {#ᴸᵇ _} {#ᴸᵇ _} {†ᴸᵇ} _ =  _

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
  ∙ᴸᵇ-assocˡ {a} {εᴸᵇ}  rewrite ∙ᴸᵇ-ε {a} =  refl
  ∙ᴸᵇ-assocˡ {a} {b} {εᴸᵇ}  rewrite ∙ᴸᵇ-ε {a ∙ᴸᵇ b} | ∙ᴸᵇ-ε {b} =  refl
  ∙ᴸᵇ-assocˡ {a} {↯ᴸᵇ}  rewrite ∙ᴸᵇ-↯ {a} =  refl
  ∙ᴸᵇ-assocˡ {a} {b} {↯ᴸᵇ}  rewrite ∙ᴸᵇ-↯ {a ∙ᴸᵇ b} | ∙ᴸᵇ-↯ {b} | ∙ᴸᵇ-↯ {a} =
    refl
  ∙ᴸᵇ-assocˡ {†ᴸᵇ} {†ᴸᵇ} {†ᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {†ᴸᵇ} {†ᴸᵇ} {#ᴸᵇ _} =  refl
  ∙ᴸᵇ-assocˡ {†ᴸᵇ} {#ᴸᵇ _} {†ᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {†ᴸᵇ} {#ᴸᵇ _} {#ᴸᵇ _} =  refl
  ∙ᴸᵇ-assocˡ {#ᴸᵇ _} {†ᴸᵇ} {†ᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {#ᴸᵇ _} {†ᴸᵇ} {#ᴸᵇ _} =  refl
  ∙ᴸᵇ-assocˡ {#ᴸᵇ _} {#ᴸᵇ _} {†ᴸᵇ} =  refl
  ∙ᴸᵇ-assocˡ {#ᴸᵇ p} {#ᴸᵇ q} {#ᴸᵇ _} =  cong #ᴸᵇ_ $ +ᴿ⁺-assocˡ {p} {q}

  -- ≈ᴸᵇ εᴸᵇ is preserved by removal w.r.t. ∙ᴸᵇ

  ≈ᴸᵇε-rem :  a ∙ᴸᵇ b ≈ᴸᵇ εᴸᵇ →  b ≈ᴸᵇ εᴸᵇ
  ≈ᴸᵇε-rem {εᴸᵇ} {εᴸᵇ} _ =  _
  ≈ᴸᵇε-rem {↯ᴸᵇ} ()

  -- ⌞⌟ᴸᵇ preserves ≈ᴸᵇ

  ⌞⌟ᴸᵇ-cong :  a ≈ᴸᵇ b  →   ⌞ a ⌟ᴸᵇ  ≈ᴸᵇ  ⌞ b ⌟ᴸᵇ
  ⌞⌟ᴸᵇ-cong {εᴸᵇ} {εᴸᵇ} _ =  _
  ⌞⌟ᴸᵇ-cong {#ᴸᵇ _} {#ᴸᵇ _} _ =  _
  ⌞⌟ᴸᵇ-cong {†ᴸᵇ} {†ᴸᵇ} _ =  _
  ⌞⌟ᴸᵇ-cong {↯ᴸᵇ} {↯ᴸᵇ} _ =  _

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

  -- ✓ᴸᵇ respects ≈ᴸᵇ

  ✓ᴸᵇ-resp :  a ≈ᴸᵇ b →  ✓ᴸᵇ a →  ✓ᴸᵇ b
  ✓ᴸᵇ-resp {εᴸᵇ} {εᴸᵇ} _ _ =  _
  ✓ᴸᵇ-resp {#ᴸᵇ p} {#ᴸᵇ q} p≈q p≤1 =  ≤1ᴿ⁺-resp {p} {q} p≈q p≤1
  ✓ᴸᵇ-resp {†ᴸᵇ} {†ᴸᵇ} _ _ =  _

  -- ✓ᴸᵇ is preserved by removal w.r.t. ∙ᴸᵇ

  ✓ᴸᵇ-rem :  ✓ᴸᵇ a ∙ᴸᵇ b →  ✓ᴸᵇ b
  ✓ᴸᵇ-rem {εᴸᵇ} =  id
  ✓ᴸᵇ-rem {_} {εᴸᵇ} _ =  _
  ✓ᴸᵇ-rem {_} {†ᴸᵇ} _ =  _
  ✓ᴸᵇ-rem {#ᴸᵇ p} {#ᴸᵇ q} p+q≤1 =  ≤1ᴿ⁺-rem {p} {q} p+q≤1

--------------------------------------------------------------------------------
-- Lftbᴱᴿᴬ :  Lifetime box ERA

Lftbᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
Lftbᴱᴿᴬ .Res =  Lftb
Lftbᴱᴿᴬ ._≈_ =  _≈ᴸᵇ_
Lftbᴱᴿᴬ ._∙_ =  _∙ᴸᵇ_
Lftbᴱᴿᴬ .ε =  εᴸᵇ
Lftbᴱᴿᴬ .⌞_⌟ =  ⌞_⌟ᴸᵇ
Lftbᴱᴿᴬ .Env =  ⊤
Lftbᴱᴿᴬ ._✓_ _ =  ✓ᴸᵇ_
Lftbᴱᴿᴬ .refl˜ =  ≈ᴸᵇ-refl
Lftbᴱᴿᴬ .◠˜_ a≈b =  ≈ᴸᵇ-sym a≈b
Lftbᴱᴿᴬ ._◇˜_ a≈b b≈c =  ≈ᴸᵇ-trans a≈b b≈c
Lftbᴱᴿᴬ .∙-congˡ =  ∙ᴸᵇ-congˡ
Lftbᴱᴿᴬ .∙-unitˡ =  ≈ᴸᵇ-refl
Lftbᴱᴿᴬ .∙-comm {a} =  ≡⇒≈ᴸᵇ $ ∙ᴸᵇ-comm {a}
Lftbᴱᴿᴬ .∙-assocˡ {a} =  ≡⇒≈ᴸᵇ $ ∙ᴸᵇ-assocˡ {a}
Lftbᴱᴿᴬ .⌞⌟-cong =  ⌞⌟ᴸᵇ-cong
Lftbᴱᴿᴬ .⌞⌟-add {a}  with ⌞⌟ᴸᵇ-add {a}
… | a' , ≡a'∙ =  a' , ≡⇒≈ᴸᵇ ≡a'∙
Lftbᴱᴿᴬ .⌞⌟-unitˡ =  ≡⇒≈ᴸᵇ $ ⌞⌟ᴸᵇ-unitˡ
Lftbᴱᴿᴬ .⌞⌟-idem =  ≡⇒≈ᴸᵇ $ ⌞⌟ᴸᵇ-idem
Lftbᴱᴿᴬ .✓-resp =  ✓ᴸᵇ-resp
Lftbᴱᴿᴬ .✓-rem {a = a} =  ✓ᴸᵇ-rem {a}

--------------------------------------------------------------------------------
-- Lftᴱᴿᴬ :  Lifetime ERA

module FinLft =  Syho.Model.ERA.Fin Lftbᴱᴿᴬ (λ{a} → ≈ᴸᵇε-rem {a})
open FinLft public using () renaming (
  --  Lft'ᴱᴿᴬ :  ERA 0ᴸ 0ᴸ 0ᴸ 0ᴸ
  Finᴱᴿᴬ to Lft'ᴱᴿᴬ;
  --  inj˙ᴸᶠᵗ :  Lft →  Lftb →  Lft →  Lftb
  inj˙ to inj˙ᴸᶠᵗ;
  inj˙-≈ to inj˙ᴸᶠᵗ-≈; inj˙-∙ to inj˙ᴸᶠᵗ-∙; inj˙-⌞⌟ to inj˙ᴸᶠᵗ-⌞⌟)
open FinLft using (✓-new)

Lftᴱᴿᴬ :  ERA 1ᴸ 1ᴸ 1ᴸ 1ᴸ
Lftᴱᴿᴬ =  Upᴱᴿᴬ Lft'ᴱᴿᴬ

open ERA Lftᴱᴿᴬ public using () renaming (Res to Resᴸᶠᵗ; _≈_ to _≈ᴸᶠᵗ_;
  _∙_ to _∙ᴸᶠᵗ_; ε to εᴸᶠᵗ; ⌞_⌟ to ⌞_⌟ᴸᶠᵗ; _✓_ to _✓ᴸᶠᵗ_; _↝_ to _↝ᴸᶠᵗ_;
  ◠˜_ to ◠˜ᴸᶠᵗ_)

-- [ ]ᴸ⟨ ⟩ʳ :  Resource for the lifetime token

[_]ᴸ⟨_⟩ʳ :  Lft →  ℚ⁺ →  Resᴸᶠᵗ
[ α ]ᴸ⟨ p ⟩ʳ .↓ =  inj˙ᴸᶠᵗ α $ #ᴸᵇ p

[_]ᴸʳ :  Lft →  Resᴸᶠᵗ
[ α ]ᴸʳ =  [ α ]ᴸ⟨ 1ᴿ⁺ ⟩ʳ

-- †ᴸʳ :  Resource for the dead lifetime token

infix 8 †ᴸʳ_
†ᴸʳ_ :  Lft →  Resᴸᶠᵗ
(†ᴸʳ α) .↓ =  inj˙ᴸᶠᵗ α †ᴸᵇ

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
  []ᴸʳ-new (↑ b˙) (↑ ✓b)  with ✓-new 1≤1ᴿ⁺ b˙ ✓b
  … | α , ✓[α]∙b =  α , ↑ ✓[α]∙b
