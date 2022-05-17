--------------------------------------------------------------------------------
-- Positive rational number
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.RatPos where

open import Base.NatPos using (ℕ⁺; 1⁺; 2⁺; _+⁺_; _*⁺_; _≡⁺ᵇ_; _≤⁺_; _<⁺_;
  +⁺-comm; +⁺-assocˡ; +⁺-assocʳ; *⁺-comm; *⁺-assocˡ; *⁺-assocʳ; *⁺-+⁺-distrʳ;
  *⁺-injʳ; *⁺-actˡ-comm; *⁺-actʳ-comm; +⁺-sincrˡ; ≡⁺ᵇ⇒≡; ≡⇒≡⁺ᵇ; ≤⁺->⁺-no)
open import Base.Eq using (_≡_; refl⁼; sym⁼; _»⁼_; cong⁼; cong⁼₂; subst; subst₂)
open import Base.Func using (_$_; flip)
open import Base.Bool using (Bool; Tt)
open import Base.Few using (¬_)

--------------------------------------------------------------------------------
-- ℚ⁺: Positive rational number

infix 7 _//⁺_
record  ℚ⁺ : Set where
  constructor _//⁺_
  field
    denom⁺ numer⁺ : ℕ⁺ --  denominator and numerator

-- We use the superscript ᴿ for rational numbers
-- (superscipt Q is not widely supported)

private variable
  p q r s :  ℚ⁺

--------------------------------------------------------------------------------
-- 1ᴿ⁺, ½ᴿ⁺: Numbers in ℚ⁺

1ᴿ⁺ ½⁺ :  ℚ⁺
1ᴿ⁺ =  1⁺ //⁺ 1⁺
½⁺ =  1⁺ //⁺ 2⁺

--------------------------------------------------------------------------------
-- ≈ᴿ⁺: Equivalence over ℚ⁺

infix 4 _≈ᴿ⁺_
_≈ᴿ⁺_ : ℚ⁺ → ℚ⁺ → Set
(a //⁺ b) ≈ᴿ⁺ (c //⁺ d) =  d *⁺ a ≡ b *⁺ c

abstract

  -- ≈ᴿ⁺ is reflexive

  ≈ᴿ⁺-refl :  p ≈ᴿ⁺ p
  ≈ᴿ⁺-refl {a //⁺ b} =  refl⁼

  ≡⇒≈ᴿ⁺ :  p ≡ q →  p ≈ᴿ⁺ q
  ≡⇒≈ᴿ⁺ {p} refl⁼ =  ≈ᴿ⁺-refl {p}

  -- ≈ᴿ⁺ is symmetric

  ≈ᴿ⁺-sym :  p ≈ᴿ⁺ q →  q ≈ᴿ⁺ p
  ≈ᴿ⁺-sym {a //⁺ b} {c //⁺ d} =  sym⁼

  -- ≈ᴿ⁺ is transitive

  ≈ᴿ⁺-trans :  p ≈ᴿ⁺ q →  q ≈ᴿ⁺ r →  p ≈ᴿ⁺ r
  ≈ᴿ⁺-trans {a //⁺ b} {c //⁺ d} {e //⁺ f} da≡bc fc≡de =  *⁺-injʳ {d} eq
   where
    eq :  d *⁺ (f *⁺ a) ≡ d *⁺ (b *⁺ e)
    eq =  cong⁼ (d *⁺_) (*⁺-comm {f} {a}) »⁼ *⁺-assocʳ {d} {a} {f} »⁼
      cong⁼ (_*⁺ f) da≡bc »⁼ *⁺-assocˡ {b} {c} {f} »⁼
      cong⁼ (b *⁺_) (*⁺-comm {c} {f} »⁼ fc≡de) »⁼ *⁺-actˡ-comm {b} {d} {e}

--------------------------------------------------------------------------------
-- ≈ᴿ⁺ᵇ: Boolean equivalence over ℚ⁺

infix 4 _≈ᴿ⁺ᵇ_
_≈ᴿ⁺ᵇ_ : ℚ⁺ → ℚ⁺ → Bool
(a //⁺ b) ≈ᴿ⁺ᵇ (c //⁺ d) =  d *⁺ a ≡⁺ᵇ b *⁺ c

abstract

  -- Conversion between ≈ᴿ⁺ᵇ and ≈ᴿ⁺

  ≈ᴿ⁺ᵇ⇒≈ᴿ⁺ :  Tt (p ≈ᴿ⁺ᵇ q) →  p ≈ᴿ⁺ q
  ≈ᴿ⁺ᵇ⇒≈ᴿ⁺ *≡⁺ᵇ* =  ≡⁺ᵇ⇒≡ *≡⁺ᵇ*

  ≈ᴿ⁺⇒≈ᴿ⁺ᵇ :  p ≈ᴿ⁺ q →  Tt (p ≈ᴿ⁺ᵇ q)
  ≈ᴿ⁺⇒≈ᴿ⁺ᵇ *≡⁺* =  ≡⇒≡⁺ᵇ *≡⁺*

--------------------------------------------------------------------------------
-- +ᴿ⁺: Addition over ℚ⁺

infixl 6 _+ᴿ⁺_
_+ᴿ⁺_ :  ℚ⁺ → ℚ⁺ → ℚ⁺
(a //⁺ b) +ᴿ⁺ (c //⁺ d) =  (d *⁺ a +⁺ b *⁺ c) //⁺ (b *⁺ d)
-- Unnormalized

abstract

  -- +ᴿ⁺ is commutative

  +ᴿ⁺-comm :  p +ᴿ⁺ q ≡ q +ᴿ⁺ p
  +ᴿ⁺-comm {a //⁺ b} {c //⁺ d} =  cong⁼₂ _//⁺_ +⁺-comm (*⁺-comm {b} {d})

  -- +ᴿ⁺ is associative

  +ᴿ⁺-assocˡ :  (p +ᴿ⁺ q) +ᴿ⁺ r ≡ p +ᴿ⁺ (q +ᴿ⁺ r)
  +ᴿ⁺-assocˡ {a //⁺ b} {c //⁺ d} {e //⁺ f} =
    cong⁼₂ _//⁺_ eq (*⁺-assocˡ {b} {d} {f})
   where
    eq :  f *⁺ (d *⁺ a +⁺ b *⁺ c) +⁺ (b *⁺ d) *⁺ e ≡
          (d *⁺ f) *⁺ a +⁺ b *⁺ (f *⁺ c +⁺ d *⁺ e)
    eq =
      flip (cong⁼₂ _+⁺_) (*⁺-assocˡ {b} {d} {e})
        (*⁺-+⁺-distrʳ {f} {d *⁺ a} {b *⁺ c} »⁼
          cong⁼₂ _+⁺_ (*⁺-actˡ-comm {f} {d} {a} »⁼ *⁺-assocʳ {d} {f} {a})
            (*⁺-actˡ-comm {f} {b} {c})) »⁼
      +⁺-assocˡ »⁼ cong⁼ (d *⁺ f *⁺ a +⁺_) $ sym⁼ $ *⁺-+⁺-distrʳ {b}

  +ᴿ⁺-assocʳ :  p +ᴿ⁺ (q +ᴿ⁺ r) ≡ (p +ᴿ⁺ q) +ᴿ⁺ r
  +ᴿ⁺-assocʳ {p} {q} {r} =  sym⁼ (+ᴿ⁺-assocˡ {p} {q} {r})

  -- +ᴿ⁺ is congruent

  +ᴿ⁺-congˡ :  p ≈ᴿ⁺ q →  p +ᴿ⁺ r ≈ᴿ⁺ q +ᴿ⁺ r
  +ᴿ⁺-congˡ {a //⁺ b} {c //⁺ d} {e //⁺ f} da≡bc =
    *⁺-actʳ-comm {d} {f} »⁼ cong⁼ (_*⁺ f) eq »⁼ *⁺-actʳ-comm {b} {_} {f}
    -- (d *⁺ f) *⁺ (f *⁺ a +⁺ b *⁺ e) ≡ (b *⁺ f) *⁺ (f *⁺ c +⁺ d *⁺ e)
   where
    eq :  d *⁺ (f *⁺ a +⁺ b *⁺ e) ≡ b *⁺ (f *⁺ c +⁺ d *⁺ e)
    eq =  *⁺-+⁺-distrʳ {d} »⁼
      flip (cong⁼₂ _+⁺_) (*⁺-actˡ-comm {d} {b})
        (*⁺-actˡ-comm {d} {f} »⁼ cong⁼ (f *⁺_) da≡bc »⁼ *⁺-actˡ-comm {f} {b}) »⁼
      sym⁼ $ *⁺-+⁺-distrʳ {b}

  +ᴿ⁺-congʳ :  ∀ {p q r} →  q ≈ᴿ⁺ r →  p +ᴿ⁺ q ≈ᴿ⁺ p +ᴿ⁺ r
  +ᴿ⁺-congʳ {p} {q} {r} q≈r =  subst₂ _≈ᴿ⁺_
    (+ᴿ⁺-comm {q} {p}) (+ᴿ⁺-comm {r} {p}) (+ᴿ⁺-congˡ {q} {r} {p} q≈r)

  +ᴿ⁺-cong :  p ≈ᴿ⁺ q →  r ≈ᴿ⁺ s →  p +ᴿ⁺ r ≈ᴿ⁺ q +ᴿ⁺ s
  +ᴿ⁺-cong {p} {q} {r} {s} p≈q r≈s =  ≈ᴿ⁺-trans {p +ᴿ⁺ r} {q +ᴿ⁺ r} {q +ᴿ⁺ s}
    (+ᴿ⁺-congˡ {p} {q} {r} p≈q) (+ᴿ⁺-congʳ {q} {r} {s} r≈s)

--------------------------------------------------------------------------------
-- /⁺: Dividing ℚ⁺ with ℕ⁺

infixl 7 _/⁺_
_/⁺_ :  ℚ⁺ → ℕ⁺ → ℚ⁺
(a //⁺ b) /⁺ c =  a //⁺ (b *⁺ c)

--------------------------------------------------------------------------------
-- ≤1ᴿ⁺: No more than 1ᴿ⁺

≤1ᴿ⁺ :  ℚ⁺ → Set
≤1ᴿ⁺ (a //⁺ b) =  a ≤⁺ b

abstract

  ?+1ᴿ⁺-not-≤1ᴿ⁺ :  ¬  ≤1ᴿ⁺ (p +ᴿ⁺ 1ᴿ⁺)
  ?+1ᴿ⁺-not-≤1ᴿ⁺ {a //⁺ b} 1a+b1≤b1 =  ≤⁺->⁺-no 1a+b1≤b1 +⁺-sincrˡ

  1ᴿ⁺+?-not-≤1ᴿ⁺ :  ¬  ≤1ᴿ⁺ (1ᴿ⁺ +ᴿ⁺ p)
  1ᴿ⁺+?-not-≤1ᴿ⁺ {p} =  subst (λ q → ¬ ≤1ᴿ⁺ q) (+ᴿ⁺-comm {p} {1ᴿ⁺}) $
    ?+1ᴿ⁺-not-≤1ᴿ⁺ {p}
