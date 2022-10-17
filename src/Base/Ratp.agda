--------------------------------------------------------------------------------
-- Positive rational number
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Ratp where

open import Base.Func using (_$_; flip)
open import Base.Few using (¬_; absurd)
open import Base.Eq using (_≡_; refl; ◠_; _◇_; cong; cong₂; subst; subst₂)
open import Base.Dec using (Dec; yes; _≟_; ≟-refl)
open import Base.Sum using (_⨿_; ĩ₀_; ĩ₁_)
open import Base.Nat using (+-0; *-1ʳ)
open import Base.Natp using (ℕ⁺; 1⁺; 2⁺; ṡ⁺_; _≤⁺_; _<⁺_; _+⁺_; _*⁺_; ≤⁺-refl;
  ≡⇒≤⁺; ≤⁺-trans; ≤⁺-antisym; <⁺-irrefl; ≡⇒¬<⁺; <⁺-trans; <⁺-asym; <⁺⇒≤⁺;
  ≤⁺-<⁺-trans; <⁺-≤⁺-trans; ≤⁺⇒¬>⁺; <⁺⇒¬≥⁺; _<≡>⁺_; _≤>⁺_; _<≥⁺_; +⁺-comm;
  +⁺-assocˡ; +⁺-assocʳ; +⁺-sincrʳ; +⁺-monoˡ; *⁺-comm; *⁺-assocˡ; *⁺-assocʳ;
  *⁺-+⁺-distrʳ; ?*⁺-comm; *⁺?-comm; *⁺-2ˡ; *⁺-injʳ; *⁺-smonoʳ; *⁺-monoˡ;
  *⁺-monoʳ; *⁺-monoʳ-inv; *⁺-smonoʳ-inv)

--------------------------------------------------------------------------------
-- ℚ⁺ :  Positive rational number, unnormalized

infix 5 _⫽⁺_
record  ℚ⁺ : Set where
  constructor _⫽⁺_
  field
    denom⁺ numer⁺ : ℕ⁺ --  denominator and numerator

-- We use the superscript ᴿ for rational numbers
-- because superscipt Q or q is not widely supported in Unicode

private variable
  a b c :  ℕ⁺
  p q r s :  ℚ⁺

--------------------------------------------------------------------------------
-- 1ᴿ⁺, ½ᴿ⁺ :  Numbers in ℚ⁺

1ᴿ⁺ ½⁺ :  ℚ⁺
1ᴿ⁺ =  1⁺ ⫽⁺ 1⁺
½⁺ =  1⁺ ⫽⁺ 2⁺

instance

  -- ℚ⁺ is inhabited

  ℚ⁺-Dec :  Dec ℚ⁺
  ℚ⁺-Dec =  yes 1ᴿ⁺

--------------------------------------------------------------------------------
-- ≈ᴿ⁺ :  Equivalence of ℚ⁺

infix 4 _≈ᴿ⁺_
_≈ᴿ⁺_ : ℚ⁺ → ℚ⁺ → Set₀
(a ⫽⁺ b) ≈ᴿ⁺ (c ⫽⁺ d) =  d *⁺ a ≡ b *⁺ c

abstract

  -- ≈ᴿ⁺ is reflexive

  ≈ᴿ⁺-refl :  p ≈ᴿ⁺ p
  ≈ᴿ⁺-refl {a ⫽⁺ b} =  refl

  ≡⇒≈ᴿ⁺ :  p ≡ q →  p ≈ᴿ⁺ q
  ≡⇒≈ᴿ⁺ {p} refl =  ≈ᴿ⁺-refl {p}

  -- ≈ᴿ⁺ is symmetric

  ≈ᴿ⁺-sym :  p ≈ᴿ⁺ q →  q ≈ᴿ⁺ p
  ≈ᴿ⁺-sym {a ⫽⁺ b} {c ⫽⁺ d} =  ◠_

  -- ≈ᴿ⁺ is transitive

  ≈ᴿ⁺-trans :  p ≈ᴿ⁺ q →  q ≈ᴿ⁺ r →  p ≈ᴿ⁺ r
  ≈ᴿ⁺-trans {a ⫽⁺ b} {c ⫽⁺ d} {e ⫽⁺ f} da≡bc fc≡de =  *⁺-injʳ {d} eq
   where
    eq :  d *⁺ (f *⁺ a) ≡ d *⁺ (b *⁺ e)
    eq =
      -- d(fa) ≡ d(af) ≡ (da)f ≡ (bc)f ≡ b(cf) ≡ b(fc) ≡ b(de) ≡ d(be)
      cong (d *⁺_) (*⁺-comm {f} {a}) ◇ *⁺-assocˡ {d} {a} {f} ◇
      cong (_*⁺ f) da≡bc ◇ *⁺-assocʳ {b} {c} {f} ◇
      cong (b *⁺_) (*⁺-comm {c} {f} ◇ fc≡de) ◇ ?*⁺-comm {b} {d} {e}

  -- Cancel multiplication of the numerator and denominator by the same factor

  ⫽⁺-*ˡ :  c *⁺ a ⫽⁺ c *⁺ b  ≈ᴿ⁺  a ⫽⁺ b
  ⫽⁺-*ˡ {c} {a} {b} =  -- b(ca) ≡ c(ba) ≡ (cb)a
    ?*⁺-comm {b} {c} {a} ◇ *⁺-assocˡ {c} {b} {a}

  ⫽⁺-*ʳ :  a *⁺ c ⫽⁺ b *⁺ c  ≈ᴿ⁺  a ⫽⁺ b
  ⫽⁺-*ʳ {a} {c} {b} =  -- b(ac) ≡ (ba)c ≡ (bc)a
    *⁺-assocˡ {b} {a} {c} ◇ *⁺?-comm {b} {a} {c}

--------------------------------------------------------------------------------
-- ≤ᴿ⁺, >ᴿ⁺ :  Order of ℚ⁺

infix 4 _≤ᴿ⁺_ _≥ᴿ⁺_ _<ᴿ⁺_ _>ᴿ⁺_
_≤ᴿ⁺_ _≥ᴿ⁺_ _<ᴿ⁺_ _>ᴿ⁺_ :  ℚ⁺ → ℚ⁺ → Set₀
(a ⫽⁺ b) ≤ᴿ⁺ (c ⫽⁺ d) =  d *⁺ a ≤⁺ b *⁺ c
p ≥ᴿ⁺ q =  q ≤ᴿ⁺ p
(a ⫽⁺ b) <ᴿ⁺ (c ⫽⁺ d) =  d *⁺ a <⁺ b *⁺ c
p >ᴿ⁺ q =  q <ᴿ⁺ p

abstract

  -- ≤ᴿ⁺ is reflexive

  ≤ᴿ⁺-refl :  p ≤ᴿ⁺ p
  ≤ᴿ⁺-refl =  ≤⁺-refl

  ≡⇒≤ᴿ⁺ :  p ≡ q →  p ≤ᴿ⁺ q
  ≡⇒≤ᴿ⁺ {p} refl =  ≤ᴿ⁺-refl {p}

  -- ≤ᴿ⁺ is transitive

  ≤ᴿ⁺-trans :  p ≤ᴿ⁺ q →  q ≤ᴿ⁺ r →  p ≤ᴿ⁺ r
  ≤ᴿ⁺-trans {a ⫽⁺ b} {c ⫽⁺ d} {e ⫽⁺ f} da≤bc fc≤de =  *⁺-monoʳ-inv {d} $
    -- d(fa) ≡ f(da) ≤ f(bc) ≡ b(fc) ≤ b(de) ≡ d(be)
    ≤⁺-trans
      (subst₂ _≤⁺_ (?*⁺-comm {f} {d}) (?*⁺-comm {f} {b}) $ *⁺-monoʳ {f} da≤bc) $
      subst (b *⁺ (f *⁺ c) ≤⁺_) (?*⁺-comm {b} {d}) $ *⁺-monoʳ {b} fc≤de

  -- ≤ᴿ⁺ is antisymmetric

  ≤ᴿ⁺-antisym :  p ≤ᴿ⁺ q →  q ≤ᴿ⁺ p →  p ≈ᴿ⁺ q
  ≤ᴿ⁺-antisym p≤q q≤p =  ≤⁺-antisym p≤q q≤p

  -- ≈ᴿ⁺ into ≤ᴿ⁺

  ≈ᴿ⁺⇒≤ᴿ⁺ :  p ≈ᴿ⁺ q →  p ≤ᴿ⁺ q
  ≈ᴿ⁺⇒≤ᴿ⁺ =  ≡⇒≤⁺

  -- ≤ᴿ⁺ respects ≈ᴿ⁺

  ≤ᴿ⁺-respˡ :  p ≈ᴿ⁺ q →  p ≤ᴿ⁺ r →  q ≤ᴿ⁺ r
  ≤ᴿ⁺-respˡ {p} {q} {r} p≈q p≤r =
    ≤ᴿ⁺-trans {q} {p} {r} (≈ᴿ⁺⇒≤ᴿ⁺ {q} {p} $ ≈ᴿ⁺-sym {p} {q} p≈q) p≤r

  ≤ᴿ⁺-respʳ :  ∀{p q r} →  q ≈ᴿ⁺ r →  p ≤ᴿ⁺ q →  p ≤ᴿ⁺ r
  ≤ᴿ⁺-respʳ {p} {q} {r} q≈r p≤q =
    ≤ᴿ⁺-trans {p} {q} {r} p≤q $ ≈ᴿ⁺⇒≤ᴿ⁺ {q} {r} q≈r

  ≤ᴿ⁺-resp :  p ≈ᴿ⁺ q →  r ≈ᴿ⁺ s →  p ≤ᴿ⁺ r →  q ≤ᴿ⁺ s
  ≤ᴿ⁺-resp {p} {q} {r} {s} p≈q r≈s p≤r =
    ≤ᴿ⁺-respʳ {q} {r} {s} r≈s $ ≤ᴿ⁺-respˡ {p} {q} {r} p≈q $ p≤r

  -- <ᴿ⁺ is irreflexive

  <ᴿ⁺-irrefl :  ¬ p <ᴿ⁺ p
  <ᴿ⁺-irrefl =  <⁺-irrefl

  -- <ᴿ⁺ is asymmetric

  <ᴿ⁺-asym :  p <ᴿ⁺ q →  ¬ q <ᴿ⁺ p
  <ᴿ⁺-asym p<q q<p =  <⁺-asym p<q q<p

  -- <ᴿ⁺ into ≤ᴿ⁺

  <ᴿ⁺⇒≤ᴿ⁺ :  p <ᴿ⁺ q →  p ≤ᴿ⁺ q
  <ᴿ⁺⇒≤ᴿ⁺ =  <⁺⇒≤⁺

  -- Compose ≤ᴿ⁺ and <ᴿ⁺

  ≤ᴿ⁺-<ᴿ⁺-trans :  p ≤ᴿ⁺ q →  q <ᴿ⁺ r →  p <ᴿ⁺ r
  ≤ᴿ⁺-<ᴿ⁺-trans {a ⫽⁺ b} {c ⫽⁺ d} {e ⫽⁺ f} da≤bc fc<de =  *⁺-smonoʳ-inv {d} $
    -- d(fa) ≡ f(da) ≤ f(bc) ≡ b(fc) < b(de) ≡ d(be)
    ≤⁺-<⁺-trans
      (subst₂ _≤⁺_ (?*⁺-comm {f} {d}) (?*⁺-comm {f} {b}) $ *⁺-monoʳ {f} da≤bc) $
      subst (b *⁺ (f *⁺ c) <⁺_) (?*⁺-comm {b} {d}) $ *⁺-smonoʳ {b} fc<de

  <ᴿ⁺-≤ᴿ⁺-trans :  p <ᴿ⁺ q →  q ≤ᴿ⁺ r →  p <ᴿ⁺ r
  <ᴿ⁺-≤ᴿ⁺-trans {a ⫽⁺ b} {c ⫽⁺ d} {e ⫽⁺ f} da<bc fc≤de =  *⁺-smonoʳ-inv {d} $
    -- d(fa) ≡ f(da) < f(bc) ≡ b(fc) ≤ b(de) ≡ d(be)
    <⁺-≤⁺-trans
      (subst₂ _<⁺_ (?*⁺-comm {f} {d}) (?*⁺-comm {f} {b}) $ *⁺-smonoʳ {f} da<bc)
      $ subst (b *⁺ (f *⁺ c) ≤⁺_) (?*⁺-comm {b} {d}) $ *⁺-monoʳ {b} fc≤de

  -- <ᴿ⁺ is transitive

  <ᴿ⁺-trans :  p <ᴿ⁺ q →  q <ᴿ⁺ r →  p <ᴿ⁺ r
  <ᴿ⁺-trans {p} {q} {r} p<q q<r =
    <ᴿ⁺-≤ᴿ⁺-trans {p} {q} {r} p<q $ <ᴿ⁺⇒≤ᴿ⁺ {q} {r} q<r

  -- <ᴿ⁺ respects ≈ᴿ⁺

  <ᴿ⁺-respˡ :  p ≈ᴿ⁺ q →  p <ᴿ⁺ r →  q <ᴿ⁺ r
  <ᴿ⁺-respˡ {p} {q} {r} p≈q p<r =  ≤ᴿ⁺-<ᴿ⁺-trans {q} {p} {r}
    (≈ᴿ⁺⇒≤ᴿ⁺ {q} {p} $ ≈ᴿ⁺-sym {p} {q} p≈q) p<r

  <ᴿ⁺-respʳ :  ∀{p q r} →  q ≈ᴿ⁺ r →  p <ᴿ⁺ q →  p <ᴿ⁺ r
  <ᴿ⁺-respʳ {p} {q} {r} q≈r p<q =
    <ᴿ⁺-≤ᴿ⁺-trans {p} {q} {r} p<q $ ≈ᴿ⁺⇒≤ᴿ⁺ {q} {r} q≈r

  <ᴿ⁺-resp :  p ≈ᴿ⁺ q →  r ≈ᴿ⁺ s →  p <ᴿ⁺ r →  q <ᴿ⁺ s
  <ᴿ⁺-resp {p} {q} {r} {s} p≈q r≈s p<r =
    <ᴿ⁺-respʳ {q} {r} {s} r≈s $ <ᴿ⁺-respˡ {p} {q} {r} p≈q $ p<r

  -- ≤ᴿ⁺ and >ᴿ⁺ do not hold at the same time

  ≤ᴿ⁺⇒¬>ᴿ⁺ :  p ≤ᴿ⁺ q →  ¬ p >ᴿ⁺ q
  ≤ᴿ⁺⇒¬>ᴿ⁺ =  ≤⁺⇒¬>⁺

  <ᴿ⁺⇒¬≥ᴿ⁺ :  p <ᴿ⁺ q →  ¬ p ≥ᴿ⁺ q
  <ᴿ⁺⇒¬≥ᴿ⁺ =  <⁺⇒¬≥⁺

  infix 4 _<≈>ᴿ⁺_ _≤>ᴿ⁺_ _<≥ᴿ⁺_

  -- Get <ᴿ⁺, ≈ᴿ⁺ or >ᴿ⁺

  _<≈>ᴿ⁺_ :  ∀ p q →  p <ᴿ⁺ q  ⨿  p ≈ᴿ⁺ q  ⨿  p >ᴿ⁺ q
  a ⫽⁺ b <≈>ᴿ⁺ c ⫽⁺ d =  d *⁺ a <≡>⁺ b *⁺ c

  -- Get ≤ᴿ⁺ or >ᴿ⁺

  _≤>ᴿ⁺_ :  ∀ p q →  p ≤ᴿ⁺ q  ⨿  p >ᴿ⁺ q
  a ⫽⁺ b ≤>ᴿ⁺ c ⫽⁺ d =  d *⁺ a ≤>⁺ b *⁺ c

  -- Get <⁺ or ≥⁺

  _<≥ᴿ⁺_ :  ∀ p q →  p <ᴿ⁺ q  ⨿  p ≥ᴿ⁺ q
  a ⫽⁺ b <≥ᴿ⁺ c ⫽⁺ d =  d *⁺ a <≥⁺ b *⁺ c

--------------------------------------------------------------------------------
-- +ᴿ⁺ :  Addition of ℚ⁺, unnormalized

infixl 6 _+ᴿ⁺_
_+ᴿ⁺_ :  ℚ⁺ → ℚ⁺ → ℚ⁺
(a ⫽⁺ b) +ᴿ⁺ (c ⫽⁺ d) =  d *⁺ a +⁺ b *⁺ c ⫽⁺ b *⁺ d

abstract

  -- +ᴿ⁺ is commutative

  +ᴿ⁺-comm :  p +ᴿ⁺ q ≡ q +ᴿ⁺ p
  +ᴿ⁺-comm {a ⫽⁺ b} {c ⫽⁺ d} =  cong₂ _⫽⁺_ +⁺-comm (*⁺-comm {b} {d})

  -- +ᴿ⁺ is associative

  +ᴿ⁺-assocʳ :  (p +ᴿ⁺ q) +ᴿ⁺ r ≡ p +ᴿ⁺ (q +ᴿ⁺ r)
  +ᴿ⁺-assocʳ {a ⫽⁺ b} {c ⫽⁺ d} {e ⫽⁺ f} =
    cong₂ _⫽⁺_ eq (*⁺-assocʳ {b} {d} {f})
   where
    eq :  f *⁺ (d *⁺ a +⁺ b *⁺ c) +⁺ (b *⁺ d) *⁺ e ≡
          (d *⁺ f) *⁺ a +⁺ b *⁺ (f *⁺ c +⁺ d *⁺ e)
    eq =
      -- f(da+bc)+(bd)e ≡ f(da+bc)+b(de) ≡ (f(da)+f(bc))+b(de) ≡
      -- ((df)a+b(fc))+b(de) ≡ (df)a+(b(fc)+b(de)) ≡ (df)a+b(fc+de)
      flip (cong₂ _+⁺_) (*⁺-assocʳ {b} {d} {e})
        (*⁺-+⁺-distrʳ {f} {d *⁺ a} {b *⁺ c} ◇ cong₂ _+⁺_
          (?*⁺-comm {f} {d} {a} ◇ *⁺-assocˡ {d} {f} {a})
          (?*⁺-comm {f} {b} {c})) ◇
      +⁺-assocʳ ◇ cong (d *⁺ f *⁺ a +⁺_) $ ◠ *⁺-+⁺-distrʳ {b}

  +ᴿ⁺-assocˡ :  p +ᴿ⁺ (q +ᴿ⁺ r) ≡ (p +ᴿ⁺ q) +ᴿ⁺ r
  +ᴿ⁺-assocˡ {p} {q} {r} =  ◠ +ᴿ⁺-assocʳ {p} {q} {r}

  -- +ᴿ⁺ preserves ≈ᴿ⁺

  +ᴿ⁺-congˡ :  p ≈ᴿ⁺ q →  p +ᴿ⁺ r ≈ᴿ⁺ q +ᴿ⁺ r
  +ᴿ⁺-congˡ {a ⫽⁺ b} {c ⫽⁺ d} {e ⫽⁺ f} da≡bc =
    -- (df)(fa+be) ≡ (d(fa+be))f ≡ (b(fc+de))f ≡ (bf)(fc+de)
    *⁺?-comm {d} {f} ◇ cong (_*⁺ f) eq ◇ *⁺?-comm {b} {_} {f}
   where
    eq :  d *⁺ (f *⁺ a +⁺ b *⁺ e) ≡ b *⁺ (f *⁺ c +⁺ d *⁺ e)
    eq =
      -- d(fa+be) ≡ d(fa)+d(be) ≡ d(fa)+b(de) ≡ f(da)+b(de) ≡ f(bc)+b(de) ≡
      -- b(fc)+b(de) ≡ b(fc+de)
      *⁺-+⁺-distrʳ {d} ◇
      flip (cong₂ _+⁺_) (?*⁺-comm {d} {b})
        (?*⁺-comm {d} {f} ◇ cong (f *⁺_) da≡bc ◇ ?*⁺-comm {f} {b}) ◇
      ◠ *⁺-+⁺-distrʳ {b}

  +ᴿ⁺-congʳ :  ∀{p q r} →  q ≈ᴿ⁺ r →  p +ᴿ⁺ q ≈ᴿ⁺ p +ᴿ⁺ r
  +ᴿ⁺-congʳ {p} {q} {r} q≈r =  subst₂ _≈ᴿ⁺_
    (+ᴿ⁺-comm {q} {p}) (+ᴿ⁺-comm {r} {p}) (+ᴿ⁺-congˡ {q} {r} {p} q≈r)

  +ᴿ⁺-cong :  p ≈ᴿ⁺ q →  r ≈ᴿ⁺ s →  p +ᴿ⁺ r ≈ᴿ⁺ q +ᴿ⁺ s
  +ᴿ⁺-cong {p} {q} {r} {s} p≈q r≈s =  ≈ᴿ⁺-trans {p +ᴿ⁺ r} {q +ᴿ⁺ r} {q +ᴿ⁺ s}
    (+ᴿ⁺-congˡ {p} {q} {r} p≈q) (+ᴿ⁺-congʳ {q} {r} {s} r≈s)

  -- +ᴿ⁺ is strictly increasing

  +ᴿ⁺-sincrʳ :  p <ᴿ⁺ p +ᴿ⁺ q
  +ᴿ⁺-sincrʳ {a ⫽⁺ b} {c ⫽⁺ d} =
    -- (bd)a ≡ b(da) < b(da)+b(bc) ≡ b(da+bc)
    subst₂ _<⁺_ (*⁺-assocˡ {b} {d}) (◠ *⁺-+⁺-distrʳ {b}) +⁺-sincrʳ

  +ᴿ⁺-sincrˡ :  ∀{p q} →  q <ᴿ⁺ p +ᴿ⁺ q
  +ᴿ⁺-sincrˡ {p} {q} =  subst (q <ᴿ⁺_) (+ᴿ⁺-comm {q} {p}) $ +ᴿ⁺-sincrʳ {q} {p}

  +ᴿ⁺-incrˡ :  ∀{p q} →  q ≤ᴿ⁺ p +ᴿ⁺ q
  +ᴿ⁺-incrˡ {p} {q} =  <ᴿ⁺⇒≤ᴿ⁺ {q} {p +ᴿ⁺ q} $ +ᴿ⁺-sincrˡ {p} {q}

  +ᴿ⁺-incrʳ :  p ≤ᴿ⁺ p +ᴿ⁺ q
  +ᴿ⁺-incrʳ {p} {q} =  <ᴿ⁺⇒≤ᴿ⁺ {p} {p +ᴿ⁺ q} $ +ᴿ⁺-sincrʳ {p} {q}

  -- Monotonicity of +ᴿ⁺

  +ᴿ⁺-monoˡ :  p ≤ᴿ⁺ q →  p +ᴿ⁺ r ≤ᴿ⁺ q +ᴿ⁺ r
  +ᴿ⁺-monoˡ {a ⫽⁺ b} {c ⫽⁺ d} {e ⫽⁺ f} da≤bc =  -- (df)(fa+be) ≤ (bf)(fc+de)
    subst₂ _≤⁺_ (*⁺?-comm {d} {_} {f}) (*⁺?-comm {b} {_} {f}) $
    -- (d(fa+be))f ≤ (b(fc+de))f
    *⁺-monoˡ {n = f} le
   where
    le :  d *⁺ (f *⁺ a +⁺ b *⁺ e) ≤⁺ b *⁺ (f *⁺ c +⁺ d *⁺ e)
    le =
      -- d(fa+be) ≡ d(fa)+d(be) ≡ f(da)+b(de) ≤ f(bc)+b(de) ≡ b(fc)+b(de) ≡
      -- b(fc+de)
      subst₂ _≤⁺_
        (cong₂ _+⁺_ (?*⁺-comm {f} {d}) (?*⁺-comm {b} {d}) ◇ ◠ *⁺-+⁺-distrʳ {d})
        (cong (_+⁺ b *⁺ (d *⁺ e)) (?*⁺-comm {f} {b}) ◇ ◠ *⁺-+⁺-distrʳ {b}) $
      +⁺-monoˡ (*⁺-monoʳ {f} da≤bc)

  +ᴿ⁺-monoʳ :  ∀{p q r} →  q ≤ᴿ⁺ r →  p +ᴿ⁺ q ≤ᴿ⁺ p +ᴿ⁺ r
  +ᴿ⁺-monoʳ {p} {q} {r} q≤r =  subst₂ _≤ᴿ⁺_
    (+ᴿ⁺-comm {q} {p}) (+ᴿ⁺-comm {r} {p}) (+ᴿ⁺-monoˡ {q} {r} {p} q≤r)

  +ᴿ⁺-mono :  p ≤ᴿ⁺ q →  r ≤ᴿ⁺ s →  p +ᴿ⁺ r ≤ᴿ⁺ q +ᴿ⁺ s
  +ᴿ⁺-mono {p} {q} {r} {s} p≤q r≤s =  ≤ᴿ⁺-trans {p +ᴿ⁺ r} {q +ᴿ⁺ r} {q +ᴿ⁺ s}
    (+ᴿ⁺-monoˡ {p} {q} {r} p≤q) (+ᴿ⁺-monoʳ {q} {r} {s} r≤s)

--------------------------------------------------------------------------------
-- ≤1ᴿ⁺ :  No more than 1ᴿ⁺

infix 4 _≤1ᴿ⁺
_≤1ᴿ⁺ :  ℚ⁺ → Set₀
p ≤1ᴿ⁺ =  p ≤ᴿ⁺ 1ᴿ⁺

abstract

  -- 1ᴿ⁺ satisfies ≤1ᴿ⁺
  1≤1ᴿ⁺ :  1ᴿ⁺ ≤1ᴿ⁺
  1≤1ᴿ⁺ =  ≤ᴿ⁺-refl {1ᴿ⁺}

  -- ≤1ᴿ⁺ respects ≈ᴿ⁺

  ≤1ᴿ⁺-resp :  p ≈ᴿ⁺ q →  p ≤1ᴿ⁺ →  q ≤1ᴿ⁺
  ≤1ᴿ⁺-resp {p} {q} p≈q =  ≤ᴿ⁺-respˡ {p} {q} {1ᴿ⁺} p≈q

  -- ≤1ᴿ⁺ is preserved by removal w.r.t. +ᴿ⁺

  ≤1ᴿ⁺-rem :  p +ᴿ⁺ q ≤1ᴿ⁺ →  q ≤1ᴿ⁺
  ≤1ᴿ⁺-rem {p} {q} p+q≤1 =
    ≤ᴿ⁺-trans {q} {p +ᴿ⁺ q} {1ᴿ⁺} (+ᴿ⁺-incrˡ {p} {q}) p+q≤1

  -- 1ᴿ⁺ +ᴿ⁺ p does not satisfy ≤1ᴿ⁺

  ¬1+?≤1ᴿ⁺ :  ¬ 1ᴿ⁺ +ᴿ⁺ p ≤1ᴿ⁺
  ¬1+?≤1ᴿ⁺ {p} =  <ᴿ⁺⇒¬≥ᴿ⁺ {1ᴿ⁺} {1ᴿ⁺ +ᴿ⁺ p} $ +ᴿ⁺-sincrʳ {1ᴿ⁺} {p}

--------------------------------------------------------------------------------
-- /⁺ :  Divide ℚ⁺ with ℕ⁺

infixl 7 _/⁺_ _/2⁺
_/⁺_ :  ℚ⁺ → ℕ⁺ → ℚ⁺
(a ⫽⁺ b) /⁺ c =  a ⫽⁺ c *⁺ b

_/2⁺ :  ℚ⁺ → ℚ⁺
p /2⁺ =  p /⁺ 2⁺

abstract

  -- Cancel addition of two halved fractions

  /2⁺-merge :  p /2⁺  +ᴿ⁺  p /2⁺  ≈ᴿ⁺  p
  /2⁺-merge {p@(a ⫽⁺ b)} =  subst (_≈ᴿ⁺ p) (cong (_⫽⁺ 2b *⁺ 2b) eq) eqv
   where
    2a 2b :  ℕ⁺
    2a =  2⁺ *⁺ a
    2b =  2⁺ *⁺ b
    eq :  2b *⁺ 2a  ≡  2b *⁺ a +⁺ 2b *⁺ a
    eq =  cong (2b *⁺_) *⁺-2ˡ ◇ *⁺-+⁺-distrʳ {2b} {a} {a}
    eqv :  2b *⁺ 2a ⫽⁺ 2b *⁺ 2b  ≈ᴿ⁺  p
    eqv =  ≈ᴿ⁺-trans {2b *⁺ 2a ⫽⁺ 2b *⁺ 2b} {2a ⫽⁺ 2b} {p}
      (⫽⁺-*ˡ {2b} {2a} {2b}) (⫽⁺-*ˡ {2⁺} {a} {b})

  /2⁺-split :  p  ≈ᴿ⁺  p /2⁺  +ᴿ⁺  p /2⁺
  /2⁺-split {p} =  ≈ᴿ⁺-sym {p /2⁺ +ᴿ⁺ p /2⁺} {p} $ /2⁺-merge {p}
