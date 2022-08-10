--------------------------------------------------------------------------------
-- ℕ and lists
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.Nat.List where

open import Base.Nat using (ℕ; suc; _≤_; _⊔_; ≤-trans; ≤⇒¬>; suc-sincr;
  ⊔-introˡ; ⊔-introʳ)
open import Base.List using (List; _∷_; [])
open import Base.Eq using (refl)
open import Base.Setoid using (≡-setoid)
open import Base.List.Any using (by-hd; by-tl)
open import Base.List.Set (≡-setoid ℕ) using (_∈ᴸ_; _∉ᴸ_)

private variable
  m :  ℕ
  ns :  List ℕ

--------------------------------------------------------------------------------
-- [⊔] :  Maximum of a list

[⊔] :  List ℕ → ℕ
[⊔] (n ∷ ns) =  n ⊔ [⊔] ns
[⊔] [] =  0

abstract

  ∈ᴸ⇒≤[⊔] :  m ∈ᴸ ns →  m ≤ [⊔] ns
  ∈ᴸ⇒≤[⊔] (by-hd refl) =  ⊔-introˡ
  ∈ᴸ⇒≤[⊔] {ns = n ∷ _} (by-tl m∈ᴸns') =
    ≤-trans (∈ᴸ⇒≤[⊔] m∈ᴸns') (⊔-introʳ {_} {n})

  suc[⊔]∉ᴸ :  suc ([⊔] ns) ∉ᴸ ns
  suc[⊔]∉ᴸ suc[⊔]∈ =  ≤⇒¬> (∈ᴸ⇒≤[⊔] suc[⊔]∈) suc-sincr
