--------------------------------------------------------------------------------
-- Agreement ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Syho.Model.ERA.Ag where

open import Base.Level using (Level)
open import Base.Func using (_$_; id)
open import Base.Eq using (_≡_; refl)
open import Base.Prod using (_,_; -,_)
open import Base.Option using (¿_; š_; ň)
open import Base.List using (List; []; [_]; _⧺_; _∈ᴸ_; _⊆ᴸ_; _≈ᴸ_; ∈ʰᵈ; ⊆ᴸ-[];
  ⧺-⊆ᴸ-introʳ; ≈ᴸ-refl; ≡⇒≈ᴸ; ≈ᴸ-sym; ≈ᴸ-trans; ⧺-congˡ; ⧺-comm; ⧺-assocˡ;
  ⧺-idem)
open import Syho.Model.ERA.Base using (ERA)

open ERA using (Env; Res; _≈_; _✓_; _∙_; ε; ⌞_⌟; refl˜; ◠˜_; _◇˜_; ⊑-refl;
  ∙-congˡ; ∙-unitˡ; ∙-comm; ∙-assocˡ; ✓-resp; ✓-rem; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ;
  ⌞⌟-idem; ⌞⌟-ε)

private variable
  ł :  Level
  A :  Set ł
  a c :  A
  aˇ :  ¿ A
  bs cs :  List A

--------------------------------------------------------------------------------
-- ✓ᴸ :  Agreement between ¿ A and List A

infix 4 _✓ᴸ_
_✓ᴸ_ :  ∀{A : Set ł} →  ¿ A →  List A →  Set ł
ň ✓ᴸ bs =  bs ≡ []
š a ✓ᴸ bs =  ∀ b →  b ∈ᴸ bs →  b ≡ a

abstract

  -- ✓ᴸ respects ⊆ᴸ and ≈ᴸ

  ✓ᴸ-⊆ᴸ :  cs ⊆ᴸ bs →  aˇ ✓ᴸ bs →  aˇ ✓ᴸ cs
  ✓ᴸ-⊆ᴸ {aˇ = ň} cs⊆[] refl =  ⊆ᴸ-[] cs⊆[]
  ✓ᴸ-⊆ᴸ {aˇ = š _} cs⊆bs aˇ✓bs _ c∈cs =  aˇ✓bs _ $ cs⊆bs c∈cs

  ✓ᴸ-resp :  bs ≈ᴸ cs →  aˇ ✓ᴸ bs →  aˇ ✓ᴸ cs
  ✓ᴸ-resp (-, cs⊆bs) =  ✓ᴸ-⊆ᴸ cs⊆bs

  -- ✓ˣ holds after removing a list with respect to ⧺

  ✓ᴸ-rem :  aˇ ✓ᴸ bs ⧺ cs →  aˇ ✓ᴸ cs
  ✓ᴸ-rem {aˇ = ň} {[]} {[]} _ =  refl
  ✓ᴸ-rem {aˇ = š _} ∈bs⧺cs⇒≡a _ c∈cs =  ∈bs⧺cs⇒≡a _ $ ⧺-⊆ᴸ-introʳ c∈cs

  -- š a ✓ᴸ [ a ] holds

  ✓ᴸ-š-[?] :  š a ✓ᴸ [ a ]
  ✓ᴸ-š-[?] _ ∈ʰᵈ =  refl

  -- Update ň into š a and cs into [ a ], preserving ✓ᴸ bs ⧺

  ✓ᴸ-alloc :  ň ✓ᴸ bs ⧺ cs →  š a ✓ᴸ bs ⧺ [ a ]
  ✓ᴸ-alloc {bs = []} {cs = []} _ _ ∈ʰᵈ =  refl

  -- Agreement from ✓ᴸ bs ⧺ [ c ]

  ✓ᴸ-agree : aˇ ✓ᴸ bs ⧺ [ c ] →  aˇ ≡ š c
  ✓ᴸ-agree {aˇ = ň} {[]} ()
  ✓ᴸ-agree {aˇ = š _} ∈bs⧺[c]⇒≡a
    rewrite ∈bs⧺[c]⇒≡a _ $ ⧺-⊆ᴸ-introʳ ∈ʰᵈ =  refl

--------------------------------------------------------------------------------
-- Agᴱᴿᴬ :  Agreement ERA

Agᴱᴿᴬ :  Set ł →  ERA ł ł ł ł
Agᴱᴿᴬ A .Env =  ¿ A
Agᴱᴿᴬ A .Res =  List A
Agᴱᴿᴬ _ ._≈_ =  _≈ᴸ_
Agᴱᴿᴬ _ ._✓_ =  _✓ᴸ_
Agᴱᴿᴬ _ ._∙_ =  _⧺_
Agᴱᴿᴬ _ .ε =  []
Agᴱᴿᴬ _ .⌞_⌟ as =  as
Agᴱᴿᴬ _ .refl˜ =  ≈ᴸ-refl
Agᴱᴿᴬ _ .◠˜_ =  ≈ᴸ-sym
Agᴱᴿᴬ _ ._◇˜_ =  ≈ᴸ-trans
Agᴱᴿᴬ _ .∙-congˡ =  ⧺-congˡ
Agᴱᴿᴬ _ .∙-unitˡ =  ≈ᴸ-refl
Agᴱᴿᴬ _ .∙-comm {a = as} =  ⧺-comm {as = as}
Agᴱᴿᴬ _ .∙-assocˡ {a = as} =  ≡⇒≈ᴸ $ ⧺-assocˡ {as = as}
Agᴱᴿᴬ _ .✓-resp =  ✓ᴸ-resp
Agᴱᴿᴬ _ .✓-rem =  ✓ᴸ-rem
Agᴱᴿᴬ _ .⌞⌟-cong =  id
Agᴱᴿᴬ _ .⌞⌟-add =  -, ≈ᴸ-refl
Agᴱᴿᴬ _ .⌞⌟-unitˡ =  ⧺-idem
Agᴱᴿᴬ _ .⌞⌟-idem =  ≈ᴸ-refl
