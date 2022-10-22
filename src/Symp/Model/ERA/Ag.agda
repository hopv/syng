--------------------------------------------------------------------------------
-- Agreement ERA
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Symp.Model.ERA.Ag where

open import Base.Level using (Level)
open import Base.Func using (_$_; _▷_; id)
open import Base.Eq using (_≡_; refl)
open import Base.Option using (¿_; š_; ň)
open import Base.Prod using (_,_; -,_)
open import Base.List using (List; []; _∷_; [_]; _⧺_; ∈ʰᵈ; _∈ᴸ_; _⊆ᴸ_; _≈ᴸ_;
  ⧺-congˡ; ⧺-comm; ⧺-assocʳ; ⧺-idem; ⧺-⊆ᴸ-introʳ; ≈ᴸ-refl; ≡⇒≈ᴸ; ≈ᴸ-sym;
  ≈ᴸ-trans)
open import Symp.Model.ERA.Base using (ERA)

open ERA using (Res; _≈_; _∙_; ε; ⌞_⌟; Env; _✓_; refl˜; ◠˜_; _◇˜_; ∙-congˡ;
  ∙-unitˡ; ∙-comm; ∙-assocʳ; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem; ✓-resp; ✓-rem)

private variable
  ł :  Level
  A :  Set ł
  a b :  A
  aˇ :  ¿ A
  as bs cs :  List A

--------------------------------------------------------------------------------
-- ✓ᴸ :  Agreement between ¿ A and List A

infix 4 _✓ᴸ_
_✓ᴸ_ :  ∀{A : Set ł} →  ¿ A →  List A →  Set ł
aˇ ✓ᴸ bs =  ∀ b →  b ∈ᴸ bs →  aˇ ≡ š b

abstract

  -- ✓ᴸ respects ⊆ᴸ and ≈ᴸ

  ✓ᴸ-⊆ᴸ :  cs ⊆ᴸ bs →  aˇ ✓ᴸ bs →  aˇ ✓ᴸ cs
  ✓ᴸ-⊆ᴸ cs⊆bs aˇ✓bs _ c∈cs =  aˇ✓bs _ $ cs⊆bs c∈cs

  ✓ᴸ-resp :  bs ≈ᴸ cs →  aˇ ✓ᴸ bs →  aˇ ✓ᴸ cs
  ✓ᴸ-resp (-, cs⊆bs) =  ✓ᴸ-⊆ᴸ cs⊆bs

  -- ň ✓ᴸ as entails as ≡ []

  ň-✓ᴸ :  ň ✓ᴸ as →  as ≡ []
  ň-✓ᴸ {as = []} _ =  refl
  ň-✓ᴸ {as = a ∷ as} ň✓as =  ň✓as _ ∈ʰᵈ ▷ λ ()

  -- aˇ ✓ᴸ [] holds

  ✓ᴸ-[] :  aˇ ✓ᴸ []
  ✓ᴸ-[] _ ()

  -- ✓ˣ is preserved by removal w.r.t. ⧺

  ✓ᴸ-rem :  aˇ ✓ᴸ bs ⧺ cs →  aˇ ✓ᴸ cs
  ✓ᴸ-rem ∈bs⧺cs⇒≡a _ c∈cs =  ∈bs⧺cs⇒≡a _ $ ⧺-⊆ᴸ-introʳ c∈cs

  -- š a ✓ᴸ [ a ] holds

  ✓ᴸ-š-[?] :  š a ✓ᴸ [ a ]
  ✓ᴸ-š-[?] _ ∈ʰᵈ =  refl

  -- Update ň into š a and [] into [ a ], preserving ✓ᴸ - ⧺ bs

  ✓ᴸ-new :  ň ✓ᴸ bs →  š a ✓ᴸ a ∷ bs
  ✓ᴸ-new {bs = []} _ _ ∈ʰᵈ =  refl
  ✓ᴸ-new {bs = _ ∷ _} ň✓ᴸ∷ =  ň✓ᴸ∷ _ ∈ʰᵈ ▷ λ ()

  -- Agreement from ✓ᴸ - ∷ -

  ✓ᴸ-agree : aˇ ✓ᴸ b ∷ cs →  aˇ ≡ š b
  ✓ᴸ-agree ∈b∷⇒≡a  rewrite ∈b∷⇒≡a _ ∈ʰᵈ =  refl

--------------------------------------------------------------------------------
-- Agᴱᴿᴬ :  Agreement ERA

Agᴱᴿᴬ :  Set ł →  ERA ł ł ł ł
Agᴱᴿᴬ A .Res =  List A
Agᴱᴿᴬ _ ._≈_ =  _≈ᴸ_
Agᴱᴿᴬ _ ._∙_ =  _⧺_
Agᴱᴿᴬ _ .ε =  []
Agᴱᴿᴬ _ .⌞_⌟ as =  as
Agᴱᴿᴬ A .Env =  ¿ A
Agᴱᴿᴬ _ ._✓_ =  _✓ᴸ_
Agᴱᴿᴬ _ .refl˜ =  ≈ᴸ-refl
Agᴱᴿᴬ _ .◠˜_ =  ≈ᴸ-sym
Agᴱᴿᴬ _ ._◇˜_ =  ≈ᴸ-trans
Agᴱᴿᴬ _ .∙-congˡ =  ⧺-congˡ
Agᴱᴿᴬ _ .∙-unitˡ =  ≈ᴸ-refl
Agᴱᴿᴬ _ .∙-comm {a = as} =  ⧺-comm {as = as}
Agᴱᴿᴬ _ .∙-assocʳ {a = as} =  ≡⇒≈ᴸ $ ⧺-assocʳ {as = as}
Agᴱᴿᴬ _ .⌞⌟-cong =  id
Agᴱᴿᴬ _ .⌞⌟-add =  -, ≈ᴸ-refl
Agᴱᴿᴬ _ .⌞⌟-unitˡ =  ⧺-idem
Agᴱᴿᴬ _ .⌞⌟-idem =  ≈ᴸ-refl
Agᴱᴿᴬ _ .✓-resp =  ✓ᴸ-resp
Agᴱᴿᴬ _ .✓-rem =  ✓ᴸ-rem
