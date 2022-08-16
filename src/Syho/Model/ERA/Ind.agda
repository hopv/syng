--------------------------------------------------------------------------------
-- Exclusive & persistent indirection ERAs
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Ind where

open import Base.Size using (∞)
open import Base.Eq using (_≡_; refl; ◠_; _◇_)
open import Base.Func using (_∘_)
open import Base.Prod using (_,_; _×_)
open import Base.Few using (absurd)
open import Base.Nat using (ℕ; _≡ᵇ_; ᵇ⇒≡; _≤_; <⇒≤; ≤-refl; <-irrefl)
open import Base.Nmap using (updⁿᵐ)
open import Base.Bool using (ff; tt)
open import Syho.Logic.Prop using (Prop'; ⊤')
open import Syho.Model.ERA using (ERA)
open import Syho.Model.Exc using (Exc; ?ˣ; #ˣ_; _∙ˣ_; _←ˣ_; ∙ˣ-comm; ∙ˣ-assocˡ;
  ∙ˣ-?ˣ)

open import Base.Finmap (Prop' ∞) (_≡ ⊤') using (Finmap; _|ᶠᵐ_; boundᶠᵐ; addᶠᵐ)

open ERA using (Env; Res; _≈ᴱ_; _≈_; _✓_; _∙_; ε; ⌞_⌟; refl˜ᴱ; ◠˜ᴱ_; _◇˜ᴱ_;
  refl˜; ◠˜_; _◇˜_; ∙-congˡ; ∙-unitˡ; ∙-comm; ∙-assocˡ; ✓-resp; ✓-rem; ✓-ε;
  ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem)

private variable
  Pᶠᵐ :  Finmap
  Q :  Prop' ∞
  i :  ℕ

--------------------------------------------------------------------------------
-- Indˣᴱᴿᴬ :  Exclusive indirection ERA

Indˣᴱᴿᴬ :  ERA

Indˣᴱᴿᴬ .Env =  Finmap

Indˣᴱᴿᴬ .Res =  ℕ →  Exc (Prop' ∞)

-- We need the bound equality m ≡ n because ✓ uses the bound information

Indˣᴱᴿᴬ ._≈ᴱ_ (P˙ |ᶠᵐ (m , _)) (Q˙ |ᶠᵐ (n , _)) =  m ≡ n × (∀ i → P˙ i ≡ Q˙ i)

Indˣᴱᴿᴬ ._≈_ Pˣ˙ Qˣ˙ =  ∀ i →  Pˣ˙ i ≡ Qˣ˙ i

-- Qˣ˙ i agrees with P˙ i and equals ?ˣ if i is in the null range

Indˣᴱᴿᴬ ._✓_ (P˙ |ᶠᵐ (n , _)) Qˣ˙ =
  ∀ i →  P˙ i ←ˣ Qˣ˙ i  ×  (n ≤ i → Qˣ˙ i ≡ ?ˣ)

Indˣᴱᴿᴬ ._∙_ Pˣ˙ Qˣ˙ i =  Pˣ˙ i ∙ˣ Qˣ˙ i

Indˣᴱᴿᴬ .ε i =  ?ˣ

Indˣᴱᴿᴬ .⌞_⌟ _ i =  ?ˣ

Indˣᴱᴿᴬ .refl˜ᴱ =  refl , λ _ → refl

Indˣᴱᴿᴬ .◠˜ᴱ_ (refl , ∀iPi≡Qi) =  refl , λ i → ◠ ∀iPi≡Qi i

Indˣᴱᴿᴬ ._◇˜ᴱ_ (refl , ∀iPi≡Qi) (refl , ∀iQi≡Ri) =
  refl , λ i → ∀iPi≡Qi i ◇ ∀iQi≡Ri i

Indˣᴱᴿᴬ .refl˜ _ =  refl

Indˣᴱᴿᴬ .◠˜_ ∀iPi≡Qi i =  ◠ ∀iPi≡Qi i

Indˣᴱᴿᴬ ._◇˜_ ∀iPi≡Qi ∀iQi≡Ri i =  ∀iPi≡Qi i ◇ ∀iQi≡Ri i

Indˣᴱᴿᴬ .∙-congˡ ∀iPi≡Qi i  rewrite ∀iPi≡Qi i =  refl

Indˣᴱᴿᴬ .∙-unitˡ _ =  refl

Indˣᴱᴿᴬ .∙-comm {a = Pˣ˙} i =  ∙ˣ-comm {x = Pˣ˙ i}

Indˣᴱᴿᴬ .∙-assocˡ {a = Pˣ˙} i =  ∙ˣ-assocˡ {x = Pˣ˙ i}

Indˣᴱᴿᴬ .✓-resp (refl , ∀iPi≡Qi) ∀iRi≡Si P✓R i  with P✓R i
... | P✓Ri  rewrite ∀iPi≡Qi i | ∀iRi≡Si i =  P✓Ri

Indˣᴱᴿᴬ .✓-rem {a = Pˣ˙} {b = Qˣ˙} R✓P∙Q i  with Pˣ˙ i | Qˣ˙ i | R✓P∙Q i
... | ?ˣ | _ | R✓Qi =  R✓Qi
... | _ | ?ˣ | _ =  _ , λ _ → refl

Indˣᴱᴿᴬ .✓-ε _ =  _ , λ _ → refl

Indˣᴱᴿᴬ .⌞⌟-cong _ _ =  refl

Indˣᴱᴿᴬ .⌞⌟-add =  (λ _ → ?ˣ) , λ _ → refl

Indˣᴱᴿᴬ .⌞⌟-unitˡ _ =  refl

Indˣᴱᴿᴬ .⌞⌟-idem _ =  refl

open ERA Indˣᴱᴿᴬ using () renaming (Res to Resˣ; ε to εˣ; _↝_ to _↝ˣ_)

-- Exclusively own a proposition at an index

line-indˣ :  ℕ →  Prop' ∞ →  Resˣ
line-indˣ i P =  updⁿᵐ i (#ˣ P) εˣ

abstract

  -- Add a new proposition and get a line

  add-indˣ :  (Pᶠᵐ , εˣ) ↝ˣ (addᶠᵐ Q Pᶠᵐ , line-indˣ (boundᶠᵐ Pᶠᵐ) Q)
  add-indˣ {Pᶠᵐ = _ |ᶠᵐ (n , fi)} R˙ˣ P✓R∙ε j  with P✓R∙ε j
  ... | (Pj←Rj∙? , n≤j⇒Rj≡?ˣ)  with n ≡ᵇ j | ᵇ⇒≡ {n} {j}
  ...   | ff | _ =  Pj←Rj∙? , n≤j⇒Rj≡?ˣ ∘ <⇒≤
  ...   | tt | ⇒n≡j  with ⇒n≡j _
  ...     | refl  rewrite ∙ˣ-?ˣ {x = R˙ˣ n} | n≤j⇒Rj≡?ˣ ≤-refl
    =  refl , absurd ∘ <-irrefl
