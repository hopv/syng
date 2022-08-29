--------------------------------------------------------------------------------
-- Exclusive & persistent indirection ERAs
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Ind where

open import Base.Level using (2ᴸ)
open import Base.Size using (∞)
open import Base.Func using (_∘_; _$_; id; _▷_)
open import Base.Few using (⊤₀; absurd)
open import Base.Eq using (_≡_; refl; ◠_; _◇_; subst)
open import Base.Prod using (_×_; proj₀; proj₁; _,_; -,_)
open import Base.Sum using (inj₀; inj₁)
open import Base.Bool using (ff; tt)
open import Base.Nat using (ℕ; _≥_; _<_; <⇒≤; ≤-refl; <-irrefl; _<≥_; _≡ᵇ_; ᵇ⇒≡;
  ≡ᵇ-refl; suc⊔-same; suc⊔-<)
open import Base.Nmap using (updⁿᵐ)
open import Base.List using (List; []; [_]; _++_; ++-assocˡ; ++-[]; ++-≡[])
open import Base.List.Set using (by-hd; _∈ᴸ_; _⊆ᴸ_; _≈ᴸ_; ≈ᴸ-refl; ≡⇒≈ᴸ; ≈ᴸ-sym;
  ≈ᴸ-trans; ++-congˡ; ++-idem; ++-comm; ⊆ᴸ-[]; ++-⊆ᴸ-introʳ)
open import Syho.Logic.Prop using (Prop'; ⊤')
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.Lib.Exc using (Exc; ?ˣ; #ˣ_; _∙ˣ_; _←ˣ_; ∙ˣ-comm;
  ∙ˣ-assocˡ; ∙ˣ-?ˣ)

open import Base.Finmap (Prop' ∞) (_≡ ⊤') using (Finmap; _|ᶠᵐ_; bndᶠᵐ; updᶠᵐ)

open ERA using (Env; Res; _≈ᴱ_; _≈_; _✓_; _∙_; ε; ⌞_⌟; refl˜ᴱ; ◠˜ᴱ_; _◇˜ᴱ_;
  refl˜; ◠˜_; _◇˜_; ∙-congˡ; ∙-unitˡ; ∙-comm; ∙-assocˡ; ✓-resp; ✓-rem; ✓-ε;
  ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem)

private variable
  P :  Prop' ∞
  Qᶠᵐ :  Finmap
  i :  ℕ

--------------------------------------------------------------------------------
-- Indˣᴱᴿᴬ :  Exclusive indirection ERA

Indˣᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ 2ᴸ

Indˣᴱᴿᴬ .Env =  Finmap

Indˣᴱᴿᴬ .Res =  ℕ →  Exc (Prop' ∞)

-- We need the bound equality m ≡ n because ✓ uses the bound information

Indˣᴱᴿᴬ ._≈ᴱ_ (P˙ |ᶠᵐ (m , _)) (Q˙ |ᶠᵐ (n , _)) =
  m ≡ n  ×  (∀ i →  P˙ i ≡ Q˙ i)

Indˣᴱᴿᴬ ._≈_ Pˣ˙ Qˣ˙ =  ∀ i →  Pˣ˙ i ≡ Qˣ˙ i

-- Qˣ˙ i agrees with P˙ i and equals ?ˣ if i is in the null range

Indˣᴱᴿᴬ ._✓_ (P˙ |ᶠᵐ (n , _)) Qˣ˙ =
  ∀ i →  P˙ i ←ˣ Qˣ˙ i  ×  (i ≥ n →  Qˣ˙ i ≡ ?ˣ)

Indˣᴱᴿᴬ ._∙_ Pˣ˙ Qˣ˙ i =  Pˣ˙ i ∙ˣ Qˣ˙ i

Indˣᴱᴿᴬ .ε i =  ?ˣ

Indˣᴱᴿᴬ .⌞_⌟ _ i =  ?ˣ

Indˣᴱᴿᴬ .refl˜ᴱ =  refl , λ _ → refl

Indˣᴱᴿᴬ .◠˜ᴱ_ (refl , ∀iPi≡Qi) =  refl , λ i → ◠ ∀iPi≡Qi i

Indˣᴱᴿᴬ ._◇˜ᴱ_ (refl , ∀iPi≡Qi) (refl , ∀iQi≡Ri) =
  refl , λ i → ∀iPi≡Qi i ◇ ∀iQi≡Ri i

Indˣᴱᴿᴬ .refl˜ _ =  refl

Indˣᴱᴿᴬ .◠˜_ ∀iPˣi≡Qˣi i =  ◠ ∀iPˣi≡Qˣi i

Indˣᴱᴿᴬ ._◇˜_ ∀iPˣi≡Qˣi ∀iQˣi≡Rˣi i =  ∀iPˣi≡Qˣi i ◇ ∀iQˣi≡Rˣi i

Indˣᴱᴿᴬ .∙-congˡ ∀iPˣi≡Qˣi i  rewrite ∀iPˣi≡Qˣi i =  refl

Indˣᴱᴿᴬ .∙-unitˡ _ =  refl

Indˣᴱᴿᴬ .∙-comm {a = Pˣ˙} i =  ∙ˣ-comm {x = Pˣ˙ i}

Indˣᴱᴿᴬ .∙-assocˡ {a = Pˣ˙} i =  ∙ˣ-assocˡ {x = Pˣ˙ i}

Indˣᴱᴿᴬ .✓-resp (refl , ∀iPi≡Qi) ∀iRˣi≡Sˣi P✓Rˣ i  with P✓Rˣ i
... | P✓Rˣi  rewrite ∀iPi≡Qi i | ∀iRˣi≡Sˣi i =  P✓Rˣi

Indˣᴱᴿᴬ .✓-rem {a = Pˣ˙} {b = Qˣ˙} R✓Pˣ∙Qˣ i  with Pˣ˙ i | Qˣ˙ i | R✓Pˣ∙Qˣ i
... | ?ˣ | _ | R✓Qˣi =  R✓Qˣi
... | _ | ?ˣ | _ =  -, λ _ → refl

Indˣᴱᴿᴬ .✓-ε _ =  -, λ _ → refl

Indˣᴱᴿᴬ .⌞⌟-cong _ _ =  refl

Indˣᴱᴿᴬ .⌞⌟-add =  (λ _ → ?ˣ) , λ _ → refl

Indˣᴱᴿᴬ .⌞⌟-unitˡ _ =  refl

Indˣᴱᴿᴬ .⌞⌟-idem _ =  refl

open ERA Indˣᴱᴿᴬ using () renaming (Res to Resˣ; _✓_ to _✓ˣ_; ε to εˣ;
  _↝_ to _↝ˣ_)

-- Exclusively own a proposition at an index

line-indˣ :  ℕ →  Prop' ∞ →  Resˣ
line-indˣ i P =  updⁿᵐ i (#ˣ P) εˣ

abstract

  -- Add a new proposition and get a line

  add-indˣ :
    (Qᶠᵐ , εˣ) ↝ˣ λ(_ : ⊤₀) → updᶠᵐ (bndᶠᵐ Qᶠᵐ) P Qᶠᵐ , line-indˣ (bndᶠᵐ Qᶠᵐ) P
  add-indˣ _ _ .proj₀ =  _
  add-indˣ {_ |ᶠᵐ (n , _)} Rˣ˙ Q✓Rˣ∙ε .proj₁ j
    rewrite suc⊔-same {n}  with Q✓Rˣ∙ε j
  ... | (Qj←Rˣj∙? , j≥n⇒Rˣj∙?≡?)  with j ≡ᵇ n | ᵇ⇒≡ {j} {n}
  ...   | ff | _ =  Qj←Rˣj∙? , j≥n⇒Rˣj∙?≡? ∘ <⇒≤
  ...   | tt | ⇒j≡n  rewrite ⇒j≡n _ | ∙ˣ-?ˣ {x = Rˣ˙ n} | j≥n⇒Rˣj∙?≡? ≤-refl
    =  refl , absurd ∘ <-irrefl

  -- If we validly have a line, then its index is within the bound

  line-bound-indˣ :  Qᶠᵐ ✓ˣ line-indˣ i P →  i < bndᶠᵐ Qᶠᵐ
  line-bound-indˣ {_ |ᶠᵐ (n , _)} {i = i} Q✓iP  with i <≥ n
  ... | inj₀ i<n =  i<n
  ... | inj₁ i≥n  with Q✓iP i
  ...   | (_ , i≥n⇒iPi≡?)  rewrite ≡ᵇ-refl {i}  with i≥n⇒iPi≡? i≥n
  ...     | ()

  -- Remove a proposition consuming a line

  rem-indˣ :
    (Qᶠᵐ , line-indˣ i P) ↝ˣ λ(_ : i < bndᶠᵐ Qᶠᵐ) → updᶠᵐ i ⊤' Qᶠᵐ , εˣ
  rem-indˣ {_ |ᶠᵐ (n , _)} {i} Rˣ˙ Q✓Rˣ∙iP .proj₀  with i <≥ n
  ... | inj₀ i<n =  i<n
  ... | inj₁ i≥n  with Q✓Rˣ∙iP _ .proj₁ i≥n
  ...   | Rˣ∙iPi≡?  rewrite ≡ᵇ-refl {i}  with Rˣ˙ i | Rˣ∙iPi≡?
  ...     | ?ˣ | ()
  rem-indˣ {Qᶠᵐ} {i} Rˣ˙ Q✓Rˣ∙iP .proj₁ j
    rewrite suc⊔-< $ line-bound-indˣ {Qᶠᵐ} $ Indˣᴱᴿᴬ .✓-rem {Qᶠᵐ} {Rˣ˙} Q✓Rˣ∙iP
    with Q✓Rˣ∙iP j
  ... | (Qj←Rˣj∙iPj , j≥n⇒Rˣj∙iPj≡?)  with j ≡ᵇ i | ᵇ⇒≡ {j} {i}
  ...   | ff | _ =  Qj←Rˣj∙iPj , j≥n⇒Rˣj∙iPj≡?
  ...   | tt | ⇒j≡i  rewrite ⇒j≡i _  with Rˣ˙ i
  ...     | ?ˣ =  _ , λ _ → refl

--------------------------------------------------------------------------------
-- Ind□ᴱᴿᴬ :  Persistent indirection ERA

Ind□ᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ 2ᴸ

Ind□ᴱᴿᴬ .Env =  Finmap

Ind□ᴱᴿᴬ .Res =  ℕ →  List (Prop' ∞)

-- We need the bound equality m ≡ n because ✓ uses the bound information

Ind□ᴱᴿᴬ ._≈ᴱ_ (P˙ |ᶠᵐ (m , _)) (Q˙ |ᶠᵐ (n , _)) =
  m ≡ n  ×  (∀ i →  P˙ i ≡ Q˙ i)

Ind□ᴱᴿᴬ ._≈_ Ps˙ Qs˙ =  ∀ i →  Ps˙ i ≈ᴸ Qs˙ i

-- Qs˙ i agrees with P˙ i and equals [] if i is in the null range

Ind□ᴱᴿᴬ ._✓_ (P˙ |ᶠᵐ (n , _)) Qs˙ =
  ∀ i →  (∀{Q} →  Q ∈ᴸ Qs˙ i →  P˙ i ≡ Q)  ×  (i ≥ n →  Qs˙ i ≡ [])

Ind□ᴱᴿᴬ ._∙_ Ps˙ Qs˙ i =  Ps˙ i ++ Qs˙ i

Ind□ᴱᴿᴬ .ε i =  []

Ind□ᴱᴿᴬ .⌞_⌟ Ps˙ =  Ps˙

Ind□ᴱᴿᴬ .refl˜ᴱ =  refl , λ _ → refl

Ind□ᴱᴿᴬ .◠˜ᴱ_ (refl , ∀iPi≡Qi) =  refl , λ i → ◠ ∀iPi≡Qi i

Ind□ᴱᴿᴬ ._◇˜ᴱ_ (refl , ∀iPi≡Qi) (refl , ∀iQi≡Ri) =
  refl , λ i → ∀iPi≡Qi i ◇ ∀iQi≡Ri i

Ind□ᴱᴿᴬ .refl˜ _ =  ≈ᴸ-refl

Ind□ᴱᴿᴬ .◠˜_ ∀iPsi≈Qsi i =  ≈ᴸ-sym $ ∀iPsi≈Qsi i

Ind□ᴱᴿᴬ ._◇˜_ ∀iPsi≈Qsi ∀iQsi≈Rsi i =  ≈ᴸ-trans (∀iPsi≈Qsi i) (∀iQsi≈Rsi i)

Ind□ᴱᴿᴬ .∙-congˡ ∀iPsi≈Qsi i =  ++-congˡ $ ∀iPsi≈Qsi i

Ind□ᴱᴿᴬ .∙-unitˡ _ =  ≈ᴸ-refl

Ind□ᴱᴿᴬ .∙-comm {a = Ps˙} i =  ++-comm {as = Ps˙ i}

Ind□ᴱᴿᴬ .∙-assocˡ {a = Ps˙} i =  ≡⇒≈ᴸ $ ++-assocˡ {as = Ps˙ i}

Ind□ᴱᴿᴬ .✓-resp (refl , ∀iPi≡Qi) ∀iRsi≈Ssi P✓R i  with P✓R i | ∀iRsi≈Ssi i
... | (Pi≡Rsi , i≥n⇒Rsi≡[]) | (Rsi⊆Ssi , Ssi⊆Rsi)  rewrite ∀iPi≡Qi i =
  (λ S∈Ssi → Pi≡Rsi $ Ssi⊆Rsi S∈Ssi) ,
  λ i≥n →  ⊆ᴸ-[] $ subst (_ ⊆ᴸ_) (i≥n⇒Rsi≡[] i≥n) Ssi⊆Rsi

Ind□ᴱᴿᴬ .✓-rem R✓Ps++Qs i  with R✓Ps++Qs i
... | Ri≡Ps++Qsi , i≥n⇒Psi++Qsi≡[] =
  (λ Q∈Qsi → Ri≡Ps++Qsi $ ++-⊆ᴸ-introʳ Q∈Qsi) ,
  λ i≥n →  proj₁ $ ++-≡[] $ i≥n⇒Psi++Qsi≡[] i≥n

Ind□ᴱᴿᴬ .✓-ε _ =  (λ ()) , λ _ → refl

Ind□ᴱᴿᴬ .⌞⌟-cong =  id

Ind□ᴱᴿᴬ .⌞⌟-add =  -, λ _ → ≈ᴸ-refl

Ind□ᴱᴿᴬ .⌞⌟-unitˡ _ =  ++-idem

Ind□ᴱᴿᴬ .⌞⌟-idem _ =  ≈ᴸ-refl

open ERA Ind□ᴱᴿᴬ using () renaming (Res to Res□; ε to ε□; _↝_ to _↝□_)

-- Persistently own a proposition at an index

line-ind□ :  ℕ →  Prop' ∞ →  Res□
line-ind□ i P =  updⁿᵐ i [ P ] ε□

abstract

  -- Add a new proposition and get a line

  add-ind□ :
    (Qᶠᵐ , ε□) ↝□ λ(_ : ⊤₀) → updᶠᵐ (bndᶠᵐ Qᶠᵐ) P Qᶠᵐ , line-ind□ (bndᶠᵐ Qᶠᵐ) P
  add-ind□ _ _ .proj₀ =  _
  add-ind□ {_ |ᶠᵐ (n , _)} Rs˙ Q✓Rs∙ε .proj₁ j
    rewrite suc⊔-same {n}  with Q✓Rs∙ε j
  ... | (Qj≡Rsj++[] , j≥n⇒Rsj++[]≡[])  with j ≡ᵇ n | ᵇ⇒≡ {j} {n}
  ...   | ff | _ =  Qj≡Rsj++[] , j≥n⇒Rsj++[]≡[] ∘ <⇒≤
  ...   | tt | ⇒j≡n  rewrite ⇒j≡n _ | ++-[] {as = Rs˙ n} | j≥n⇒Rsj++[]≡[] ≤-refl
    =  (λ{ (by-hd refl) → refl }) , absurd ∘ <-irrefl
