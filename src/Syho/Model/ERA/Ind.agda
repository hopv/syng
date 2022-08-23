--------------------------------------------------------------------------------
-- Exclusive & persistent indirection ERAs
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Ind where

open import Base.Level using (2ᴸ)
open import Base.Size using (∞)
open import Base.Eq using (_≡_; refl; ◠_; _◇_; subst)
open import Base.Func using (_∘_; _$_; id; _▷_)
open import Base.Prod using (_×_; proj₀; proj₁; _,_; -,_)
open import Base.Sum using (inj₀; inj₁)
open import Base.Few using (absurd)
open import Base.Nat using (ℕ; _≤_; _<_; <⇒≤; ≤-refl; <-irrefl; _≤>_; _≡ᵇ_; ᵇ⇒≡;
  ≡ᵇ-refl)
open import Base.Nmap using (updⁿᵐ)
open import Base.Bool using (ff; tt)
open import Base.List using (List; []; [_]; _++_; ++-assocˡ; ++-[]; ++-≡[])
open import Base.List.Set using (by-hd; _∈ᴸ_; _⊆ᴸ_; _≈ᴸ_; ≈ᴸ-refl; ≡⇒≈ᴸ; ≈ᴸ-sym;
  ≈ᴸ-trans; ++-congˡ; ++-idem; ++-comm; ⊆ᴸ-[]; ++-⊆ᴸ-introʳ)
open import Syho.Logic.Prop using (Prop'; ⊤')
open import Syho.Model.ERA using (ERA)
open import Syho.Model.Exc using (Exc; ?ˣ; #ˣ_; _∙ˣ_; _←ˣ_; ∙ˣ-comm; ∙ˣ-assocˡ;
  ∙ˣ-?ˣ)

open import Base.Finmap (Prop' ∞) (_≡ ⊤') using (Finmap; _|ᶠᵐ_; boundᶠᵐ; addᶠᵐ;
  inupdᶠᵐ)

open ERA using (Env; Res; _≈ᴱ_; _≈_; _✓_; _∙_; ε; ⌞_⌟; refl˜ᴱ; ◠˜ᴱ_; _◇˜ᴱ_;
  refl˜; ◠˜_; _◇˜_; ∙-congˡ; ∙-unitˡ; ∙-comm; ∙-assocˡ; ✓-resp; ✓-rem; ✓-ε;
  ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem)

private variable
  Pᶠᵐ :  Finmap
  Q :  Prop' ∞
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
  ∀ i →  P˙ i ←ˣ Qˣ˙ i  ×  (n ≤ i →  Qˣ˙ i ≡ ?ˣ)

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
  _↝_ to _↝ˣ_; _↝˙_ to _↝˙ˣ_)

-- Exclusively own a proposition at an index

line-indˣ :  ℕ →  Prop' ∞ →  Resˣ
line-indˣ i P =  updⁿᵐ i (#ˣ P) εˣ

abstract

  -- Add a new proposition and get a line

  add-indˣ :  (Pᶠᵐ , εˣ) ↝ˣ (addᶠᵐ Q Pᶠᵐ , line-indˣ (boundᶠᵐ Pᶠᵐ) Q)
  add-indˣ {_ |ᶠᵐ (n , _)} Rˣ˙ P✓Rˣ∙ε j  with P✓Rˣ∙ε j
  ... | (Pj←Rˣj∙? , n≤j⇒Rˣj∙?≡?)  with j ≡ᵇ n | ᵇ⇒≡ {j} {n}
  ...   | ff | _ =  Pj←Rˣj∙? , n≤j⇒Rˣj∙?≡? ∘ <⇒≤
  ...   | tt | ⇒j≡n  rewrite ⇒j≡n _ | ∙ˣ-?ˣ {x = Rˣ˙ n} | n≤j⇒Rˣj∙?≡? ≤-refl
    =  refl , absurd ∘ <-irrefl

  -- If we validly have a line, then its index is within the bound

  line-bound-indˣ :  Pᶠᵐ ✓ˣ line-indˣ i Q →  i < boundᶠᵐ Pᶠᵐ
  line-bound-indˣ {_ |ᶠᵐ (n , _)} {i = i} P✓iQ  with n ≤> i
  ... | inj₁ i<n =  i<n
  ... | inj₀ n≤i  with P✓iQ i
  ...   | (_ , n≤i⇒iQi≡?)  rewrite ≡ᵇ-refl {i}  with n≤i⇒iQi≡? n≤i
  ...     | ()

  -- Remove a proposition consuming a line

  rem-indˣ :  (Pᶠᵐ , line-indˣ i Q) ↝˙ˣ λ i<n → (inupdᶠᵐ i ⊤' Pᶠᵐ i<n , εˣ)
  rem-indˣ {Pᶠᵐ} Rˣ˙ P✓Rˣ∙iQ .proj₀ =
    line-bound-indˣ {Pᶠᵐ} $ Indˣᴱᴿᴬ .✓-rem {Pᶠᵐ} {Rˣ˙} P✓Rˣ∙iQ
  rem-indˣ {i = i} Rˣ˙ P✓Rˣ∙iQ .proj₁ j  with P✓Rˣ∙iQ j
  ... | (Pj←Rˣj∙iQj , n≤j⇒Rˣj∙iQj≡?)  with j ≡ᵇ i | ᵇ⇒≡ {j} {i}
  ...   | ff | _ =  Pj←Rˣj∙iQj , n≤j⇒Rˣj∙iQj≡?
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
  ∀ i →  (∀{Q} →  Q ∈ᴸ Qs˙ i →  P˙ i ≡ Q)  ×  (n ≤ i →  Qs˙ i ≡ [])

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
... | (Pi≡Rsi , n≤i⇒Rsi≡[]) | (Rsi⊆Ssi , Ssi⊆Rsi)  rewrite ∀iPi≡Qi i =
  (λ S∈Ssi → Pi≡Rsi $ Ssi⊆Rsi S∈Ssi) ,
  λ n≤i →  ⊆ᴸ-[] $ subst (_ ⊆ᴸ_) (n≤i⇒Rsi≡[] n≤i) Ssi⊆Rsi

Ind□ᴱᴿᴬ .✓-rem R✓Ps++Qs i  with R✓Ps++Qs i
... | Ri≡Ps++Qsi , n≤i⇒Psi++Qsi≡[] =
  (λ Q∈Qsi → Ri≡Ps++Qsi $ ++-⊆ᴸ-introʳ Q∈Qsi) ,
  λ n≤i →  proj₁ $ ++-≡[] $ n≤i⇒Psi++Qsi≡[] n≤i

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

  add-ind□ :  (Pᶠᵐ , ε□) ↝□ (addᶠᵐ Q Pᶠᵐ , line-ind□ (boundᶠᵐ Pᶠᵐ) Q)
  add-ind□ {_ |ᶠᵐ (n , _)} Rs˙ P✓Rs∙ε j  with P✓Rs∙ε j
  ... | (Pj≡Rsj++[] , n≤j⇒Rsj++[]≡[])  with j ≡ᵇ n | ᵇ⇒≡ {j} {n}
  ...   | ff | _ =  Pj≡Rsj++[] , n≤j⇒Rsj++[]≡[] ∘ <⇒≤
  ...   | tt | ⇒j≡n  rewrite ⇒j≡n _ | ++-[] {as = Rs˙ n} | n≤j⇒Rsj++[]≡[] ≤-refl
    =  (λ{ (by-hd refl) → refl }) , absurd ∘ <-irrefl
