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
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Base.Bool using (ff; tt)
open import Base.Nat using (ℕ; ṡ_; _≥_; _<_; <⇒≤; ≤-refl; <-irrefl; _<≥_; _≡ᵇ_;
  ᵇ⇒≡; ≡ᵇ-refl)
open import Base.Natmap using (updᴺᴹ)
open import Base.List using (List; _∷_; []; [_]; _⧺_; ⧺-assocˡ; ⧺-[]; ⧺-≡[])
open import Base.List.Set using (by-hd; _∈ᴸ_; _⊆ᴸ_; _≈ᴸ_; ≈ᴸ-refl; ≡⇒≈ᴸ; ≈ᴸ-sym;
  ≈ᴸ-trans; ⧺-congˡ; ⧺-idem; ⧺-comm; ∈ᴸ-[?]; ∈ᴸ-⧺-ĩ₁; ⊆ᴸ-[]; ⧺-⊆ᴸ-introʳ)
open import Syho.Logic.Prop using (Prop'; ⊤')
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.Lib.Exc using (Exc; ?ˣ; #ˣ_; _∙ˣ_; _←ˣ_; ∙ˣ-comm;
  ∙ˣ-assocˡ; ∙ˣ-?ˣ)

open ERA using (Env; Res; _≈_; _✓_; _∙_; ε; ⌞_⌟; refl˜; ◠˜_; _◇˜_; ∙-congˡ;
  ∙-unitˡ; ∙-comm; ∙-assocˡ; ✓-resp; ✓-rem; ✓-ε; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ;
  ⌞⌟-idem)

private variable
  P :  Prop' ∞
  Q˙ :  ℕ → Prop' ∞
  i n :  ℕ

--------------------------------------------------------------------------------
-- Indˣᴱᴿᴬ :  Exclusive indirection ERA

Indˣᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ

Indˣᴱᴿᴬ .Env =  (ℕ → Prop' ∞) × ℕ

Indˣᴱᴿᴬ .Res =  ℕ →  Exc (Prop' ∞)

Indˣᴱᴿᴬ ._≈_ Pˣ˙ Qˣ˙ =  ∀ i →  Pˣ˙ i ≡ Qˣ˙ i

-- Qˣ˙ i agrees with P˙ i and equals ?ˣ if i is in the null range

Indˣᴱᴿᴬ ._✓_ (P˙ , n) Qˣ˙ =
  ∀ i →  P˙ i ←ˣ Qˣ˙ i  ×  (i ≥ n →  Qˣ˙ i ≡ ?ˣ)

Indˣᴱᴿᴬ ._∙_ Pˣ˙ Qˣ˙ i =  Pˣ˙ i ∙ˣ Qˣ˙ i

Indˣᴱᴿᴬ .ε _ =  ?ˣ

Indˣᴱᴿᴬ .⌞_⌟ _ _ =  ?ˣ

Indˣᴱᴿᴬ .refl˜ _ =  refl

Indˣᴱᴿᴬ .◠˜_ Pˣi≡Qˣi _ =  ◠ Pˣi≡Qˣi _

Indˣᴱᴿᴬ ._◇˜_ Pˣi≡Qˣi Qˣi≡Rˣi _ =  Pˣi≡Qˣi _ ◇ Qˣi≡Rˣi _

Indˣᴱᴿᴬ .∙-congˡ Pˣi≡Qˣi i  rewrite Pˣi≡Qˣi i =  refl

Indˣᴱᴿᴬ .∙-unitˡ _ =  refl

Indˣᴱᴿᴬ .∙-comm {a = Pˣ˙} _ =  ∙ˣ-comm {x = Pˣ˙ _}

Indˣᴱᴿᴬ .∙-assocˡ {a = Pˣ˙} _ =  ∙ˣ-assocˡ {x = Pˣ˙ _}

Indˣᴱᴿᴬ .✓-resp Rˣi≡Sˣi P✓Rˣ i  with P✓Rˣ i
… | P✓Rˣi  rewrite Rˣi≡Sˣi i =  P✓Rˣi

Indˣᴱᴿᴬ .✓-rem {a = Pˣ˙} {b = Qˣ˙} R✓Pˣ∙Qˣ i  with Pˣ˙ i | Qˣ˙ i | R✓Pˣ∙Qˣ i
… | ?ˣ | _ | R✓Qˣi =  R✓Qˣi
… | _ | ?ˣ | _ =  -, λ _ → refl

Indˣᴱᴿᴬ .✓-ε _ =  -, λ _ → refl

Indˣᴱᴿᴬ .⌞⌟-cong _ _ =  refl

Indˣᴱᴿᴬ .⌞⌟-add =  (λ _ → ?ˣ) , λ _ → refl

Indˣᴱᴿᴬ .⌞⌟-unitˡ _ =  refl

Indˣᴱᴿᴬ .⌞⌟-idem _ =  refl

open ERA Indˣᴱᴿᴬ public using () renaming (Env to Env-indˣ)

open ERA Indˣᴱᴿᴬ using () renaming (Res to Resˣ; _✓_ to _✓ˣ_; ε to εˣ;
  _↝_ to _↝ˣ_)

-- Exclusively own a proposition at an index

line-indˣ :  ℕ →  Prop' ∞ →  Resˣ
line-indˣ i P =  updᴺᴹ i (#ˣ P) εˣ

abstract

  -- Add a new proposition and get a line

  alloc-indˣ :  ((Q˙ , n) , εˣ)  ↝ˣ  λ(_ : ⊤₀) →
                  (updᴺᴹ n P Q˙ , ṡ n) , line-indˣ n P
  alloc-indˣ _ _ .proj₀ =  _
  alloc-indˣ {n = n} Rˣ˙ Q✓Rˣ∙ε .proj₁ j  with Q✓Rˣ∙ε j
  … | (Qj←Rˣj∙? , j≥n⇒Rˣj∙?≡?)  with j ≡ᵇ n | ᵇ⇒≡ {j} {n}
  …   | ff | _ =  Qj←Rˣj∙? , j≥n⇒Rˣj∙?≡? ∘ <⇒≤
  …   | tt | ⇒j≡n  rewrite ⇒j≡n _ | ∙ˣ-?ˣ {x = Rˣ˙ n} | j≥n⇒Rˣj∙?≡? ≤-refl =
    refl , absurd ∘ <-irrefl

  -- Remove a proposition consuming a line

  use-indˣ :  ((Q˙ , n) , line-indˣ i P)  ↝ˣ
                λ(_ :  Q˙ i ≡ P  ×  i < n) →  (updᴺᴹ i ⊤' Q˙ , n) , εˣ
  use-indˣ {i = i} Rˣ˙ Q✓Rˣ∙iP .proj₀ .proj₀  with Q✓Rˣ∙iP i
  … | (Qi←Rˣi∙#P , _)  rewrite ≡ᵇ-refl {i}  with Rˣ˙ i
  …   | ?ˣ =  Qi←Rˣi∙#P
  use-indˣ {n = n} {i} Rˣ˙ Q✓Rˣ∙iP .proj₀ .proj₁  with i <≥ n
  … | ĩ₀ i<n =  i<n
  … | ĩ₁ i≥n  with Q✓Rˣ∙iP _ .proj₁ i≥n
  …   | Rˣi∙P≡?  rewrite ≡ᵇ-refl {i}  with Rˣ˙ i | Rˣi∙P≡?
  …     | ?ˣ | ()
  use-indˣ {i = i} Rˣ˙ Q✓Rˣ∙iP .proj₁ j  with Q✓Rˣ∙iP j
  … | (Qj←Rˣj∙iPj , j≥n⇒Rˣj∙iPj≡?)  with j ≡ᵇ i | ᵇ⇒≡ {j} {i}
  …   | ff | _ =  Qj←Rˣj∙iPj , j≥n⇒Rˣj∙iPj≡?
  …   | tt | ⇒j≡i  rewrite ⇒j≡i _  with Rˣ˙ i
  …     | ?ˣ =  _ , λ _ → refl

--------------------------------------------------------------------------------
-- Ind□ᴱᴿᴬ :  Persistent indirection ERA

Ind□ᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ

Ind□ᴱᴿᴬ .Env =  (ℕ → Prop' ∞) × ℕ

Ind□ᴱᴿᴬ .Res =  ℕ →  List (Prop' ∞)

Ind□ᴱᴿᴬ ._≈_ Ps˙ Qs˙ =  ∀ i →  Ps˙ i ≈ᴸ Qs˙ i

-- Qs˙ i agrees with P˙ i and equals [] if i is in the null range

Ind□ᴱᴿᴬ ._✓_ (P˙ , n) Qs˙ =
  ∀ i →  (∀{Q} →  Q ∈ᴸ Qs˙ i →  P˙ i ≡ Q)  ×  (i ≥ n →  Qs˙ i ≡ [])

Ind□ᴱᴿᴬ ._∙_ Ps˙ Qs˙ i =  Ps˙ i ⧺ Qs˙ i

Ind□ᴱᴿᴬ .ε _ =  []

Ind□ᴱᴿᴬ .⌞_⌟ Ps˙ =  Ps˙

Ind□ᴱᴿᴬ .refl˜ _ =  ≈ᴸ-refl

Ind□ᴱᴿᴬ .◠˜_ Psi≈Qsi _ =  ≈ᴸ-sym $ Psi≈Qsi _

Ind□ᴱᴿᴬ ._◇˜_ Psi≈Qsi Qsi≈Rsi _ =  ≈ᴸ-trans (Psi≈Qsi _) (Qsi≈Rsi _)

Ind□ᴱᴿᴬ .∙-congˡ Psi≈Qsi _ =  ⧺-congˡ $ Psi≈Qsi _

Ind□ᴱᴿᴬ .∙-unitˡ _ =  ≈ᴸ-refl

Ind□ᴱᴿᴬ .∙-comm {a = Ps˙} _ =  ⧺-comm {as = Ps˙ _}

Ind□ᴱᴿᴬ .∙-assocˡ {a = Ps˙} _ =  ≡⇒≈ᴸ $ ⧺-assocˡ {as = Ps˙ _}

Ind□ᴱᴿᴬ .✓-resp Rsi≈Ssi P✓R i  with P✓R i | Rsi≈Ssi i
… | (Pi≡Rsi , i≥n⇒Rsi≡[]) | (Rsi⊆Ssi , Ssi⊆Rsi)  =
  (λ S∈Ssi → Pi≡Rsi $ Ssi⊆Rsi S∈Ssi) ,
  λ i≥n →  ⊆ᴸ-[] $ subst (_ ⊆ᴸ_) (i≥n⇒Rsi≡[] i≥n) Ssi⊆Rsi

Ind□ᴱᴿᴬ .✓-rem R✓Ps⧺Qs i  with R✓Ps⧺Qs i
… | Ri≡Ps⧺Qsi , i≥n⇒Psi⧺Qsi≡[] =
  (λ Q∈Qsi → Ri≡Ps⧺Qsi $ ⧺-⊆ᴸ-introʳ Q∈Qsi) ,
  λ i≥n →  proj₁ $ ⧺-≡[] $ i≥n⇒Psi⧺Qsi≡[] i≥n

Ind□ᴱᴿᴬ .✓-ε _ =  (λ ()) , λ _ → refl

Ind□ᴱᴿᴬ .⌞⌟-cong =  id

Ind□ᴱᴿᴬ .⌞⌟-add =  -, λ _ → ≈ᴸ-refl

Ind□ᴱᴿᴬ .⌞⌟-unitˡ _ =  ⧺-idem

Ind□ᴱᴿᴬ .⌞⌟-idem _ =  ≈ᴸ-refl

open ERA Ind□ᴱᴿᴬ public using () renaming (Env to Env-ind□)

open ERA Ind□ᴱᴿᴬ using () renaming (Res to Res□; ε to ε□; _↝_ to _↝□_)

-- Persistently own a proposition at an index

line-ind□ :  ℕ →  Prop' ∞ →  Res□
line-ind□ i P =  updᴺᴹ i [ P ] ε□

abstract

  -- Add a new proposition and get a line

  alloc-ind□ :  ((Q˙ , n) , ε□)  ↝□  λ(_ : ⊤₀) →
                  (updᴺᴹ n P Q˙ , ṡ n) , line-ind□ n P
  alloc-ind□ _ _ .proj₀ =  _
  alloc-ind□ {n = n} Rs˙ Q✓Rs∙ε .proj₁ j  with Q✓Rs∙ε j
  … | (Qj≡Rsj⧺[] , j≥n⇒Rsj⧺[]≡[])  with j ≡ᵇ n | ᵇ⇒≡ {j} {n}
  …   | ff | _ =  Qj≡Rsj⧺[] , j≥n⇒Rsj⧺[]≡[] ∘ <⇒≤
  …   | tt | ⇒j≡n  rewrite ⇒j≡n _ | ⧺-[] {as = Rs˙ n} | j≥n⇒Rsj⧺[]≡[] ≤-refl =
    (λ{ (by-hd refl) → refl }) , absurd ∘ <-irrefl

  -- Get an agreement from a line

  use-ind□ :  ((Q˙ , n) , line-ind□ i P)  ↝□
                λ(_ :  Q˙ i ≡ P  ×  i < n) →  ((Q˙ , n) , line-ind□ i P)
  use-ind□ {i = i} Rs˙ Q✓Rs∙iP .proj₀ .proj₀  with Q✓Rs∙iP i
  … | (Qi≡Rsi⧺[P] , _)  rewrite ≡ᵇ-refl {i} =  Qi≡Rsi⧺[P] (∈ᴸ-⧺-ĩ₁ ∈ᴸ-[?])
  use-ind□ {n = n} {i} Rs˙ Q✓Rs∙iP .proj₀ .proj₁  with i <≥ n
  … | ĩ₀ i<n =  i<n
  … | ĩ₁ i≥n  with Q✓Rs∙iP _ .proj₁ i≥n
  …   | Rsi⧺[P]≡?  rewrite ≡ᵇ-refl {i}  with Rs˙ i | Rsi⧺[P]≡?
  …     | _ ∷ _ | ()
  …     | [] | ()
  use-ind□ _ Q✓Rˣ∙iP .proj₁ =  Q✓Rˣ∙iP

--------------------------------------------------------------------------------
-- On both indirection ERAs

Env-ind :  Set₂
Env-ind =  Env-indˣ × Env-ind□
