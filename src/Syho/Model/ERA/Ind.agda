--------------------------------------------------------------------------------
-- Exclusive & persistent indirection ERAs
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.ERA.Ind where

open import Base.Level using (2ᴸ)
open import Base.Func using (_∘_; _$_; id; _▷_)
open import Base.Few using (⊤₀; absurd)
open import Base.Eq using (_≡_; refl; ◠_; _◇_; subst)
open import Base.Size using (∞)
open import Base.Option using (¿_; š_; ň)
open import Base.Prod using (_×_; π₀; π₁; _,_; -,_)
open import Base.Sum using (ĩ₀_; ĩ₁_)
open import Base.Dec using (yes; no; upd˙; _≡?_; ≡?-refl)
open import Base.Nat using (ℕ; ṡ_; _≥_; _<_; <⇒≤; ≤-refl; <-irrefl; _<≥_)
open import Base.List using (List; []; [_]; _⧺_; _∈ᴸ_; _≈ᴸ_; _✓ᴸ_; ⧺-assocˡ;
  ≈ᴸ-refl; ≡⇒≈ᴸ; ≈ᴸ-sym; ≈ᴸ-trans; ⧺-congˡ; ⧺-idem; ⧺-comm; ✓ᴸ-resp; ✓ᴸ-rem;
  ✓ᴸ-alloc; ✓ᴸ-agree)
open import Syho.Logic.Prop using (Prop'; ⊤')
open import Syho.Model.ERA.Base using (ERA)
open import Syho.Model.Lib.Exc using (Exc; ?ˣ; #ˣ_; _∙ˣ_; _✓ˣ_; ∙ˣ-comm;
  ∙ˣ-assocˡ; ✓ˣ-rem; ✓ˣ-alloc; ✓ˣ-agree; ✓ˣ-free)

open ERA using (Env; Res; _≈_; _✓_; _∙_; ε; ⌞_⌟; refl˜; ◠˜_; _◇˜_; ∙-congˡ;
  ∙-unitˡ; ∙-comm; ∙-assocˡ; ✓-resp; ✓-rem; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem)

private variable
  P :  Prop' ∞
  Qˇ˙ :  ℕ → ¿ Prop' ∞
  i n :  ℕ

--------------------------------------------------------------------------------
-- Indˣᴱᴿᴬ :  Exclusive indirection ERA

Indˣᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ

Indˣᴱᴿᴬ .Env =  (ℕ →  ¿ Prop' ∞)  ×  ℕ

Indˣᴱᴿᴬ .Res =  ℕ →  Exc (Prop' ∞)

Indˣᴱᴿᴬ ._≈_ Pˣ˙ Qˣ˙ =  ∀ i →  Pˣ˙ i ≡ Qˣ˙ i

-- Pˇ˙ i is ň for i in the null range and Qˣ˙ i agrees with Pˇ˙ i for all i

Indˣᴱᴿᴬ ._✓_ (Pˇ˙ , n) Qˣ˙ =
  (∀{i} →  i ≥ n →  Pˇ˙ i ≡ ň)  ×  (∀ i →  Pˇ˙ i ✓ˣ Qˣ˙ i)

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

Indˣᴱᴿᴬ .✓-resp _ (✓Pˇ , _) .π₀ =  ✓Pˇ
Indˣᴱᴿᴬ .✓-resp Qˣi≡Rˣi (-, Pˇi✓Qˣi) .π₁ i  rewrite ◠ Qˣi≡Rˣi i =  Pˇi✓Qˣi i

Indˣᴱᴿᴬ .✓-rem (✓Pˇ , _) .π₀ =  ✓Pˇ
Indˣᴱᴿᴬ .✓-rem {a = Qˣ˙} (-, Pˇ✓Qˣ∙Rˣ) .π₁ i =  ✓ˣ-rem {x = Qˣ˙ i} $ Pˇ✓Qˣ∙Rˣ i

Indˣᴱᴿᴬ .⌞⌟-cong _ _ =  refl

Indˣᴱᴿᴬ .⌞⌟-add =  (λ _ → ?ˣ) , λ _ → refl

Indˣᴱᴿᴬ .⌞⌟-unitˡ _ =  refl

Indˣᴱᴿᴬ .⌞⌟-idem _ =  refl

open ERA Indˣᴱᴿᴬ public using () renaming (Env to Env-indˣ)

open ERA Indˣᴱᴿᴬ using () renaming (Res to Resˣ; ε to εˣ; _↝_ to _↝ˣ_)

-- Exclusively own a proposition at an index

line-indˣ :  ℕ →  Prop' ∞ →  Resˣ
line-indˣ i P =  upd˙ i (#ˣ P) εˣ

abstract

  -- Add a new proposition and get a line

  alloc-indˣ :  ((Qˇ˙ , n) , εˣ)  ↝ˣ  λ(_ : ⊤₀) →
                  (upd˙ n (š P) Qˇ˙ , ṡ n) , line-indˣ n P
  alloc-indˣ _ _ .π₀ =  _
  alloc-indˣ {n = n} _ (✓Qˇ , _) .π₁ .π₀ {i}  with i ≡? n
  … | no _ =  ✓Qˇ ∘ <⇒≤
  … | yes refl =  absurd ∘ <-irrefl
  alloc-indˣ {n = n} Rˣ˙ (✓Qˇ , Qˇ✓Rˣ) .π₁ .π₁ i  with i ≡? n | Qˇ✓Rˣ i
  … | no _ | Qˇi✓Rˣi =  Qˇi✓Rˣi
  … | yes refl | Qˇn✓Rˣn  rewrite ✓Qˇ ≤-refl =  ✓ˣ-alloc {x = Rˣ˙ n} Qˇn✓Rˣn

  -- Remove a proposition consuming a line

  use-indˣ :  ((Qˇ˙ , n) , line-indˣ i P)  ↝ˣ
                λ(_ :  Qˇ˙ i ≡ š P  ×  i < n) →  (upd˙ i ň Qˇ˙ , n) , εˣ
  use-indˣ {n = n} {i} Rˣ˙ (✓Qˇ , Qˇ✓Rˣ∙iP) .π₀  with Qˇ✓Rˣ∙iP i
  … | Qˇi✓Rˣi∙#P  rewrite ≡?-refl {a = i}  with ✓ˣ-agree {x = Rˣ˙ i} Qˇi✓Rˣi∙#P
  …   | Qˇi≡šP  with i <≥ n
  …     | ĩ₀ i<n =  Qˇi≡šP , i<n
  …     | ĩ₁ i≥n  rewrite ✓Qˇ i≥n  with Qˇi≡šP
  …       | ()
  use-indˣ {i = i} Rˣ˙ (✓Qˇ , _) .π₁ .π₀ {j}  with j ≡? i
  … | no _ =  ✓Qˇ
  … | yes refl =  λ _ → refl
  use-indˣ {i = i} Rˣ˙ (-, Qˇ✓Rˣ∙iP) .π₁ .π₁ j  with j ≡? i | Qˇ✓Rˣ∙iP j
  … | no _ | Qˇj✓Rˣj∙? =  Qˇj✓Rˣj∙?
  … | yes refl | Qˇi✓Rˣi∙#P =  ✓ˣ-free {x = Rˣ˙ i} Qˇi✓Rˣi∙#P

--------------------------------------------------------------------------------
-- Ind□ᴱᴿᴬ :  Persistent indirection ERA

Ind□ᴱᴿᴬ :  ERA 2ᴸ 2ᴸ 2ᴸ 2ᴸ

Ind□ᴱᴿᴬ .Env =  (ℕ →  ¿ Prop' ∞)  ×  ℕ

Ind□ᴱᴿᴬ .Res =  ℕ →  List (Prop' ∞)

Ind□ᴱᴿᴬ ._≈_ Ps˙ Qs˙ =  ∀ i →  Ps˙ i ≈ᴸ Qs˙ i

-- Qs˙ i agrees with P˙ i and equals [] if i is in the null range

Ind□ᴱᴿᴬ ._✓_ (Pˇ˙ , n) Qs˙ =
  (∀{i} →  i ≥ n →  Pˇ˙ i ≡ ň)  ×  (∀ i → Pˇ˙ i ✓ᴸ Qs˙ i)

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

Ind□ᴱᴿᴬ .✓-resp _ (✓Pˇ , _) .π₀ =  ✓Pˇ
Ind□ᴱᴿᴬ .✓-resp Qs≈Rs (-, Pˇ✓Qs) .π₁ i =  ✓ᴸ-resp (Qs≈Rs i) $ Pˇ✓Qs i

Ind□ᴱᴿᴬ .✓-rem (✓Pˇ , _) .π₀ =  ✓Pˇ
Ind□ᴱᴿᴬ .✓-rem (-, Pˇ✓Qs⧺Rs) .π₁ i =  ✓ᴸ-rem $ Pˇ✓Qs⧺Rs i

Ind□ᴱᴿᴬ .⌞⌟-cong =  id

Ind□ᴱᴿᴬ .⌞⌟-add =  -, λ _ → ≈ᴸ-refl

Ind□ᴱᴿᴬ .⌞⌟-unitˡ _ =  ⧺-idem

Ind□ᴱᴿᴬ .⌞⌟-idem _ =  ≈ᴸ-refl

open ERA Ind□ᴱᴿᴬ public using () renaming (Env to Env-ind□)

open ERA Ind□ᴱᴿᴬ using () renaming (Res to Res□; ε to ε□; _↝_ to _↝□_)

-- Persistently own a proposition at an index

line-ind□ :  ℕ →  Prop' ∞ →  Res□
line-ind□ i P =  upd˙ i [ P ] ε□

abstract

  -- Add a new proposition and get a line

  alloc-ind□ :  ((Qˇ˙ , n) , ε□)  ↝□  λ(_ : ⊤₀) →
                  (upd˙ n (š P) Qˇ˙ , ṡ n) , line-ind□ n P
  alloc-ind□ _ _ .π₀ =  _
  alloc-ind□ {n = n} _ (✓Qˇ , _) .π₁ .π₀ {i}  with i ≡? n
  … | no _ =  ✓Qˇ ∘ <⇒≤
  … | yes refl =  absurd ∘ <-irrefl
  alloc-ind□ {n = n} Rs˙ (✓Qˇ , Qˇ✓Rs) .π₁ .π₁ i  with i ≡? n | Qˇ✓Rs i
  … | no _ | Qˇi✓Rsi =  Qˇi✓Rsi
  … | yes refl | Qˇn✓Rsn  rewrite ✓Qˇ ≤-refl =  ✓ᴸ-alloc Qˇn✓Rsn

  -- Get an agreement from a line

  use-ind□ :  ((Qˇ˙ , n) , line-ind□ i P)  ↝□
                λ(_ :  Qˇ˙ i ≡ š P  ×  i < n) →  ((Qˇ˙ , n) , line-ind□ i P)
  use-ind□ {n = n} {i} Rs˙ (✓Qˇ , Qˇ✓Rs⧺iP) .π₀  with Qˇ✓Rs⧺iP i
  … | Qˇi✓Rsi⧺[P]  rewrite ≡?-refl {a = i}  with ✓ᴸ-agree Qˇi✓Rsi⧺[P]
  …   | Qˇi≡šP  with i <≥ n
  …     | ĩ₀ i<n =  Qˇi≡šP , i<n
  …     | ĩ₁ i≥n  rewrite ✓Qˇ i≥n  with Qˇi≡šP
  …       | ()
  use-ind□ _ ✓Qˇ✓Rs⧺iP .π₁ =  ✓Qˇ✓Rs⧺iP

--------------------------------------------------------------------------------
-- On both indirection ERAs

Env-ind :  Set₂
Env-ind =  Env-indˣ × Env-ind□
