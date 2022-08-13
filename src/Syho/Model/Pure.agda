--------------------------------------------------------------------------------
-- Prove semantic soundness of the pure sequent
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.Model.Pure where

open import Base.Size using (Size; ∞)
open import Base.Func using (_$_; _▷_; flip; it)
open import Base.Thunk using (!)
open import Base.Few using (0₂; 1₂; binary; absurd)
open import Base.Prod using (_,_; proj₀; proj₁)
open import Syho.Logic.Prop using (Prop'; ∀₁˙; ∃₁˙; _∧_; _→'_; _∗_; _-∗_; |=>_;
  □_; Saveˣ; Save□; _↦⟨_⟩_; Free; IsBasic; ∀₁-IsBasic; ∃₁-IsBasic; ∗-IsBasic;
  □-IsBasic; Basic; isBasic; ∧-Basic)
open import Syho.Logic.Core using (_⊢[_]_; ⊢-refl; _»_;
  ∀₁-intro; ∃₁-elim; ∀₁-elim; ∃₁-intro; choice₁; →-intro; →-elim;
  ⊤∗-elim; ⊤∗-intro; ∗-comm; ∗-assocˡ; ∗-monoˡ; -∗-intro; -∗-elim;
  |=>-mono; |=>-intro; |=>-join; |=>-frameˡ; |=>-∃₁-out;
  □-mono; □-elim; □-dup; □ˡ-∧⇒∗; □-∀₁-in; □-∃₁-out; ∧-assocˡ; ∧-monoʳ)
open import Syho.Logic.Save using (Save□-□; Saveˣ-mono-∧; Save□-mono-∧)
open import Syho.Model.ERA using (ERA)
open import Syho.Model.ERA.Glob using (GlobRA)
open import Syho.Model.Prop GlobRA using (Propᵒ; monoᵒ; congᵒ; _⊨_; _⊨'_;
  ∀₁ᵒ-syntax; ∃₁ᵒ-syntax; ⊤ᵒ; _→ᵒ_; _∗ᵒ_; _-∗ᵒ_; |=>ᵒ_; □ᵒ_; Own-⌞⌟-□)
open ERA GlobRA using (_≈_; _∙_; ε; ⌞_⌟; refl˜; ◠˜_; _◇˜_; ≈⇒⊑; ⊑-refl; ⊑-trans;
  ⊑-respˡ; ✓-resp; ✓-mono; ∙-congˡ; ∙-congʳ; ∙-monoˡ; ∙-monoʳ; ∙-unitˡ; ∙-comm;
  ∙-assocˡ; ∙-assocʳ; ∙-incrˡ; ∙-incrʳ; ⌞⌟-unitˡ; ⌞⌟-idem; ⌞⌟-decr)
open import Syho.Model.Save.Exc using (Saveˣᵒ)
open import Syho.Model.Save.Pers using (Save□ᵒ; lineˢ□-⌞⌟)
open import Syho.Model.Basic using (⸨_⸩ᴮ[_]; ⸨_⸩ᴮ; ⸨⸩ᴮ-⇒□)

private variable
  P Q R S T :  Prop' ∞

--------------------------------------------------------------------------------
-- ⸨ ⸩ :  Interpreting propositions

⸨_⸩ :  (P : Prop' ∞) →  Propᵒ
⸨ ∀₁˙ P˙ ⸩ =  ∀₁ᵒ x , ⸨ P˙ x ⸩
⸨ ∃₁˙ P˙ ⸩ =  ∃₁ᵒ x , ⸨ P˙ x ⸩
⸨ P →' Q ⸩ =  ⸨ P ⸩ →ᵒ ⸨ Q ⸩
⸨ P ∗ Q ⸩ =  ⸨ P ⸩ ∗ᵒ ⸨ Q ⸩
⸨ P -∗ Q ⸩ =  ⸨ P ⸩ -∗ᵒ ⸨ Q ⸩
⸨ |=> P ⸩ =  |=>ᵒ ⸨ P ⸩
⸨ □ P ⸩ =  □ᵒ ⸨ P ⸩
⸨ Saveˣ P˂ ⸩ =  Saveˣᵒ (P˂ .!)
⸨ Save□ P˂ ⸩ =  Save□ᵒ (P˂ .!)
⸨ _ ↦⟨ _ ⟩ _ ⸩ =  ⊤ᵒ -- For now
⸨ Free _ _ ⸩ =  ⊤ᵒ -- For now

abstract

  -- ⸨ ⸩ᴮ[ ] / ⸨ ⸩ᴮ agrees with ⸨ ⸩

  ⸨⸩-ᴮ'⇒ :  (IsBaP : IsBasic P) →  ⸨ P ⸩ᴮ[ IsBaP ] ⊨' ⸨ P ⸩
  ⸨⸩-ᴮ'⇒ (∀₁-IsBasic IsBaP˙) ∀xPxa x =  ⸨⸩-ᴮ'⇒ (IsBaP˙ x) (∀xPxa x)
  ⸨⸩-ᴮ'⇒ (∃₁-IsBasic IsBaP˙) (x , Pxa) =  x , ⸨⸩-ᴮ'⇒ (IsBaP˙ x) Pxa
  ⸨⸩-ᴮ'⇒ (∗-IsBasic IsBaP IsBaQ) (b , c , bc≈a , Pb , Qc) =
    b , c , bc≈a , ⸨⸩-ᴮ'⇒ IsBaP Pb , ⸨⸩-ᴮ'⇒ IsBaQ Qc
  ⸨⸩-ᴮ'⇒ (□-IsBasic IsBaP) =  ⸨⸩-ᴮ'⇒ IsBaP

  ⸨⸩-⇒ᴮ' :  (IsBaP : IsBasic P) →  ⸨ P ⸩ ⊨' ⸨ P ⸩ᴮ[ IsBaP ]
  ⸨⸩-⇒ᴮ' (∀₁-IsBasic IsBaP˙) ∀xPxa x =  ⸨⸩-⇒ᴮ' (IsBaP˙ x) (∀xPxa x)
  ⸨⸩-⇒ᴮ' (∃₁-IsBasic IsBaP˙) (x , Pxa) =  x , ⸨⸩-⇒ᴮ' (IsBaP˙ x) Pxa
  ⸨⸩-⇒ᴮ' (∗-IsBasic IsBaP IsBaQ) (b , c , bc≈a , Pb , Qc) =
    b , c , bc≈a , ⸨⸩-⇒ᴮ' IsBaP Pb , ⸨⸩-⇒ᴮ' IsBaQ Qc
  ⸨⸩-⇒ᴮ' (□-IsBasic IsBaP) =  ⸨⸩-⇒ᴮ' IsBaP

  ⸨⸩-ᴮ⇒ :  {{_ : Basic P}} →  ⸨ P ⸩ᴮ ⊨' ⸨ P ⸩
  ⸨⸩-ᴮ⇒ =  ⸨⸩-ᴮ'⇒ isBasic

  ⸨⸩-⇒ᴮ :  {{_ : Basic P}} →  ⸨ P ⸩ ⊨' ⸨ P ⸩ᴮ
  ⸨⸩-⇒ᴮ =  ⸨⸩-⇒ᴮ' isBasic

--------------------------------------------------------------------------------
-- ⊢⇒⊨ :  Semantic soundness of the pure sequent

abstract

  private

    ∧⊢-chain :  S ∧ T ⊢[ ∞ ] P →  R ∧ P ⊢[ ∞ ] Q →  (R ∧ S) ∧ T ⊢[ ∞ ] Q
    ∧⊢-chain S∧T⊢P R∧P⊢Q =  ∧-assocˡ » ∧-monoʳ S∧T⊢P » R∧P⊢Q

  ⊢⇒⊨ :  P ⊢[ ∞ ] Q →  ⸨ P ⸩ ⊨ ⸨ Q ⸩

  -- ⊢-refl :  P ⊢[ ∞ ] P
  ⊢⇒⊨ ⊢-refl _ Pa =  Pa

  -- _»_ :  P ⊢[ ∞ ] Q →  Q ⊢[ ∞ ] R →  P ⊢[ ∞ ] R
  ⊢⇒⊨ (P⊢Q » Q⊢R) ✓a Pa =  Pa ▷ ⊢⇒⊨ P⊢Q ✓a ▷ ⊢⇒⊨ Q⊢R ✓a

  -- ∀₁-intro :  (∀₁ x → P ⊢[ ∞ ] Q˙ x) →  P ⊢[ ∞ ] ∀₁˙ Q˙
  ⊢⇒⊨ (∀₁-intro ∀xP⊢Qx) ✓a Pa x =  ⊢⇒⊨ (∀xP⊢Qx x) ✓a Pa

  -- ∃₁-elim :  (∀₁ x → P˙ x ⊢[ ∞ ] Q) →  ∃₁˙ P˙ ⊢[ ∞ ] Q
  ⊢⇒⊨ (∃₁-elim ∀xPx⊢Q) ✓a (x , Pxa) =  ⊢⇒⊨ (∀xPx⊢Q x) ✓a Pxa

  -- ∀₁-elim :  ∀ x →  ∀₁˙ P˙ ⊢[ ∞ ] P˙ x
  ⊢⇒⊨ (∀₁-elim _) _ ∀Pa =  ∀Pa _

  -- ∃₁-intro :  ∀ x →  P˙ x ⊢[ ∞ ] ∃₁˙ P˙
  ⊢⇒⊨ (∃₁-intro _) _ Px =  _ , Px

  -- choice₁ :  ∀₁ x , ∃₁ y , P˙˙ x y ⊢[ ∞ ] ∃₁ y˙ , ∀₁ x , P˙˙ x (y˙ x)
  -- It can be proved axiom-free thanks to the logic's predicativity
  ⊢⇒⊨ choice₁ _ ∀x∃₁yPxy .proj₀ x =  ∀x∃₁yPxy x .proj₀
  ⊢⇒⊨ choice₁ _ ∀x∃₁yPxy .proj₁ x =  ∀x∃₁yPxy x .proj₁

  -- →-intro :  P ∧ Q ⊢[ ∞ ] R →  Q ⊢[ ∞ ] P →' R
  ⊢⇒⊨ (→-intro {Q = Q} P∧Q⊢R) _ Qa a⊑b ✓b Pb =
    ⊢⇒⊨ P∧Q⊢R ✓b $ binary Pb $ ⸨ Q ⸩ .monoᵒ a⊑b Qa

  -- →-elim :  Q ⊢[ ∞ ] P →' R →  P ∧ Q ⊢[ ∞ ] R
  ⊢⇒⊨ (→-elim Q⊢P→R) ✓a P∧Qa =  ⊢⇒⊨ Q⊢P→R ✓a (P∧Qa 1₂) ⊑-refl ✓a (P∧Qa 0₂)

  -- ⊤∗-elim :  ⊤' ∗ P ⊢[ ∞ ] P
  ⊢⇒⊨ (⊤∗-elim {P}) _ (_ , _ , b∙c⊑a , _ , Pc) =
    ⸨ P ⸩ .monoᵒ (⊑-trans ∙-incrˡ b∙c⊑a) Pc

  -- ⊤∗-intro :  P ⊢[ ∞ ] ⊤' ∗ P
  ⊢⇒⊨ ⊤∗-intro _ Pa =  ε , _ , ≈⇒⊑ ∙-unitˡ , absurd , Pa

  -- ∗-comm :  P ∗ Q ⊢[ ∞ ] Q ∗ P
  ⊢⇒⊨ ∗-comm _ (b , c , b∙c⊑a , Pb , Qc) =
    c , b , ⊑-respˡ ∙-comm b∙c⊑a , Qc , Pb

  -- ∗-assocˡ :  (P ∗ Q) ∗ R ⊢[ ∞ ] P ∗ (Q ∗ R)
  ⊢⇒⊨ ∗-assocˡ _ (e , d , e∙d⊑a , (b , c , b∙c⊑e , Pb , Qc) , Rd) =
    b , c ∙ d , ⊑-respˡ ∙-assocˡ (⊑-trans (∙-monoˡ b∙c⊑e) e∙d⊑a) ,
    Pb , c , d , ⊑-refl , Qc , Rd

  -- ∗-monoˡ :  P ⊢[ ∞ ] Q →  P ∗ R ⊢[ ∞ ] Q ∗ R
  ⊢⇒⊨ (∗-monoˡ P⊢Q) ✓a (b , c , b∙c⊑a , Pb , Rc) =
    b , c , b∙c⊑a , ⊢⇒⊨ P⊢Q (✓-mono (⊑-trans ∙-incrʳ b∙c⊑a) ✓a) Pb , Rc

  -- -∗-intro :  P ∗ Q ⊢[ ∞ ] R →  Q ⊢[ ∞ ] P -∗ R
  ⊢⇒⊨ (-∗-intro {Q = Q} P∗Q⊢R) _ Qa a⊑b ✓c∙b Pc =  ⊢⇒⊨ P∗Q⊢R ✓c∙b $
    _ , _ , ⊑-refl , Pc , ⸨ Q ⸩ .monoᵒ a⊑b Qa

  -- -∗-elim :  Q ⊢[ ∞ ] P -∗ R →  P ∗ Q ⊢[ ∞ ] R
  ⊢⇒⊨ (-∗-elim {R = R} Q⊢P-∗R) ✓a (b , c , b∙c⊑a , Pb , Qc) =
    ⸨ R ⸩ .monoᵒ b∙c⊑a $ ⊢⇒⊨ Q⊢P-∗R (✓-mono (⊑-trans ∙-incrˡ b∙c⊑a) ✓a)
      Qc ⊑-refl (✓-mono b∙c⊑a ✓a) Pb

  -- |=>-mono :  P ⊢[ ∞ ] Q →  |=> P ⊢[ ∞ ] |=> Q
  ⊢⇒⊨ (|=>-mono P⊢Q) _ |=>Pa c ✓c∙a  with |=>Pa c ✓c∙a
  ... | b , ✓c∙b , Pb =  b , ✓c∙b , ⊢⇒⊨ P⊢Q (✓-mono ∙-incrˡ ✓c∙b) Pb

  -- |=>-intro :  P ⊢[ ∞ ] |=> P
  ⊢⇒⊨ |=>-intro _ Pa c ✓c∙a =  _ , ✓c∙a , Pa

  -- |=>-join :  |=> |=> P ⊢[ ∞ ] |=> P
  ⊢⇒⊨ |=>-join _ |=>|=>Pa d ✓d∙a  with |=>|=>Pa d ✓d∙a
  ... | b , ✓d∙b , |=>Pb  with |=>Pb d ✓d∙b
  ...   | c , ✓d∙c , Pc =  c , ✓d∙c , Pc

  -- |=>-frameˡ :  P ∗ |=> Q ⊢[ ∞ ] |=> (P ∗ Q)
  ⊢⇒⊨ |=>-frameˡ _ (b , c , b∙c⊑a , Pb , |=>Qc) e ✓e∙a
    with |=>Qc (e ∙ b) $ flip ✓-mono ✓e∙a $ ⊑-respˡ ∙-assocʳ $ ∙-monoʳ b∙c⊑a
  ... | d , ✓eb∙d , Qd =
    b ∙ d , ✓-resp ∙-assocˡ ✓eb∙d , b , d , ⊑-refl , Pb , Qd

  -- |=>-∃₁-out :  |=> (∃₁ _ ∈ X , P) ⊢[ ∞ ] ∃₁ _ ∈ X , |=> P
  ⊢⇒⊨ |=>-∃₁-out ✓a |=>∃₁AP .proj₀ =
    let _ , _ , x , _ = |=>∃₁AP ε $ ✓-resp (◠˜ ∙-unitˡ) ✓a in  x
  ⊢⇒⊨ |=>-∃₁-out _ |=>∃₁AP .proj₁ c ✓c∙a =
    let b , ✓c∙b , _ , Pb = |=>∃₁AP c ✓c∙a in  b , ✓c∙b , Pb

  -- □-mono :  P ⊢[ ∞ ] Q →  □ P ⊢[ ∞ ] □ Q
  ⊢⇒⊨ (□-mono P⊢Q) ✓a P⌞a⌟ =  ⊢⇒⊨ P⊢Q (✓-mono ⌞⌟-decr ✓a) P⌞a⌟

  -- □-elim :  □ P ⊢[ ∞ ] P
  ⊢⇒⊨ (□-elim {P}) _ P⌞a⌟ =  ⸨ P ⸩ .monoᵒ ⌞⌟-decr P⌞a⌟

  -- □-dup :  □ P ⊢[ ∞ ] □ □ P
  ⊢⇒⊨ (□-dup {P}) _ P⌞a⌟ =  congᵒ ⸨ P ⸩ (◠˜ ⌞⌟-idem) P⌞a⌟

  -- □ˡ-∧⇒∗ :  □ P ∧ Q ⊢[ ∞ ] □ P ∗ Q
  ⊢⇒⊨ (□ˡ-∧⇒∗ {P}) {a} _ P⌞a⌟∧Qa =  ⌞ a ⌟ , a , ≈⇒⊑ ⌞⌟-unitˡ ,
    congᵒ ⸨ P ⸩ (◠˜ ⌞⌟-idem) (P⌞a⌟∧Qa 0₂) , P⌞a⌟∧Qa 1₂

  -- □-∀₁-in :  ∀₁˙ (□_ ∘ P˙) ⊢[ ∞ ] □ ∀₁˙ P˙
  ⊢⇒⊨ □-∀₁-in _ ∀xPx⌞a⌟ =  ∀xPx⌞a⌟

  -- □-∃₁-out :  □ ∃₁˙ P˙ ⊢[ ∞ ] ∃₁˙ (□_ ∘ P˙)
  ⊢⇒⊨ □-∃₁-out _ ∑xPx⌞a⌟ =  ∑xPx⌞a⌟

  -- Save□-□ :  Save□ P˂ ⊢[ ∞ ] □ Save□ P˂
  ⊢⇒⊨ Save□-□ _ (_ , _ , BaQ , _ , Q∧P'⊢P , Qa , line□iP'a) =
    let instance _ = BaQ in
    _ , _ , _ , _ , Q∧P'⊢P , ⸨⸩ᴮ-⇒□ Qa , Own-⌞⌟-□ lineˢ□-⌞⌟ line□iP'a

  -- Saveˣ-mono-∧ :  {{Basic R}} →
  --   R ∧ P˂ .! ⊢[< ∞ ] Q˂ .! →  R ∧ Saveˣ P˂ ⊢[ ∞ ] Saveˣ Q˂
  ⊢⇒⊨ (Saveˣ-mono-∧ R∧P⊢<Q) _ R∧SaveˣP˂a =
    let T , S , BaS , _ , S∧T⊢P , Sa , lineˢˣTa = R∧SaveˣP˂a 1₂ in
    let instance _ = BaS in
    T , _ ∧ S , it , _ , ∧⊢-chain S∧T⊢P (R∧P⊢<Q .!) ,
    ⸨⸩-⇒ᴮ (binary (R∧SaveˣP˂a 0₂) $ ⸨⸩-ᴮ⇒ Sa) , lineˢˣTa

  -- Save□-mono-∧ :  {{Basic R}} →
  --   R ∧ P˂ .! ⊢[< ∞ ] Q˂ .! →  R ∧ Save□ P˂ ⊢[ ∞ ] Save□ Q˂
  ⊢⇒⊨ (Save□-mono-∧ R∧P⊢<Q) _ R∧Save□P˂a =
    let T , S , BaS , _ , S∧T⊢P , Sa , lineˢ□Ta = R∧Save□P˂a 1₂ in
    let instance _ = BaS in
    T , _ ∧ S , it , _ , ∧⊢-chain S∧T⊢P (R∧P⊢<Q .!) ,
    ⸨⸩-⇒ᴮ (binary (R∧Save□P˂a 0₂) $ ⸨⸩-ᴮ⇒ Sa) , lineˢ□Ta
