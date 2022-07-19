--------------------------------------------------------------------------------
-- Prove semantic soundness of the pure sequent
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Model.Pure (ℓ : Level) where

open import Base.Size using (Size; ∞)
open import Base.Func using (_$_; _▷_; flip; it)
open import Base.Thunk using (!)
open import Base.Few using (0₂; 1₂; binary; absurd)
open import Base.Prod using (_,_; proj₀; proj₁)
open import Shog.Logic.Prop ℓ using (Prop'; ∀˙; ∃˙; _∧_; _→'_; _∗_; _-∗_; |=>_;
  □_; Saveˣ; Save□; IsBasic; ∀-IsBasic; ∃-IsBasic; ∗-IsBasic; □-IsBasic; Basic;
  isBasic; ∧-Basic)
open import Shog.Logic.Core ℓ using (_⊢[_]_; ⊢-refl; _»_;
  ∀-intro; ∃-elim; ∀-elim; ∃-intro; choice; →-intro; →-elim;
  ⊤∗-elim; ⊤∗-intro; ∗-comm; ∗-assocˡ; ∗-monoˡ; -∗-intro; -∗-elim;
  |=>-mono; |=>-intro; |=>-join; |=>-frameˡ; |=>-∃-out;
  □-mono; □-elim; □-dup; □ˡ-∧⇒∗; □-∀-in; □-∃-out; ∧-assocˡ; ∧-monoʳ)
open import Shog.Logic.Save ℓ using (Save□-□; Saveˣ-mono-∧; Save□-mono-∧)
open import Shog.Model.RA using (RA)
open import Shog.Model.RA.Glob ℓ using (GlobRA)
open import Shog.Model.Prop GlobRA using (Propᵒ; monoᵒ; renewᵒ; congᵒ; congᵒ';
  _⊨_; ∀ᵒ-syntax; ∃ᵒ-syntax; _→ᵒ_; _∗ᵒ_; _-∗ᵒ_; |=>ᵒ_; □ᵒ_; Own-⌞⌟-□')
open RA GlobRA using (_≈_; _∙_; ε; ⌞_⌟; refl˜; ◠˜_; _◇˜_; ≈⇒⊑; ⊑-refl; ⊑-trans;
  ⊑-respˡ; ✓-resp; ✓-mono; ∙-congˡ; ∙-congʳ; ∙-monoˡ; ∙-monoʳ; ∙-unitˡ; ∙-comm;
  ∙-assocˡ; ∙-assocʳ; ∙-incrˡ; ✓-ε; ⌞⌟-unitˡ; ⌞⌟-idem; ⌞⌟-decr; ✓-⌞⌟)
open import Shog.Model.Save.X ℓ using (Saveˣᵒ)
open import Shog.Model.Save.P ℓ using (Save□ᵒ; lineˢ□-⌞⌟)
open import Shog.Model.Basic ℓ using ([|_|]ᴮ[_]; [|_|]ᴮ; [||]ᴮ-⇒□)

private variable
  P Q R S T :  Prop' ∞

--------------------------------------------------------------------------------
-- [| |]: Interpreting propositions

[|_|] :  (P : Prop' ∞) →  Propᵒ
[| ∀˙ P˙ |] =  ∀ᵒ x , [| P˙ x |]
[| ∃˙ P˙ |] =  ∃ᵒ x , [| P˙ x |]
[| P →' Q |] =  [| P |] →ᵒ [| Q |]
[| P ∗ Q |] =  [| P |] ∗ᵒ [| Q |]
[| P -∗ Q |] =  [| P |] -∗ᵒ [| Q |]
[| |=> P |] =  |=>ᵒ [| P |]
[| □ P |] =  □ᵒ [| P |]
[| Saveˣ P˂ |] =  Saveˣᵒ (P˂ .!)
[| Save□ P˂ |] =  Save□ᵒ (P˂ .!)

abstract

  -- [| |]ᴮ[ ] / [| |]ᴮ agrees with [| |]

  [||]-ᴮ'⇒ :  (IsBaP : IsBasic P) →  [| P |]ᴮ[ IsBaP ] ⊨ [| P |]
  [||]-ᴮ'⇒ (∀-IsBasic IsBaP˙) ∀xPxa x =  [||]-ᴮ'⇒ (IsBaP˙ x) (∀xPxa x)
  [||]-ᴮ'⇒ (∃-IsBasic IsBaP˙) (x , Pxa) =  x , [||]-ᴮ'⇒ (IsBaP˙ x) Pxa
  [||]-ᴮ'⇒ (∗-IsBasic {P} {Q} IsBaP IsBaQ) (b , c , bc≈a , Pb , Qc) =
    b , c , bc≈a , [||]-ᴮ'⇒ IsBaP Pb , [||]-ᴮ'⇒ IsBaQ Qc
  [||]-ᴮ'⇒ (□-IsBasic IsBaP) =  [||]-ᴮ'⇒ IsBaP

  [||]-⇒ᴮ' :  (IsBaP : IsBasic P) →  [| P |] ⊨ [| P |]ᴮ[ IsBaP ]
  [||]-⇒ᴮ' (∀-IsBasic IsBaP˙) ∀xPxa x =  [||]-⇒ᴮ' (IsBaP˙ x) (∀xPxa x)
  [||]-⇒ᴮ' (∃-IsBasic IsBaP˙) (x , Pxa) =  x , [||]-⇒ᴮ' (IsBaP˙ x) Pxa
  [||]-⇒ᴮ' (∗-IsBasic {P} {Q} IsBaP IsBaQ) (b , c , bc≈a , Pb , Qc) =
    b , c , bc≈a , [||]-⇒ᴮ' IsBaP Pb , [||]-⇒ᴮ' IsBaQ Qc
  [||]-⇒ᴮ' (□-IsBasic IsBaP) =  [||]-⇒ᴮ' IsBaP

  [||]-ᴮ⇒ :  {{_ : Basic P}} →  [| P |]ᴮ ⊨ [| P |]
  [||]-ᴮ⇒ =  [||]-ᴮ'⇒ isBasic

  [||]-⇒ᴮ :  {{_ : Basic P}} →  [| P |] ⊨ [| P |]ᴮ
  [||]-⇒ᴮ =  [||]-⇒ᴮ' isBasic

--------------------------------------------------------------------------------
-- ⊢⇒⊨: Semantic soundness of the pure sequent

abstract

  private

    ∧⊢-chain :  S ∧ T ⊢[ ∞ ] P →  R ∧ P ⊢[ ∞ ] Q →  (R ∧ S) ∧ T ⊢[ ∞ ] Q
    ∧⊢-chain S∧T⊢P R∧P⊢Q =  ∧-assocˡ » ∧-monoʳ S∧T⊢P » R∧P⊢Q

  ⊢⇒⊨ :  P ⊢[ ∞ ] Q →  [| P |] ⊨ [| Q |]

  -- ⊢-refl :  P ⊢[ ∞ ] P
  ⊢⇒⊨ ⊢-refl Pa =  Pa

  -- _»_ :  P ⊢[ ∞ ] Q →  Q ⊢[ ∞ ] R →  P ⊢[ ∞ ] R
  ⊢⇒⊨ (P⊢Q » Q⊢R) Pa =  Pa ▷ ⊢⇒⊨ P⊢Q ▷ ⊢⇒⊨ Q⊢R

  -- ∀-intro :  (∀ a → P ⊢[ ∞ ] Q˙ a) →  P ⊢[ ∞ ] ∀˙ Q˙
  ⊢⇒⊨ (∀-intro ∀xP⊢Qx) Pa x =  ⊢⇒⊨ (∀xP⊢Qx x) Pa

  -- ∃-elim :  (∀ a → P˙ a ⊢[ ∞ ] Q) →  ∃˙ P˙ ⊢[ ∞ ] Q
  ⊢⇒⊨ (∃-elim ∀xPx⊢Q) (x , Pxa) =  ⊢⇒⊨ (∀xPx⊢Q x) Pxa

  -- ∀-elim :  ∀˙ P˙ ⊢[ ∞ ] P˙ a
  ⊢⇒⊨ ∀-elim ∀Pa =  ∀Pa _

  -- ∃-intro :  P˙ a ⊢[ ∞ ] ∃˙ P˙
  ⊢⇒⊨ ∃-intro Px =  _ , Px

  -- choice :  ∀' a , ∃ b , P˙˙ a b ⊢[ ∞ ] ∃ f , ∀' a , P˙˙ a (f a)
  -- It can be proved axiom-free thanks to the logic's predicativity
  ⊢⇒⊨ choice ∀x∃yPxy =  (λ x → ∀x∃yPxy x .proj₀) , λ x → ∀x∃yPxy x .proj₁

  -- →-intro :  P ∧ Q ⊢[ ∞ ] R →  Q ⊢[ ∞ ] P →' R
  ⊢⇒⊨ (→-intro {Q = Q} P∧Q⊢R) Qa a⊑b Pb =
    ⊢⇒⊨ P∧Q⊢R $ binary Pb $ [| Q |] .monoᵒ a⊑b Qa

  -- →-elim :  Q ⊢[ ∞ ] P →' R →  P ∧ Q ⊢[ ∞ ] R
  ⊢⇒⊨ (→-elim Q⊢P→R) P∧Qa =  ⊢⇒⊨ Q⊢P→R (P∧Qa 1₂) ⊑-refl (P∧Qa 0₂)

  -- ⊤∗-elim :  ⊤' ∗ P ⊢[ ∞ ] P
  ⊢⇒⊨ (⊤∗-elim {P}) (b , c , b∙c⊑a , _ , Pc) =
    [| P |] .monoᵒ (⊑-trans ∙-incrˡ b∙c⊑a) Pc

  -- ⊤∗-intro :  P ⊢[ ∞ ] ⊤' ∗ P
  ⊢⇒⊨ (⊤∗-intro {P}) Pa =  ε , _ , ≈⇒⊑ ∙-unitˡ , absurd , renewᵒ [| P |] Pa

  -- ∗-comm :  P ∗ Q ⊢[ ∞ ] Q ∗ P
  ⊢⇒⊨ (∗-comm {P} {Q}) (b , c , b∙c⊑a , Pb , Qc) =
    c , b , ⊑-respˡ ∙-comm b∙c⊑a , renewᵒ [| Q |] Qc , renewᵒ [| P |] Pb

  -- ∗-assocˡ :  (P ∗ Q) ∗ R ⊢[ ∞ ] P ∗ (Q ∗ R)
  ⊢⇒⊨ (∗-assocˡ {P} {Q} {R})
   (e , d , e∙d⊑a , (b , c , b∙c⊑e , Pb , Qc) , Rd) =
    b , c ∙ d , ⊑-respˡ ∙-assocˡ (⊑-trans (∙-monoˡ b∙c⊑e) e∙d⊑a) ,
    renewᵒ [| P |] Pb , c , d , ⊑-refl , renewᵒ [| Q |] Qc , renewᵒ [| R |] Rd

  -- ∗-monoˡ :  P ⊢[ ∞ ] Q →  P ∗ R ⊢[ ∞ ] Q ∗ R
  ⊢⇒⊨ (∗-monoˡ {Q = Q} {R} P⊢Q) (b , c , b∙c≈a , Pb , Rc) =
    b , c , b∙c≈a , ⊢⇒⊨ P⊢Q Pb , Rc

  -- -∗-intro :  P ∗ Q ⊢[ ∞ ] R →  Q ⊢[ ∞ ] P -∗ R
  ⊢⇒⊨ (-∗-intro {P} {Q} P∗Q⊢R) Qa a⊑b Pb =  ⊢⇒⊨ P∗Q⊢R $
    _ , _ , ⊑-refl , renewᵒ [| P |] Pb , [| Q |] .monoᵒ a⊑b Qa

  -- -∗-elim :  Q ⊢[ ∞ ] P -∗ R →  P ∗ Q ⊢[ ∞ ] R
  ⊢⇒⊨ (-∗-elim {R = R} Q⊢P-∗R) {✓a = ✓a} (b , c , b∙c⊑a , Pb , Qc) =
    [| R |] .monoᵒ {✓a = ✓-mono b∙c⊑a ✓a} b∙c⊑a $ ⊢⇒⊨ Q⊢P-∗R Qc ⊑-refl Pb

  -- |=>-mono :  P ⊢[ ∞ ] Q →  |=> P ⊢[ ∞ ] |=> Q
  ⊢⇒⊨ (|=>-mono {Q = Q} P⊢Q) |=>Pa c ✓c∙a with |=>Pa c ✓c∙a
  ... | b , ✓c∙b , Pb =  b , ✓c∙b , ⊢⇒⊨ P⊢Q Pb

  -- |=>-intro :  P ⊢[ ∞ ] |=> P
  ⊢⇒⊨ (|=>-intro {P}) Pa c ✓c∙a =  _ , ✓c∙a , renewᵒ [| P |] Pa

  -- |=>-join :  |=> |=> P ⊢[ ∞ ] |=> P
  ⊢⇒⊨ (|=>-join {P}) |=>|=>Pa d ✓d∙a with |=>|=>Pa d ✓d∙a
  ... | b , ✓d∙b , |=>Pb with  |=>Pb d ✓d∙b
  ...   | c , ✓d∙c , Pc =  c , ✓d∙c , Pc

  -- |=>-frameˡ :  P ∗ |=> Q ⊢[ ∞ ] |=> (P ∗ Q)
  ⊢⇒⊨ (|=>-frameˡ {P} {Q}) (b , c , b∙c⊑a , Pb , |=>Qc) e ✓e∙a with
    |=>Qc (e ∙ b) $ flip ✓-mono ✓e∙a $ ⊑-respˡ ∙-assocʳ $ ∙-monoʳ b∙c⊑a
  ... | d , ✓eb∙d , Qd =  b ∙ d , ✓-resp ∙-assocˡ ✓eb∙d , b , d , ⊑-refl ,
    renewᵒ [| P |] Pb , renewᵒ [| Q |] Qd

  -- |=>-∃-out :  |=> (∃ _ ∈ A , P) ⊢[ ∞ ] ∃ _ ∈ A , |=> P
  ⊢⇒⊨ (|=>-∃-out {P = P}) {✓a = ✓a} |=>∃AP =  λ where
    .proj₀ →  let (_ , _ , x , _) = |=>∃AP ε $ ✓-resp (◠˜ ∙-unitˡ) ✓a in  x
    .proj₁ c ✓c∙a →  let (b , ✓c∙b , _ , Pb) = |=>∃AP c ✓c∙a in  b , ✓c∙b , Pb

  -- □-mono :  P ⊢[ ∞ ] Q →  □ P ⊢[ ∞ ] □ Q
  ⊢⇒⊨ (□-mono P⊢Q) P⌞a⌟ =  ⊢⇒⊨ P⊢Q P⌞a⌟

  -- □-elim :  □ P ⊢[ ∞ ] P
  ⊢⇒⊨ (□-elim {P = P}) P⌞a⌟ =  [| P |] .monoᵒ ⌞⌟-decr P⌞a⌟

  -- □-dup :  □ P ⊢[ ∞ ] □ □ P
  ⊢⇒⊨ (□-dup {P = P}) P⌞a⌟ =  congᵒ [| P |] (◠˜ ⌞⌟-idem) P⌞a⌟

  -- □ˡ-∧⇒∗ :  □ P ∧ Q ⊢[ ∞ ] □ P ∗ Q
  ⊢⇒⊨ (□ˡ-∧⇒∗ {P} {Q}) {a = a} P⌞a⌟∧Qa =  ⌞ a ⌟ , a , ≈⇒⊑ ⌞⌟-unitˡ ,
    congᵒ [| P |] (◠˜ ⌞⌟-idem) (P⌞a⌟∧Qa 0₂) ,
    renewᵒ [| Q |] (P⌞a⌟∧Qa 1₂)

  -- □-∀-in :  ∀˙ (□_ ∘ P˙) ⊢[ ∞ ] □ ∀˙ P˙
  ⊢⇒⊨ □-∀-in ∀xPx⌞a⌟ =  ∀xPx⌞a⌟

  -- □-∃-out :  □ ∃˙ P˙ ⊢[ ∞ ] ∃˙ (□_ ∘ P˙)
  ⊢⇒⊨ □-∃-out ∑xPx⌞a⌟ =  ∑xPx⌞a⌟

  -- Save□-□ :  Save□ P˂ ⊢[ ∞ ] □ Save□ P˂
  ⊢⇒⊨ Save□-□ {✓a = ✓a} (_ , _ , BaQ , i , Q∧P'⊢P , Qa , line□iP'a) =
    let instance _ = BaQ in
    _ , _ , _ , _ , Q∧P'⊢P , [||]ᴮ-⇒□ Qa ,
    Own-⌞⌟-□' lineˢ□-⌞⌟ {✓a = ✓a} line□iP'a

  -- Saveˣ-mono-∧ :  {{Basic R}} →
  --   R ∧ P˂ .! ⊢[< ∞ ] Q˂ .! →  R ∧ Saveˣ P˂ ⊢[ ∞ ] Saveˣ Q˂
  ⊢⇒⊨ (Saveˣ-mono-∧ {R = R} R∧P⊢<Q) R∧SaveˣP˂a =
    (R∧SaveˣP˂a 0₂ , R∧SaveˣP˂a 1₂) ▷
    λ (Ra , T , S , BaS , _ , S∧T⊢P , Sa , lineˢˣTa) →
    let instance _ = BaS in
    T , R ∧ S , it , _ , ∧⊢-chain S∧T⊢P (R∧P⊢<Q .!) ,
    [||]-⇒ᴮ (binary Ra $ [||]-ᴮ⇒ Sa) , lineˢˣTa

  -- Save□-mono-∧ :  {{Basic R}} →
  --   R ∧ P˂ .! ⊢[< ∞ ] Q˂ .! →  R ∧ Save□ P˂ ⊢[ ∞ ] Save□ Q˂
  ⊢⇒⊨ (Save□-mono-∧ {R = R} R∧P⊢<Q) R∧Save□P˂a =
    (R∧Save□P˂a 0₂ , R∧Save□P˂a 1₂) ▷
    λ (Ra , T , S , BaS , _ , S∧T⊢P , Sa , lineˢ□Ta) →
    let instance _ = BaS in
    T , R ∧ S , it , _ , ∧⊢-chain S∧T⊢P (R∧P⊢<Q .!) ,
    [||]-⇒ᴮ (binary Ra $ [||]-ᴮ⇒ Sa) , lineˢ□Ta
