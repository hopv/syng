--------------------------------------------------------------------------------
-- Interpreting propositions and proving semantic soundness of the sequent
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Base.Level using (Level)
module Shog.Model.Sequent (ℓ : Level) where

open import Base.Size using (Size; ∞)
open import Base.Func using (_$_; _▷_; flip; it)
open import Base.Thunk using (!)
open import Base.Few using (0₂; 1₂; binary; absurd)
open import Base.Prod using (_,_; proj₀; proj₁)
open import Shog.Logic.Prop ℓ using (Prop'; ∀˙; ∃˙; _∧_; _→'_; _∗_; _-∗_; |=>_;
  □_; saveˣ; save□; IsBasic; ∀-IsBasic; ∃-IsBasic; ∗-IsBasic; Basic; isBasic;
  ∧-Basic)
open import Shog.Logic.Judg.All ℓ using (_⊢[_]_; refl; _»_;
  ∀-intro; ∃-elim; ∀-elim; ∃-intro; choice; →-intro; →-elim;
  ⊤∗-elim; ⊤∗-intro; ∗-comm; ∗-assocˡ; ∗-monoˡ; -∗-intro; -∗-elim;
  |=>-mono; |=>-intro; |=>-join; |=>-frameˡ; |=>-∃-out;
  □-mono; □-elim; □-dup; □ˡ-∧⇒∗; □-∀-in; □-∃-out;
  saveˣ-mono; save□-mono; save□-□)
open import Shog.Logic.Core ℓ using (∧-assocˡ; ∧-monoʳ)
open import Shog.Model.RA using (RA)
open import Shog.Model.RA.Glob ℓ using (Globᴿᴬ)
open import Shog.Model.Prop Globᴿᴬ using (Propᵒ; monoᵒ; _⊨_; ∀ᵒ-syntax;
  ∃ᵒ-syntax; _→ᵒ_; _∗ᵒ_; _-∗ᵒ_; |=>ᵒ_; □ᵒ_; own-⌞⌟-□')
open RA Globᴿᴬ using (_≈_; _∙_; ε; ⌞_⌟; refl˜; sym˜; _»˜_; ⊑-refl; ≈⇒⊑; ✓-resp;
  ✓-mono; ∙-congˡ; ∙-congʳ; ∙-monoˡ; ∙-unitˡ; ∙-comm; ∙-assocˡ; ∙-assocʳ;
  ∙-incrˡ; ✓-ε; ⌞⌟-unitˡ; ⌞⌟-idem; ⌞⌟-decr; ✓-⌞⌟)
open import Shog.Model.Save.X ℓ using (saveˣᵒ)
open import Shog.Model.Save.P ℓ using (save□ᵒ; lineˢ□-⌞⌟)
open import Shog.Model.Basic ℓ using ([|_|]ᴮ[_]; [|_|]ᴮ; [||]ᴮ-⇒□)

private variable
  P Q R S T :  Prop' ∞

--------------------------------------------------------------------------------
-- [| |]: Interpreting propositions

[|_|] :  (P : Prop' ∞) →  Propᵒ
[| ∀˙ _ P˙ |] =  ∀ᵒ x , [| P˙ x |]
[| ∃˙ _ P˙ |] =  ∃ᵒ x , [| P˙ x |]
[| P →' Q |] =  [| P |] →ᵒ [| Q |]
[| P ∗ Q |] =  [| P |] ∗ᵒ [| Q |]
[| P -∗ Q |] =  [| P |] -∗ᵒ [| Q |]
[| |=> P |] =  |=>ᵒ [| P |]
[| □ P |] =  □ᵒ [| P |]
[| saveˣ P^ |] =  saveˣᵒ (P^ .!)
[| save□ P^ |] =  save□ᵒ (P^ .!)

abstract

  -- [| |]ᴮ[ ] / [| |]ᴮ agrees with [| |]

  [||]-ᴮ'⇒ :  (IsBaP : IsBasic P) →  [| P |]ᴮ[ IsBaP ] ⊨ [| P |]
  [||]-ᴮ'⇒ (∀-IsBasic IsBaP˙) ∀xPxa x =  [||]-ᴮ'⇒ (IsBaP˙ x) (∀xPxa x)
  [||]-ᴮ'⇒ (∃-IsBasic IsBaP˙) (x , Pxa) =  x , [||]-ᴮ'⇒ (IsBaP˙ x) Pxa
  [||]-ᴮ'⇒ (∗-IsBasic IsBaP IsBaQ) (b , c , _ , _ , bc≈a , Pb , Qc) =
    b , c , _ , _ , bc≈a , [||]-ᴮ'⇒ IsBaP Pb , [||]-ᴮ'⇒ IsBaQ Qc

  [||]-⇒ᴮ' :  (IsBaP : IsBasic P) →  [| P |] ⊨ [| P |]ᴮ[ IsBaP ]
  [||]-⇒ᴮ' (∀-IsBasic IsBaP˙) ∀xPxa x =  [||]-⇒ᴮ' (IsBaP˙ x) (∀xPxa x)
  [||]-⇒ᴮ' (∃-IsBasic IsBaP˙) (x , Pxa) =  x , [||]-⇒ᴮ' (IsBaP˙ x) Pxa
  [||]-⇒ᴮ' (∗-IsBasic IsBaP IsBaQ) (b , c , _ , _ , bc≈a , Pb , Qc) =
    b , c , _ , _ , bc≈a , [||]-⇒ᴮ' IsBaP Pb , [||]-⇒ᴮ' IsBaQ Qc

  [||]-ᴮ⇒ :  {{BaP : Basic P}} →  [| P |]ᴮ {{BaP}} ⊨ [| P |]
  [||]-ᴮ⇒ =  [||]-ᴮ'⇒ isBasic

  [||]-⇒ᴮ :  {{BaP : Basic P}} →  [| P |] ⊨ [| P |]ᴮ {{BaP}}
  [||]-⇒ᴮ =  [||]-⇒ᴮ' isBasic

--------------------------------------------------------------------------------
-- ⊢-sem: Semantic soundness of the sequent

private

  -- Lemma for saveˣ/□-mono
  for-token-mono :  S ∧ T ⊢[ ∞ ] P →  R ∧ P ⊢[ ∞ ] Q →  (R ∧ S) ∧ T ⊢[ ∞ ] Q
  for-token-mono S∧T⊢P R∧P⊢Q =  ∧-assocˡ » ∧-monoʳ S∧T⊢P » R∧P⊢Q

abstract

  ⊢-sem :  P ⊢[ ∞ ] Q →  [| P |] ⊨ [| Q |]

  -- refl :  P ⊢[ ∞ ] P
  ⊢-sem refl Pa =  Pa

  -- _»_ :  P ⊢[ ∞ ] Q →  Q ⊢[ ∞ ] R →  P ⊢[ ∞ ] R
  ⊢-sem (P⊢Q » Q⊢R) Pa =  Pa ▷ ⊢-sem P⊢Q ▷ ⊢-sem Q⊢R

  -- ∀-intro :  (∀ a → P ⊢[ ∞ ] Q˙ a) →  P ⊢[ ∞ ] ∀˙ _ Q˙
  ⊢-sem (∀-intro ∀xP⊢Qx) Pa x =  ⊢-sem (∀xP⊢Qx x) Pa

  -- ∃-elim :  (∀ a → P˙ a ⊢[ ∞ ] Q) →  ∃˙ _ P˙ ⊢[ ∞ ] Q
  ⊢-sem (∃-elim ∀xPx⊢Q) (x , Pxa) =  ⊢-sem (∀xPx⊢Q x) Pxa

  -- ∀-elim :  ∀˙ _ P˙ ⊢[ ∞ ] P˙ a
  ⊢-sem ∀-elim ∀Pa =  ∀Pa _

  -- ∃-intro :  P˙ a ⊢[ ∞ ] ∃˙ _ P˙
  ⊢-sem ∃-intro Px =  _ , Px

  -- choice :  ∀' a , ∃ b , P˙˙ a b ⊢[ ∞ ] ∃ f , ∀' a , P˙˙ a (f a)
  ⊢-sem choice ∀x∃yPxy =  (λ x → ∀x∃yPxy x .proj₀) , λ x → ∀x∃yPxy x .proj₁

  -- →-intro :  P ∧ Q ⊢[ ∞ ] R →  Q ⊢[ ∞ ] P →' R
  ⊢-sem (→-intro {Q = Q} P∧Q⊢R) Qa a⊑b Pb =
    ⊢-sem P∧Q⊢R $ binary Pb $ [| Q |] .monoᵒ a⊑b Qa

  -- →-elim :  Q ⊢[ ∞ ] P →' R →  P ∧ Q ⊢[ ∞ ] R
  ⊢-sem (→-elim Q⊢P→R) P∧Qa =  ⊢-sem Q⊢P→R (P∧Qa 1₂) ⊑-refl (P∧Qa 0₂)

  -- ⊤∗-elim :  ⊤' ∗ P ⊢[ ∞ ] P
  ⊢-sem (⊤∗-elim {P = P}) (b , c , _ , _ , b∙c≈a , _ , Pc) =
    [| P |] .monoᵒ (b , b∙c≈a) Pc

  -- ⊤∗-intro :  P ⊢[ ∞ ] ⊤' ∗ P
  ⊢-sem ⊤∗-intro Pa =  ε , _ , ✓-ε , _ , ∙-unitˡ , absurd , Pa

  -- ∗-comm :  P ∗ Q ⊢[ ∞ ] Q ∗ P
  ⊢-sem ∗-comm (b , c , _ , _ , b∙c≈a , Pb , Qc) =
    c , b , _ , _ , (∙-comm »˜ b∙c≈a) , Qc , Pb

  -- ∗-assocˡ :  (P ∗ Q) ∗ R ⊢[ ∞ ] P ∗ (Q ∗ R)
  ⊢-sem ∗-assocˡ {a = a} {✓a}
   (bc , d , _ , _ , bc∙d≈a , (b , c , _ , _ , b∙c≈bc , Pb , Qc) , Rd) =
    b , c ∙ d , _ , ✓-mono (b , b∙cd≈a) ✓a , b∙cd≈a , Pb , c , d , _ , _ ,
    refl˜ , Qc , Rd
   where
    b∙cd≈a :  b ∙ (c ∙ d) ≈ a
    b∙cd≈a =  ∙-assocʳ »˜ ∙-congˡ b∙c≈bc »˜ bc∙d≈a

  -- ∗-monoˡ :  P ⊢[ ∞ ] Q →  P ∗ R ⊢[ ∞ ] Q ∗ R
  ⊢-sem (∗-monoˡ P⊢Q) (b , c , _ , _ , b∙c≈a , Pb , Rc) =
    b , c , _ , _ , b∙c≈a , ⊢-sem P⊢Q Pb , Rc

  -- -∗-intro :  P ∗ Q ⊢[ ∞ ] R →  Q ⊢[ ∞ ] P -∗ R
  ⊢-sem (-∗-intro {Q = Q} P∗Q⊢R) Qa {✓c∙b = ✓c∙b} a⊑b Pb =  ⊢-sem P∗Q⊢R $
    _ , _ , _ , ✓-mono ∙-incrˡ ✓c∙b , refl˜ , Pb , [| Q |] .monoᵒ a⊑b Qa

  -- -∗-elim :  Q ⊢[ ∞ ] P -∗ R →  P ∗ Q ⊢[ ∞ ] R
  ⊢-sem (-∗-elim {R = R} Q⊢P-∗R) {✓a = ✓a} (b , c , _ , _ , b∙c≈a , Pb , Qc) =
    [| R |] .monoᵒ {✓a = ✓-resp (sym˜ b∙c≈a) ✓a} (≈⇒⊑ b∙c≈a) $
    ⊢-sem Q⊢P-∗R Qc ⊑-refl Pb

  -- |=>-mono :  P ⊢[ ∞ ] Q →  |=> P ⊢[ ∞ ] |=> Q
  ⊢-sem (|=>-mono P⊢Q) |=>Pa c ✓c∙a with |=>Pa c ✓c∙a
  ... | b , _ , ✓c∙b , Pb =  b , _ , ✓c∙b , ⊢-sem P⊢Q Pb

  -- |=>-intro :  P ⊢[ ∞ ] |=> P
  ⊢-sem |=>-intro Pa c ✓c∙a =  _ , _ , ✓c∙a , Pa

  -- |=>-join :  |=> |=> P ⊢[ ∞ ] |=> P
  ⊢-sem |=>-join |=>|=>Pa d ✓d∙a with |=>|=>Pa d ✓d∙a
  ... | b , _ , ✓d∙b , |=>Pb with  |=>Pb d ✓d∙b
  ...   | c , _ , ✓d∙c , Pc = c , _ , ✓d∙c , Pc

  -- |=>-frameˡ :  P ∗ |=> Q ⊢[ ∞ ] |=> (P ∗ Q)
  ⊢-sem |=>-frameˡ (b , c , _ , _ , b∙c≈a , Pb , |=>Qc) e ✓e∙a with
    |=>Qc (e ∙ b) $ flip ✓-resp ✓e∙a $ ∙-congʳ (sym˜ b∙c≈a) »˜ ∙-assocʳ
  ... | d , _ , ✓eb∙d , Qd =  b ∙ d , (flip ✓-mono ✓eb∙d $ ∙-monoˡ ∙-incrˡ) ,
    (✓-resp ∙-assocˡ ✓eb∙d) , b , d , _ , _ , refl˜ , Pb , Qd

  -- |=>-∃-out :  |=> (∃ _ ∈ A , P) ⊢[ ∞ ] ∃ _ ∈ A , |=> P
  ⊢-sem |=>-∃-out {✓a = ✓a} |=>∃AP =  λ where
    .proj₀ →  |=>∃AP ε (✓-resp (sym˜ ∙-unitˡ) ✓a) ▷ λ (_ , _ , _ , x , _) → x
    .proj₁ c ✓c∙a →  |=>∃AP c ✓c∙a ▷ λ (b , _ , ✓c∙b , _ , Pb) →
      b , _ , ✓c∙b , Pb

  -- □-mono :  P ⊢[ ∞ ] Q →  □ P ⊢[ ∞ ] □ Q
  ⊢-sem (□-mono P⊢Q) P⌞a⌟ =  ⊢-sem P⊢Q P⌞a⌟

  -- □-elim :  □ P ⊢[ ∞ ] P
  ⊢-sem (□-elim {P = P}) P⌞a⌟ =  [| P |] .monoᵒ ⌞⌟-decr P⌞a⌟

  -- □-dup :  □ P ⊢[ ∞ ] □ □ P
  ⊢-sem (□-dup {P = P}) P⌞a⌟ =  [| P |] .monoᵒ (≈⇒⊑ $ sym˜ ⌞⌟-idem) P⌞a⌟

  -- □ˡ-∧⇒∗ :  □ P ∧ Q ⊢[ ∞ ] □ P ∗ Q
  ⊢-sem (□ˡ-∧⇒∗ {P = P}) {a = a} {✓a} P⌞a⌟∧Qa =  ⌞ a ⌟ , a , ✓-⌞⌟ ✓a , _ ,
    ⌞⌟-unitˡ , [| P |] .monoᵒ (≈⇒⊑ $ sym˜ ⌞⌟-idem) (P⌞a⌟∧Qa 0₂) , P⌞a⌟∧Qa 1₂

  -- □-∀-in :  ∀˙ _ (□_ ∘ P˙) ⊢[ ∞ ] □ ∀˙ _ P˙
  ⊢-sem □-∀-in ∀xPx⌞a⌟ =  ∀xPx⌞a⌟

  -- □-∃-out :  □ ∃˙ _ P˙ ⊢[ ∞ ] ∃˙ _ (□_ ∘ P˙)
  ⊢-sem □-∃-out ΣxPx⌞a⌟ =  ΣxPx⌞a⌟

  -- saveˣ-mono :  {{Basic R}} →
  --   R ∧ P^ .! ⊢[< ∞ ] Q^ .! →  R ∧ saveˣ P^ ⊢[ ∞ ] saveˣ Q^
  ⊢-sem (saveˣ-mono {R = R} R∧P⊢<Q) R∧saveˣP^a =
    (R∧saveˣP^a 0₂ , R∧saveˣP^a 1₂) ▷
    λ (Ra , T , S , BaS , _ , S∧T⊢P , Sa , lineˢˣTa) →
    let instance BaS :  Basic S
                 BaS =  BaS in
    T , R ∧ S , it , _ , for-token-mono S∧T⊢P (R∧P⊢<Q .!) ,
    [||]-⇒ᴮ (binary Ra $ [||]-ᴮ⇒ Sa) , lineˢˣTa

  -- save□-mono :  {{Basic R}} →
  --   R ∧ P^ .! ⊢[< ∞ ] Q^ .! →  R ∧ save□ P^ ⊢[ ∞ ] save□ Q^
  ⊢-sem (save□-mono {R = R} R∧P⊢<Q) R∧save□P^a =
    (R∧save□P^a 0₂ , R∧save□P^a 1₂) ▷
    λ (Ra , T , S , BaS , _ , S∧T⊢P , Sa , lineˢ□Ta) →
    let instance BaS :  Basic S
                 BaS =  BaS in
    T , R ∧ S , it , _ , for-token-mono S∧T⊢P (R∧P⊢<Q .!) ,
    [||]-⇒ᴮ (binary Ra $ [||]-ᴮ⇒ Sa) , lineˢ□Ta

  -- save□-□ :  save□ P^ ⊢[ ∞ ] □ save□ P^
  ⊢-sem save□-□ {✓a = ✓a} (_ , _ , BaB , i , B∗P'⊢P , Ba , line□iP'a) =
    _ , _ , _ , _ , B∗P'⊢P , [||]ᴮ-⇒□ {{BaB}} Ba ,
    own-⌞⌟-□' lineˢ□-⌞⌟ {✓a = ✓a} line□iP'a
