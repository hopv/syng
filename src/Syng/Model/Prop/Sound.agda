--------------------------------------------------------------------------------
-- Prove the semantic soundness and adequacy of the pure sequent
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syng.Model.Prop.Sound where

open import Base.Func using (_$_; _›_; id)
open import Base.Few using (0₂; 1₂; binary; absurd)
open import Base.Size using (𝕊; ∞; !)
open import Base.Prod using (_,_; π₀; π₁; ∑-case)
open import Syng.Lang.Expr using (✓ᴴ-∅)
open import Syng.Logic.Prop using (Name; SProp∞; ⊤'; ⌜_⌝; [⊤]ᴺ; [^_]ᴺ)
open import Syng.Logic.Core using (_⊢[_]_; ⊢-refl; _»_; ∀-intro; ∃-elim; ∀-elim;
  ∃-intro; choice; ⊤-intro; →-introˡ; →-elimˡ; ∗-monoˡ; ⊤∗-elim; ⊤∗-intro;
  ∗-comm; ∗-assocʳ; -∗-introˡ; -∗-elimˡ; ⤇-mono; ⤇-intro; ⤇-join; ⤇-eatˡ;
  ⤇-⌜⌝∧-out; □-mono; □-elim; □-dup; □ˡ-∧⇒∗; □-∀-in; □-∃-out)
open import Syng.Logic.Names using ([]ᴺ-resp; []ᴺ-merge; []ᴺ-split; []ᴺ-✔;
  ᴺ⇒[^])
open import Syng.Logic.Heap using (↦⟨⟩-resp; ↦⟨⟩-merge; ↦⟨⟩-split; ↦⟨⟩-≤1;
  ↦⟨⟩-agree)
open import Syng.Logic.Ind using (○-mono; ○-eatˡ; ⊸⇛-≤; ⊸⇛-eatˡ⁻ˡᵘ; ⊸⇛-monoʳᵘ;
  ⊸⇛-eatˡ⁻ʳ; ⊸⇛-frameʳ; ○⇒⊸⇛;  ⊸ᵃ⟨⟩-≤; ⊸ᵃ⟨⟩-eatˡ⁻ˡᵘ; ⊸ᵃ⟨⟩-monoʳᵘ; ⊸ᵃ⟨⟩-eatˡ⁻ʳ;
  ⊸ᵃ⟨⟩-frameʳ; ○⇒⊸ᵃ⟨⟩; ⊸⟨⟩ᵀ⇒⊸⟨⟩ᴾ; ⊸⟨⟩ᵀ-≤; ⊸⟨⟩-eatˡ⁻ˡᵘᴺ; ⊸⟨⟩-monoʳᵘᴺ; ⊸⟨⟩-eatˡ⁻ʳ;
  ⊸⟨⟩-frameʳ; ○⇒⊸⟨⟩; ⊸⟨⟩∞⇒⊸⟨⟩ᴾ; ⊸⟨⟩∞-≤; ⊸⟨⟩∞-eatˡ⁻ᵘᴺ; ○⇒⊸⟨⟩∞)
open import Syng.Logic.Inv using (&ⁱ-⇒□; &ⁱ-resp-□∗; ⅋ⁱ-mono; ⅋ⁱ-eatˡ)
open import Syng.Logic.Lft using ([]ᴸ⟨⟩-resp; []ᴸ⟨⟩-merge; []ᴸ⟨⟩-split;
  []ᴸ⟨⟩-≤1; †ᴸ-⇒□; []ᴸ⟨⟩-†ᴸ-no; []ᴸ-new; []ᴸ-kill)
open import Syng.Logic.Bor using (&ᵐ-resp-□∗; ⅋ᵐ-respᴿ; ⅋ᵐ-monoᴾ; ⅋ᵐ-eatˡ;
  ⟨†⟩-mono; ⟨†⟩-eatˡ)
open import Syng.Logic.Ub using (≤ᵁᵇ-mono; ≤ᵁᵇ-⇒□; ≤ᵁᵇ-#ᵁᵇ; #ᵁᵇ-new; #ᵁᵇ-upd)
open import Syng.Model.ERA.Glob using (∅ᴵⁿᴳ-✓ᴺ)
open import Syng.Model.Prop.Base using (_⊨✓_; →ᵒ-introˡ; →ᵒ-elimˡ; ∗ᵒ-mono✓ˡ;
  ∗ᵒ-monoˡ; ?∗ᵒ-intro; ∗ᵒ-elimʳ; ∗ᵒ-comm; ∗ᵒ-assocʳ; -∗ᵒ-introˡ; -∗ᵒ-elimˡ;
  ⤇ᵒ-mono✓; ⤇ᵒ-intro; ⤇ᵒ-join; ⤇ᵒ-eatˡ; ⤇ᵒ-⌜⌝ᵒ×-out; □ᵒ-mono✓; □ᵒ-elim; □ᵒ-dup;
  □ᵒˡ-×ᵒ⇒∗ᵒ; ◎-just)
open import Syng.Model.Prop.Heap using (↦⟨⟩ᵒ-resp; ↦⟨⟩ᵒ-merge; ↦⟨⟩ᵒ-split;
  ↦⟨⟩ᵒ-≤1; ↦⟨⟩ᵒ-agree)
open import Syng.Model.Prop.Names using ([]ᴺᵒ-resp; []ᴺᵒ-merge; []ᴺᵒ-split;
  []ᴺᵒ-✔)
open import Syng.Model.Prop.Lft using ([]ᴸ⟨⟩ᵒ-resp; []ᴸ⟨⟩ᵒ-merge; []ᴸ⟨⟩ᵒ-split;
  []ᴸ⟨⟩ᵒ-≤1; †ᴸᵒ-⇒□ᵒ; []ᴸ⟨⟩ᵒ-†ᴸᵒ-no; []ᴸᵒ-new; []ᴸᵒ-kill)
open import Syng.Model.Prop.Ind using (○ᵒ-mono; ○ᵒ-eatˡ; ⊸⇛ᵒ-≤; ⊸⇛ᵒ-eatˡ⁻ˡᵘ;
  ⊸⇛ᵒ-monoʳᵘ; ⊸⇛ᵒ-eatˡ⁻ʳ; ⊸⇛ᵒ-frameʳ; ○ᵒ⇒⊸⇛ᵒ; ⊸ᵃ⟨⟩ᵒ-≤; ⊸ᵃ⟨⟩ᵒ-eatˡ⁻ˡᵘ;
  ⊸ᵃ⟨⟩ᵒ-monoʳᵘ; ⊸ᵃ⟨⟩ᵒ-eatˡ⁻ʳ; ⊸ᵃ⟨⟩ᵒ-frameʳ; ○ᵒ⇒⊸ᵃ⟨⟩ᵒ; ⊸⟨⟩ᵀᵒ⇒⊸⟨⟩ᴾᵒ; ⊸⟨⟩ᵀᵒ-≤;
  ⊸⟨⟩ᵒ-eatˡ⁻ˡᵘᴺ; ⊸⟨⟩ᵒ-monoʳᵘᴺ; ⊸⟨⟩ᵒ-eatˡ⁻ʳ; ⊸⟨⟩ᵒ-frameʳ; ○ᵒ⇒⊸⟨⟩ᵒ; ⊸⟨⟩∞ᵒ⇒⊸⟨⟩ᴾᵒ;
  ⊸⟨⟩∞ᵒ-≤; ⊸⟨⟩∞ᵒ-eatˡ⁻ᵘᴺ; ○ᵒ⇒⊸⟨⟩∞ᵒ)
open import Syng.Model.Prop.Inv using (&ⁱᵒ-⇒□ᵒ; &ⁱᵒ-resp-□ᵒ∗ᵒ; ⅋ⁱᵒ-mono;
  ⅋ⁱᵒ-eatˡ)
open import Syng.Model.Prop.Bor using (&ᵐᵒ-resp-□ᵒ∗ᵒ; ⅋ᵐᵒ-respᴿ; ⅋ᵐᵒ-monoᴾ;
  ⅋ᵐᵒ-eatˡ; ⟨†⟩ᵒ-mono; ⟨†⟩ᵒ-eatˡ)
open import Syng.Model.Prop.Ub using (≤ᵁᵇᵒ-mono; ≤ᵁᵇᵒ-⇒□ᵒ; ≤ᵁᵇᵒ-#ᵁᵇᵒ; #ᵁᵇᵒ-new;
  #ᵁᵇᵒ-upd)
open import Syng.Model.Prop.Interp using (⸨_⸩; ⸨⸩-Mono; ⸨⸩-⇒ᴮ)

private variable
  P Q R S T :  SProp∞
  X :  Set₀
  nm :  Name

--------------------------------------------------------------------------------
-- ⊢-sem :  Semantic soundness of the pure sequent

abstract

  ⊢-sem :  P ⊢[ ∞ ] Q →  ⸨ P ⸩ ⊨✓ ⸨ Q ⸩

  -- ⊢-refl :  P ⊢[ ∞ ] P

  ⊢-sem ⊢-refl _ =  id

  -- _»_ :  P ⊢[ ∞ ] Q →  Q ⊢[ ∞ ] R →  P ⊢[ ∞ ] R

  ⊢-sem (P⊢Q » Q⊢R) ✓a =  ⊢-sem P⊢Q ✓a › ⊢-sem Q⊢R ✓a

  -- ∀-intro :  (∀' x → P ⊢[ ∞ ] Q˙ x) →  P ⊢[ ∞ ] ∀˙ Q˙

  ⊢-sem (∀-intro ∀xP⊢Qx) ✓a Pa x =  ⊢-sem (∀xP⊢Qx x) ✓a Pa

  -- ∃-elim :  (∀' x → P˙ x ⊢[ ∞ ] Q) →  ∃˙ P˙ ⊢[ ∞ ] Q

  ⊢-sem (∃-elim ∀xPx⊢Q) ✓a =  ∑-case λ x → ⊢-sem (∀xPx⊢Q x) ✓a

  -- ∀-elim :  ∀ x →  ∀˙ P˙ ⊢[ ∞ ] P˙ x

  ⊢-sem (∀-elim x) _ ∀Pa =  ∀Pa x

  -- ∃-intro :  ∀ x →  P˙ x ⊢[ ∞ ] ∃˙ P˙

  ⊢-sem (∃-intro x) _ Px =  x , Px

  -- choice :  ∀' x , ∃ y , P˙˙ x y ⊢[ ∞ ] ∃ y˙ , ∀' x , P˙˙ x (y˙ x)

  -- It can be proved axiom-free thanks to the logic's predicativity

  ⊢-sem choice _ ∀x∃yPxy .π₀ x =  ∀x∃yPxy x .π₀
  ⊢-sem choice _ ∀x∃yPxy .π₁ x =  ∀x∃yPxy x .π₁

  -- →-introˡ :  P ∧ Q ⊢[ ∞ ] R →  Q ⊢[ ∞ ] P →' R

  ⊢-sem (→-introˡ {Q = Q} P∧Q⊢R) _ =
    →ᵒ-introˡ (⸨⸩-Mono {Q}) λ ✓b (Pb , Qb) → ⊢-sem P∧Q⊢R ✓b $ binary Pb Qb

  -- →-elimˡ :  Q ⊢[ ∞ ] P →' R →  P ∧ Q ⊢[ ∞ ] R

  ⊢-sem (→-elimˡ Q⊢P→R) ✓a P∧Qa =  →ᵒ-elimˡ (⊢-sem Q⊢P→R) ✓a (P∧Qa 0₂ , P∧Qa 1₂)

  -- ∗-monoˡ :  P ⊢[ ∞ ] Q →  P ∗ R ⊢[ ∞ ] Q ∗ R

  ⊢-sem (∗-monoˡ P⊢Q) =  ∗ᵒ-mono✓ˡ (⊢-sem P⊢Q)

  -- ⊤∗-elim :  ⊤' ∗ P ⊢[ ∞ ] P

  ⊢-sem (⊤∗-elim {P}) _ =  ∗ᵒ-elimʳ $ ⸨⸩-Mono {P}

  -- ⊤∗-intro :  P ⊢[ ∞ ] ⊤' ∗ P

  ⊢-sem ⊤∗-intro _ =  ?∗ᵒ-intro absurd

  -- ∗-comm :  P ∗ Q ⊢[ ∞ ] Q ∗ P

  ⊢-sem ∗-comm _ =  ∗ᵒ-comm

  -- ∗-assocʳ :  (P ∗ Q) ∗ R ⊢[ ∞ ] P ∗ (Q ∗ R)

  ⊢-sem ∗-assocʳ _ =  ∗ᵒ-assocʳ

  -- -∗-introˡ :  P ∗ Q ⊢[ ∞ ] R →  Q ⊢[ ∞ ] P -∗ R

  ⊢-sem (-∗-introˡ P∗Q⊢R) _ =  -∗ᵒ-introˡ $ ⊢-sem P∗Q⊢R

  -- -∗-elimˡ :  Q ⊢[ ∞ ] P -∗ R →  P ∗ Q ⊢[ ∞ ] R

  ⊢-sem (-∗-elimˡ {R = R} Q⊢P-∗R) =  -∗ᵒ-elimˡ (⸨⸩-Mono {R}) $ ⊢-sem Q⊢P-∗R

  -- ⤇-mono :  P ⊢[ ∞ ] Q →  ⤇ P ⊢[ ∞ ] ⤇ Q

  ⊢-sem (⤇-mono P⊢Q) _ =  ⤇ᵒ-mono✓ $ ⊢-sem P⊢Q

  -- ⤇-intro :  P ⊢[ ∞ ] ⤇ P

  ⊢-sem ⤇-intro _ =  ⤇ᵒ-intro

  -- ⤇-join :  ⤇ ⤇ P ⊢[ ∞ ] ⤇ P

  ⊢-sem ⤇-join _ =  ⤇ᵒ-join

  -- ⤇-eatˡ :  Q ∗ ⤇ P ⊢[ ∞ ] ⤇ (Q ∗ P)

  ⊢-sem ⤇-eatˡ _ =  ⤇ᵒ-eatˡ

  -- ⤇-⌜⌝∧-out :  ⤇ (⌜ X ⌝∧ P) ⊢[ ∞ ] ⌜ X ⌝∧ ⤇ P

  ⊢-sem ⤇-⌜⌝∧-out =  ⤇ᵒ-⌜⌝ᵒ×-out

  -- □-mono :  P ⊢[ ∞ ] Q →  □ P ⊢[ ∞ ] □ Q

  ⊢-sem (□-mono P⊢Q) =  □ᵒ-mono✓ $ ⊢-sem P⊢Q

  -- □-elim :  □ P ⊢[ ∞ ] P

  ⊢-sem (□-elim {P}) _ =  □ᵒ-elim $ ⸨⸩-Mono {P}

  -- □-dup :  □ P ⊢[ ∞ ] □ □ P

  ⊢-sem (□-dup {P}) _ =   □ᵒ-dup $ ⸨⸩-Mono {P}

  -- □ˡ-∧⇒∗ :  □ P ∧ Q ⊢[ ∞ ] □ P ∗ Q

  ⊢-sem (□ˡ-∧⇒∗ {P}) _ □P∧Qa =  □ᵒˡ-×ᵒ⇒∗ᵒ (⸨⸩-Mono {P}) (□P∧Qa 0₂ , □P∧Qa 1₂)

  -- □-∀-in :  ∀˙ (□_ ∘ P˙) ⊢[ ∞ ] □ ∀˙ P˙

  ⊢-sem □-∀-in _ =  id

  -- □-∃-out :  □ ∃˙ P˙ ⊢[ ∞ ] ∃˙ (□_ ∘ P˙)

  ⊢-sem □-∃-out _ =  id

  -- []ᴺ-resp :  Nm ≡˙ Nm' →  [ Nm ]ᴺ ⊢[ ∞ ] [ Nm' ]ᴺ

  ⊢-sem ([]ᴺ-resp Nm≡Nm') _ =  []ᴺᵒ-resp Nm≡Nm'

  -- []ᴺ-merge :  [ Nm ]ᴺ  ∗  [ Nm' ]ᴺ  ⊢[ ∞ ]  [ Nm ⊎ᶻ Nm' ]ᴺ

  ⊢-sem []ᴺ-merge _ =  []ᴺᵒ-merge

  -- []ᴺ-split :  [ Nm ⊎ᶻ Nm' ]ᴺ  ⊢[ ∞ ]  [ Nm ]ᴺ  ∗  [ Nm' ]ᴺ

  ⊢-sem []ᴺ-split _ =  []ᴺᵒ-split

  -- []ᴺ-✔ :  [ Nm ]ᴺ  ⊢[ ∞ ]  ⌜ ✔ᶻ Nm ⌝

  ⊢-sem []ᴺ-✔ ✓∙ =  []ᴺᵒ-✔ ✓∙ › (_, absurd)

  -- ↦⟨⟩-resp :  p ≈ᴿ⁺ q  →   θ ↦⟨ p ⟩ ᵗv  ⊢[ ∞ ]  θ ↦⟨ q ⟩ ᵗv

  ⊢-sem (↦⟨⟩-resp p≈q) _ =  ↦⟨⟩ᵒ-resp p≈q

  -- ↦⟨⟩-merge :  θ ↦⟨ p ⟩ ᵗv  ∗  θ ↦⟨ q ⟩ ᵗv  ⊢[ ∞ ]  θ ↦⟨ p +ᴿ⁺ q ⟩ ᵗv

  ⊢-sem ↦⟨⟩-merge _ =  ↦⟨⟩ᵒ-merge

  -- ↦⟨⟩-split :  θ ↦⟨ p +ᴿ⁺ q ⟩ ᵗv  ⊢[ ∞ ]  θ ↦⟨ p ⟩ ᵗv  ∗  θ ↦⟨ q ⟩ ᵗv

  ⊢-sem ↦⟨⟩-split _ =  ↦⟨⟩ᵒ-split

  -- ↦⟨⟩-≤1 :  θ ↦⟨ p ⟩ ᵗv  ⊢[ ∞ ]  ⌜ p ≤1ᴿ⁺ ⌝

  ⊢-sem ↦⟨⟩-≤1 ✓a =  ↦⟨⟩ᵒ-≤1 ✓a › (_, absurd)

  -- ↦⟨⟩-agree :  θ ↦⟨ p ⟩ ᵗu  ∗  θ ↦⟨ q ⟩ ᵗv  ⊢[ ∞ ]  ⌜ ᵗu ≡ ᵗv ⌝

  ⊢-sem ↦⟨⟩-agree ✓a =  ↦⟨⟩ᵒ-agree ✓a › (_, absurd)

  -- ○-mono :  P˂ .! ⊢[< ∞ ] Q˂ .! →  ○ P˂ ⊢[ ∞ ] ○ Q˂

  ⊢-sem (○-mono P⊢Q) _ =  ○ᵒ-mono $ P⊢Q .!

  -- ○-eatˡ :  {{Basic Q}} →  Q ∗ ○ P˂ ⊢[ ∞ ] ○ ¡ᴾ (Q ∗ P˂ .!)

  ⊢-sem (○-eatˡ {Q}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {Q}) › ○ᵒ-eatˡ

  -- ⊸⇛-≤ :  i ≤ j  →   P˂ ⊸[ i ]⇛ Q˂  ⊢[ ∞ ]  P˂ ⊸[ j ]⇛ Q˂

  ⊢-sem (⊸⇛-≤ i≤j) _ =  ⊸⇛ᵒ-≤ i≤j

  -- ⊸⇛-eatˡ⁻ˡᵘ :  {{Basic R}}  →   R  ∗  P'˂ .!  ⊢[< ∞ ][ i ]⇛  P˂ .! →
  --               R  ∗  (P˂ ⊸[ i ]⇛ Q˂)  ⊢[ ∞ ]  P'˂ ⊸[ i ]⇛ Q˂

  ⊢-sem (⊸⇛-eatˡ⁻ˡᵘ {R} R∗P'⊢⇛P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ⊸⇛ᵒ-eatˡ⁻ˡᵘ $ R∗P'⊢⇛P .!

  -- ⊸⇛-monoʳᵘ :  Q˂ .!  ⊢[< ∞ ][ i ]⇛  Q'˂ .! →
  --              P˂ ⊸[ i ]⇛ Q˂  ⊢[ ∞ ]  P˂ ⊸[ i ]⇛ Q'˂

  ⊢-sem (⊸⇛-monoʳᵘ Q⊢⇛Q') _ =  ⊸⇛ᵒ-monoʳᵘ $ Q⊢⇛Q' .!

  -- ⊸⇛-eatˡ⁻ʳ :  {{Basic R}}  →
  --   R  ∗  (P˂ ⊸[ i ]⇛ Q˂)  ⊢[ ∞ ]  P˂ ⊸[ i ]⇛ ¡ᴾ (R ∗ Q˂ .!)

  ⊢-sem (⊸⇛-eatˡ⁻ʳ {R}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ⊸⇛ᵒ-eatˡ⁻ʳ

  -- ⊸⇛-frameʳ :  P˂ ⊸[ i ]⇛ Q˂  ⊢[ ∞ ]  ¡ᴾ (R ∗ P˂ .!) ⊸[ i ]⇛ ¡ᴾ (R ∗ Q˂ .!)

  ⊢-sem ⊸⇛-frameʳ _ =  ⊸⇛ᵒ-frameʳ

  -- ○⇒⊸⇛ :  P˂ .!  ∗  R˂ .!  ⊢[< ∞ ][ i ]⇛  Q˂ .!  →
  --         ○ R˂  ⊢[ ∞ ]  P˂ ⊸[ i ]⇛ Q˂

  ⊢-sem (○⇒⊸⇛ P∗R⊢⇛Q) _ =  ○ᵒ⇒⊸⇛ᵒ $ P∗R⊢⇛Q .!

  -- ⊸ᵃ⟨⟩-≤ :  i ≤ j  →   P˂ ⊸[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ∞ ]  P˂ ⊸[ j ]ᵃ⟨ red ⟩ Q˂˙

  ⊢-sem (⊸ᵃ⟨⟩-≤ i≤j) _ =  ⊸ᵃ⟨⟩ᵒ-≤ i≤j

  -- ⊸ᵃ⟨⟩-eatˡ⁻ˡᵘ :  {{Basic R}}  →   R  ∗  P'˂ .!  ⊢[< ∞ ][ i ]⇛  P˂ .!  →
  --                 R ∗ (P˂ ⊸[ j ]ᵃ⟨ red ⟩ Q˂˙)  ⊢[ ∞ ]  P'˂ ⊸[ j ]ᵃ⟨ red ⟩ Q˂˙

  ⊢-sem (⊸ᵃ⟨⟩-eatˡ⁻ˡᵘ {R} R∗P'⊢⇛P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ⊸ᵃ⟨⟩ᵒ-eatˡ⁻ˡᵘ $ R∗P'⊢⇛P .!

  -- ⊸ᵃ⟨⟩-monoʳᵘ :  (∀ v →  Q˂˙ v .!  ⊢[< ∞ ][ i ]⇛  Q'˂˙ v .!)  →
  --                P˂ ⊸[ j ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ∞ ]  P˂ ⊸[ j ]ᵃ⟨ red ⟩ Q'˂˙

  ⊢-sem (⊸ᵃ⟨⟩-monoʳᵘ ∀vQ⊢⇛Q') _ =  ⊸ᵃ⟨⟩ᵒ-monoʳᵘ λ v → ∀vQ⊢⇛Q' v .!

  -- ⊸ᵃ⟨⟩-eatˡ⁻ʳ :  {{Basic R}}  →
  --   R  ∗  (P˂ ⊸[ i ]ᵃ⟨ red ⟩ Q˂˙)  ⊢[ ∞ ]
  --     P˂ ⊸[ i ]ᵃ⟨ red ⟩ λ v → ¡ᴾ (R ∗ Q˂˙ v .!)

  ⊢-sem (⊸ᵃ⟨⟩-eatˡ⁻ʳ {R}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ⊸ᵃ⟨⟩ᵒ-eatˡ⁻ʳ

  -- ⊸ᵃ⟨⟩-frameʳ :  P˂ ⊸[ i ]ᵃ⟨ red ⟩ Q˂˙  ⊢[ ∞ ]
  --                  ¡ᴾ (R ∗ P˂ .!) ⊸[ i ]ᵃ⟨ red ⟩ λ v → ¡ᴾ (R ∗ Q˂˙ v .!)

  ⊢-sem ⊸ᵃ⟨⟩-frameʳ _ =  ⊸ᵃ⟨⟩ᵒ-frameʳ

  -- ○⇒⊸ᵃ⟨⟩ :  P˂ .!  ∗  R˂ .!  ⊢[< ∞ ][ i ]ᵃ⟨ red ⟩ (λ v →  Q˂˙ v .!)  →
  --           ○ R˂  ⊢[ ∞ ]  P˂ ⊸[ i ]ᵃ⟨ red ⟩ Q˂˙

  ⊢-sem (○⇒⊸ᵃ⟨⟩ P∗R⊢⟨red⟩Q) _ =  ○ᵒ⇒⊸ᵃ⟨⟩ᵒ $ P∗R⊢⟨red⟩Q .!

  -- ⊸⟨⟩ᵀ⇒⊸⟨⟩ᴾ :  P˂ ⊸⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ∞ ]  P˂ ⊸⟨ e ⟩ᴾ Q˂˙

  ⊢-sem ⊸⟨⟩ᵀ⇒⊸⟨⟩ᴾ _ =  ⊸⟨⟩ᵀᵒ⇒⊸⟨⟩ᴾᵒ

  -- ⊸⟨⟩ᵀ-≤ :  i ≤ j  →   P˂ ⊸⟨ e ⟩ᵀ[ i ] Q˂˙  ⊢[ ∞ ]  P˂ ⊸⟨ e ⟩ᵀ[ j ] Q˂˙

  ⊢-sem (⊸⟨⟩ᵀ-≤ i≤j) _ =  ⊸⟨⟩ᵀᵒ-≤ i≤j

  -- ⊸⟨⟩-eatˡ⁻ˡᵘᴺ :  {{Basic R}}  →   R  ∗  P'˂ .!  ⊢[< ∞ ][ i ]⇛ᴺ  P˂ .!  →
  --                 R  ∗  (P˂ ⊸⟨ e ⟩[ κ ] Q˂˙)  ⊢[ ∞ ]  P'˂ ⊸⟨ e ⟩[ κ ] Q˂˙

  ⊢-sem (⊸⟨⟩-eatˡ⁻ˡᵘᴺ {R} R∗P'⊢⇛P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ⊸⟨⟩ᵒ-eatˡ⁻ˡᵘᴺ $ R∗P'⊢⇛P .!

  -- ⊸⟨⟩-monoʳᵘᴺ :  (∀ v →  Q˂˙ v .!  ⊢[< ∞ ][ i ]⇛ᴺ  Q'˂˙ v .!)  →
  --                P˂ ⊸⟨ e ⟩[ κ ] Q˂˙  ⊢[ ∞ ]  P˂ ⊸⟨ e ⟩[ κ ] Q'˂˙

  ⊢-sem (⊸⟨⟩-monoʳᵘᴺ ∀vQ⊢⇛Q') _ =  ⊸⟨⟩ᵒ-monoʳᵘᴺ λ v → ∀vQ⊢⇛Q' v .!

  -- ⊸⟨⟩-eatˡ⁻ʳ :  {{Basic R}}  →   R  ∗  (P˂ ⊸⟨ e ⟩[ κ ] Q˂˙)  ⊢[ ∞ ]
  --                                  P˂ ⊸⟨ e ⟩[ κ ] λ v → ¡ᴾ (R ∗ Q˂˙ v .!)

  ⊢-sem (⊸⟨⟩-eatˡ⁻ʳ {R}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ⊸⟨⟩ᵒ-eatˡ⁻ʳ

  -- ⊸⟨⟩-frameʳ :  P˂ ⊸⟨ e ⟩[ κ ] Q˂˙  ⊢[ ∞ ]
  --                 ¡ᴾ (R ∗ P˂ .!) ⊸⟨ e ⟩[ κ ] λ v → ¡ᴾ (R ∗ Q˂˙ v .!)

  ⊢-sem ⊸⟨⟩-frameʳ _ =  ⊸⟨⟩ᵒ-frameʳ

  -- ○⇒⊸⟨⟩ :  P˂ .!  ∗  R˂ .!  ⊢[< ∞ ]⟨ e ⟩[ κ ] (λ v →  Q˂˙ v .!)  →
  --          ○ R˂  ⊢[ ∞ ]  P˂ ⊸⟨ e ⟩[ κ ] Q˂˙

  ⊢-sem (○⇒⊸⟨⟩ P∗R⊢⟨e⟩Q) _ =  ○ᵒ⇒⊸⟨⟩ᵒ $ P∗R⊢⟨e⟩Q .!

  -- ⊸⟨⟩∞⇒⊸⟨⟩ᴾ :  P˂ ⊸[ i ]⟨ e ⟩∞  ⊢[ ∞ ]  P˂ ⊸⟨ e ⟩ᴾ Q˂˙

  ⊢-sem ⊸⟨⟩∞⇒⊸⟨⟩ᴾ _ =  ⊸⟨⟩∞ᵒ⇒⊸⟨⟩ᴾᵒ

  -- ⊸⟨⟩∞-≤ :  i ≤ j  →   P˂ ⊸[ i ]⟨ e ⟩∞  ⊢[ ∞ ]  P˂ ⊸[ j ]⟨ e ⟩∞

  ⊢-sem (⊸⟨⟩∞-≤ i≤j) _ =  ⊸⟨⟩∞ᵒ-≤ i≤j

  -- ⊸⟨⟩∞-eatˡ⁻ᵘᴺ :  {{Basic R}}  →   R  ∗  Q˂ .!  ⊢[< ∞ ][ i ]⇛ᴺ  P˂ .!  →
  --                 R  ∗  (P˂ ⊸[ j ]⟨ e ⟩∞)  ⊢[ ∞ ]  Q˂ ⊸[ j ]⟨ e ⟩∞

  ⊢-sem (⊸⟨⟩∞-eatˡ⁻ᵘᴺ {R} R∗Q⊢⇛P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › ⊸⟨⟩∞ᵒ-eatˡ⁻ᵘᴺ $ R∗Q⊢⇛P .!

  -- ○⇒⊸⟨⟩∞ :  P˂ .!  ∗  Q˂ .!  ⊢[< ∞ ][ i ]⟨ e ⟩∞   →
  --           ○ Q˂  ⊢[ ∞ ]  P˂ ⊸[ i ]⟨ e ⟩∞

  ⊢-sem (○⇒⊸⟨⟩∞ P∗Q⊢⟨e⟩∞) _ =  ○ᵒ⇒⊸⟨⟩∞ᵒ $ P∗Q⊢⟨e⟩∞ .!

  -- &ⁱ-⇒□ :  &ⁱ⟨ nm ⟩ P˂  ⊢[ ∞ ]  □ &ⁱ⟨ nm ⟩ P˂

  ⊢-sem &ⁱ-⇒□ _ =  &ⁱᵒ-⇒□ᵒ

  -- &ⁱ-resp-□∗ :  {{Basic R}}  →
  --   R  ∗  P˂ .!  ⊢[< ∞ ]  Q˂ .!  →   R  ∗  Q˂ .!  ⊢[< ∞ ]  P˂ .!  →
  --   □ R  ∗  &ⁱ⟨ nm ⟩ P˂  ⊢[ ∞ ]  &ⁱ⟨ nm ⟩ Q˂

  ⊢-sem (&ⁱ-resp-□∗ {R} R∗P⊢Q R∗Q⊢P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › &ⁱᵒ-resp-□ᵒ∗ᵒ (R∗P⊢Q .!) (R∗Q⊢P .!)

  -- ⅋ⁱ-mono :  Q˂ .!  ⊢[< ∞ ]  P˂ .!  →   ⅋ⁱ⟨ nm ⟩ P˂  ⊢[ ∞ ]  ⅋ⁱ⟨ nm ⟩ Q˂

  ⊢-sem (⅋ⁱ-mono P⊢Q) _ =  ⅋ⁱᵒ-mono $ P⊢Q .!

  -- ⅋ⁱ-eatˡ :  {{Basic Q}}  →
  --   Q  ∗  ⅋ⁱ⟨ nm ⟩ P˂  ⊢[ ∞ ]  ⅋ⁱ⟨ nm ⟩ ¡ᴾ (Q -∗ P˂ .!)

  ⊢-sem (⅋ⁱ-eatˡ {Q}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {Q}) › ⅋ⁱᵒ-eatˡ

  -- []ᴸ⟨⟩-resp :  p ≈ᴿ⁺ q  →   [ α ]ᴸ⟨ p ⟩  ⊢[ ∞ ]  [ α ]ᴸ⟨ q ⟩

  ⊢-sem ([]ᴸ⟨⟩-resp p≈q) _ =  []ᴸ⟨⟩ᵒ-resp p≈q

  -- []ᴸ⟨⟩-merge :  [ α ]ᴸ⟨ p ⟩  ∗  [ α ]ᴸ⟨ q ⟩  ⊢[ ∞ ]  [ α ]ᴸ⟨ p +ᴿ⁺ q ⟩

  ⊢-sem []ᴸ⟨⟩-merge _ =  []ᴸ⟨⟩ᵒ-merge

  -- []ᴸ⟨⟩-split :  [ α ]ᴸ⟨ p +ᴿ⁺ q ⟩  ⊢[ ∞ ]  [ α ]ᴸ⟨ p ⟩  ∗  [ α ]ᴸ⟨ q ⟩

  ⊢-sem []ᴸ⟨⟩-split _ =  []ᴸ⟨⟩ᵒ-split

  -- []ᴸ⟨⟩-≤1 :  [ α ]ᴸ⟨ p ⟩  ⊢[ ∞ ]  ⌜ p ≤1ᴿ⁺ ⌝

  ⊢-sem []ᴸ⟨⟩-≤1 p≤1 =  []ᴸ⟨⟩ᵒ-≤1 p≤1 › (_, absurd)

  -- †ᴸ-⇒□ :  †ᴸ α  ⊢[ ∞ ]  □ †ᴸ α

  ⊢-sem †ᴸ-⇒□ _ =  †ᴸᵒ-⇒□ᵒ

  -- []ᴸ⟨⟩-†ᴸ-no :  [ α ]ᴸ⟨ p ⟩  ∗  †ᴸ α  ⊢[ ∞ ]  ⊥'

  ⊢-sem []ᴸ⟨⟩-†ᴸ-no ✓∙ =  []ᴸ⟨⟩ᵒ-†ᴸᵒ-no ✓∙ › λ ()

  -- []ᴸ-new :  ⊤'  ⊢[ ∞ ] ⤇  ∃ α , [ α ]ᴸ

  ⊢-sem []ᴸ-new _ _ =  []ᴸᵒ-new

  -- []ᴸ-kill :  [ α ]ᴸ  ⊢[ ∞ ] ⤇  †ᴸ α

  ⊢-sem []ᴸ-kill _ =  []ᴸᵒ-kill

  -- &ᵐ-resp-□∗ :  {{Basic R}}  →
  --   R  ∗  P˂ .!  ⊢[< ∞ ]  Q˂ .!  →   R  ∗  Q˂ .!  ⊢[< ∞ ]  P˂ .!  →
  --   □ R  ∗  &ᵐ⟨ α ⟩ P˂  ⊢[ ∞ ]  &ᵐ⟨ α ⟩ Q˂

  ⊢-sem (&ᵐ-resp-□∗ {R} R∗P⊢Q R∗Q⊢P) _ =
    ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {R}) › &ᵐᵒ-resp-□ᵒ∗ᵒ (R∗P⊢Q .!) (R∗Q⊢P .!)

  -- ⅋ᵐ-respᴿ :  p ≈ᴿ⁺ q  →   ⅋ᵐ⟨ α , p ⟩ P˂  ⊢[ ∞ ]  ⅋ᵐ⟨ α , q ⟩ P˂

  ⊢-sem (⅋ᵐ-respᴿ {p} {q} p≈q) _ =  ⅋ᵐᵒ-respᴿ {p} {q} p≈q

  -- ⅋ᵐ-monoᴾ :
  --   Q˂ .!  ⊢[< ∞ ]  P˂ .!  →  ⅋ᵐ⟨ α , p ⟩ P˂  ⊢[ ∞ ]  ⅋ᵐ⟨ α , p ⟩ Q˂

  ⊢-sem (⅋ᵐ-monoᴾ {p = p} Q⊢P) _ =  ⅋ᵐᵒ-monoᴾ {p = p} $ Q⊢P .!

  -- ⅋ᵐ-eatˡ :  {{Basic Q}}  →
  --   Q  ∗  ⅋ᵐ⟨ α , p ⟩ P˂  ⊢[ ∞ ]  ⅋ᵐ⟨ α , p ⟩ ¡ᴾ (Q -∗ P˂ .!)

  ⊢-sem (⅋ᵐ-eatˡ {Q} {p = p}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {Q}) › ⅋ᵐᵒ-eatˡ {p = p}

  -- ⟨†⟩-mono :  P˂ .!  ⊢[< ∞ ]  Q˂ .!  →   ⟨† α ⟩ P˂  ⊢[ ∞ ]  ⟨† α ⟩ Q˂

  ⊢-sem (⟨†⟩-mono P⊢Q) _ =  ⟨†⟩ᵒ-mono $ P⊢Q .!

  -- ⟨†⟩-eatˡ :  {{Basic Q}}  →   Q  ∗  ⟨† α ⟩ P˂  ⊢[ ∞ ]  ⟨† α ⟩ ¡ᴾ (Q ∗ P˂ .!)

  ⊢-sem (⟨†⟩-eatˡ {Q}) _ =  ∗ᵒ-monoˡ (⸨⸩-⇒ᴮ {Q}) › ⟨†⟩ᵒ-eatˡ

  -- ≤ᵁᵇ-mono :  m ≤ n  →   ≤ᵁᵇ⟨ o ⟩ m  ⊢[ ∞ ]  ≤ᵁᵇ⟨ o ⟩ n

  ⊢-sem (≤ᵁᵇ-mono m≤n) _ =  ≤ᵁᵇᵒ-mono m≤n

  -- ≤ᵁᵇ-⇒□ :  ≤ᵁᵇ⟨ o ⟩ n  ⊢[ ∞ ]  □ ≤ᵁᵇ⟨ o ⟩ n

  ⊢-sem ≤ᵁᵇ-⇒□ _ =  ≤ᵁᵇᵒ-⇒□ᵒ

  -- ≤ᵁᵇ-#ᵁᵇ :  ≤ᵁᵇ⟨ o ⟩ m  ∗  #ᵁᵇ⟨ o ⟩ n  ⊢[ ∞ ]  ⌜ n ≤ m ⌝

  ⊢-sem ≤ᵁᵇ-#ᵁᵇ ✓∙ =  ≤ᵁᵇᵒ-#ᵁᵇᵒ ✓∙ › (_, absurd)

  -- #ᵁᵇ-new :  ⊤'  ⊢[ ∞ ] ⤇  ∃ o , ≤ᵁᵇ⟨ o ⟩ n  ∗  #ᵁᵇ⟨ o ⟩ n

  ⊢-sem #ᵁᵇ-new _ _ =  #ᵁᵇᵒ-new

  -- #ᵁᵇ-upd :  m ≤ n  →   #ᵁᵇ⟨ o ⟩ n  ⊢[ ∞ ] ⤇  ≤ᵁᵇ⟨ o ⟩ m  ∗  #ᵁᵇ⟨ o ⟩ m

  ⊢-sem (#ᵁᵇ-upd m≤n) _ =  #ᵁᵇᵒ-upd m≤n

--------------------------------------------------------------------------------
-- Adequacy of the pure sequent

abstract

  -- Under the premise [⊤]ᴺ

  ⊢-adeqᴺ :  [⊤]ᴺ ⊢[ ∞ ] ⌜ X ⌝ →  X
  ⊢-adeqᴺ ᴺ⊢X =  ⊢-sem ᴺ⊢X (∅ᴵⁿᴳ-✓ᴺ ✓ᴴ-∅) ◎-just .π₀

  -- Under the premise [^ nm ]ᴺ

  ⊢-adeq-[^]ᴺ :  [^ nm ]ᴺ ⊢[ ∞ ] ⌜ X ⌝ →  X
  ⊢-adeq-[^]ᴺ [nm]⊢X =  ⊢-adeqᴺ $ ᴺ⇒[^] » [nm]⊢X

  -- Under the trivial premise

  ⊢-adeq :  ⊤' ⊢[ ∞ ] ⌜ X ⌝ →  X
  ⊢-adeq ⊢X =  ⊢-adeqᴺ $ ⊤-intro » ⊢X
