--------------------------------------------------------------------------------
-- Paradoxes on plausible proof rules
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Symp.Logic.Paradox where

open import Base.Func using (_$_; flip)
open import Base.Eq using (refl)
open import Base.Size using (∞; !)
open import Base.Prod using (-,_)
open import Symp.Lang.Expr using (Type; Expr∞; loop; Val)
open import Symp.Lang.Ktxred using (Redex)
open import Symp.Lang.Reduce using (_⇒ᴾ_; redᴾ)
open import Symp.Logic.Prop using (Name; strnm; Lft; SProp∞; SProp˂∞; ¡ᴾ_;
  ∃-syntax; _∨_; ⊤'; ⊥'; □_; _∗_; _-∗_; [^_]ᴺ; ○_; _⊸[_]⇛_; _⊸[_]ᵃ⟨_⟩_; _⊸⟨_⟩ᴾ_;
  _⊸⟨_⟩ᵀ[_]_; _⊸[_]⟨_⟩∞; &ⁱ⟨_⟩_; ⅋ⁱ⟨_⟩_; [_]ᴸ; †ᴸ_)
open import Symp.Logic.Core using (_⊢[_]_; ⇒<; ⊢-refl; _»_; ∃-elim; ∃-intro;
  ∨-introˡ; ∨-introʳ; ⊥-elim; ∗-monoˡ; ∗-monoʳ; ∗-comm; ∗-assocˡ; ∗-assocʳ;
  ?∗-comm; ∗-elimˡ; ∗-elimʳ; ⊤∗-intro; ∗⊤-intro; ∃∗-elim; ∨∗-elim; ∗∨-elim;
  -∗-introˡ; -∗-introʳ; -∗-applyʳ; □-mono; □-elim; □-intro-Pers; dup-Pers-∗)
open import Symp.Logic.Fupd using (_⊢[_][_]⇛_; ⤇⇒⇛; _ᵘ»ᵘ_; _ᵘ»_; ⇛-frameˡ;
  ⇛-frameʳ)
open import Symp.Logic.Hor using (_⊢[_][_]ᵃ⟨_⟩_; _⊢[_]⟨_⟩ᴾ_; _⊢[_]⟨_⟩ᵀ[_]_;
  _⊢[_][_]⟨_⟩∞; _ᵘ»ᵃʰ_; _ᵘ»ʰ_; _ᵘ»ⁱʰ_)
open import Symp.Logic.Ind using (○-mono; □○-new-rec; ○-use; ○⇒⊸⇛; ○⇒⊸ᵃ⟨⟩;
  ○⇒⊸⟨⟩; ○⇒⊸⟨⟩∞)
open import Symp.Logic.Inv using (&ⁱ-new; &ⁱ-open; ⅋ⁱ-close)
open import Symp.Logic.Lft using ([]ᴸ⟨⟩-†ᴸ-no; []ᴸ-new; []ᴸ-kill)

private variable
  α :  Lft
  X :  Set₀
  T :  Type
  P Q :  SProp∞
  P˂ Q˂ :  SProp˂∞
  Q˙ :  X →  SProp∞
  Q˂˙ :  X →  SProp˂∞

--------------------------------------------------------------------------------
-- If we have the fancy update as a modality ⇛ᵐ, then we have a paradox, because
-- we can construct something like Landin's knot using our later-less
-- impredicative invariant and the two-state protocol (here we repurpose the
-- lifetime and dead lifetime tokens)

-- Our construction is based on Iris's paradox of the "naive impredicative
-- invariant" (Jung et al. "Iris from the Ground Up" JFP 2018) but does not
-- depend on quantification over propositions, not supported by our logic
-- This is much simpler than Iris's original construction

module _ {nm : Name} (⇛ᵐ : SProp∞ → SProp∞)
  (⇛ᵐ-intro :  ∀{P Q} →  P ⊢[ ∞ ][ 0 ]⇛ Q →  P ⊢[ ∞ ] ⇛ᵐ Q)
  (⇛ᵐ-elim :  ∀{P Q} →  P ⊢[ ∞ ] ⇛ᵐ Q →  P ⊢[ ∞ ][ 0 ]⇛ Q)
  where abstract

  -- □⇛⊥ :  Persistent proposition for getting ⊥' after update with [^ nm ]ᴺ

  □⇛⊥/⇛ᵐ :  SProp∞
  □⇛⊥/⇛ᵐ =  □ ([^ nm ]ᴺ -∗ ⇛ᵐ ⊥')

  -- Evil :  The evil impredicative invariant

  Evil/⇛ᵐ :  Lft → SProp∞
  Evil/⇛ᵐ α =  &ⁱ⟨ nm ⟩ ¡ᴾ ([ α ]ᴸ ∨ □⇛⊥/⇛ᵐ)

  -- We get contradiction consuming □⇛⊥ and ⅋ⁱ⟨ nm ⟩ ¡ᴾ ([ α ]ᴸ ∨ □⇛⊥/⇛ᵐ)

  □⇛⊥-⅋ⁱ-no/⇛ᵐ :  □⇛⊥/⇛ᵐ  ∗  ⅋ⁱ⟨ nm ⟩ ¡ᴾ ([ α ]ᴸ ∨ □⇛⊥/⇛ᵐ)  ⊢[ ∞ ][ 0 ]⇛  ⊥'
  □⇛⊥-⅋ⁱ-no/⇛ᵐ =  dup-Pers-∗ » ⇛-frameʳ (∗-monoˡ ∨-introʳ » ⅋ⁱ-close) ᵘ»ᵘ
    ∗-monoˡ □-elim » -∗-applyʳ » ⇛ᵐ-elim ⊢-refl

  -- Create Evil

  Evil-intro/⇛ᵐ :  ⊤'  ⊢[ ∞ ][ 0 ]⇛  ∃ α , Evil/⇛ᵐ α
  Evil-intro/⇛ᵐ =  []ᴸ-new » ⤇⇒⇛ ᵘ»ᵘ ∃-elim λ α → ∨-introˡ » &ⁱ-new ᵘ» ∃-intro α

  -- We get contradiction out of †ᴸ α and Evil α with [^ nm ]ᴺ,
  -- because †ᴸ α eliminates the possibility of [ α ]ᴸ when we open Evil α

  †ᴸ-Evil-no/⇛ᵐ :  †ᴸ α  ∗  Evil/⇛ᵐ α  ∗  [^ nm ]ᴺ  ⊢[ ∞ ][ 0 ]⇛  ⊥'
  †ᴸ-Evil-no/⇛ᵐ =  ⇛-frameʳ &ⁱ-open ᵘ»ᵘ ∗-assocˡ »
    ∗-monoˡ (∗∨-elim (∗-comm » []ᴸ⟨⟩-†ᴸ-no » ⊥-elim) ∗-elimʳ) » □⇛⊥-⅋ⁱ-no/⇛ᵐ

  -- So †ᴸ α and Evil α turns into □⇛⊥/⇛ᵐ

  †ᴸ-Evil-□⇛⊥/⇛ᵐ :  †ᴸ α  ∗  Evil/⇛ᵐ α  ⊢[ ∞ ]  □⇛⊥/⇛ᵐ
  †ᴸ-Evil-□⇛⊥/⇛ᵐ =  □-intro-Pers $
    -∗-introʳ $ ⇛ᵐ-intro $ ∗-assocʳ » †ᴸ-Evil-no/⇛ᵐ

  -- We get contradiction out of Evil α with [^ nm ]ᴺ
  -- When we open Evil α, in the case the content is [ α ]ᴸ, we can kill it to
  -- get †ᴸ α; this allows us to close the invariant (by †ᴸ-Evil-□⇛⊥/⇛ᵐ), and
  -- the retrieved name token allows us to get ⊥' (by †ᴸ-Evil-no/⇛ᵐ)

  Evil-no/⇛ᵐ :  Evil/⇛ᵐ α  ∗  [^ nm ]ᴺ  ⊢[ ∞ ][ 0 ]⇛  ⊥'
  Evil-no/⇛ᵐ =  dup-Pers-∗ » ⇛-frameʳ &ⁱ-open ᵘ»ᵘ ?∗-comm »
    flip ∨∗-elim (∗-monoʳ ∗-elimʳ » □⇛⊥-⅋ⁱ-no/⇛ᵐ) $
    ⇛-frameˡ ([]ᴸ-kill » ⤇⇒⇛) ᵘ»ᵘ ∗-assocˡ » dup-Pers-∗ »
    ⇛-frameʳ (∗-monoˡ (†ᴸ-Evil-□⇛⊥/⇛ᵐ » ∨-introʳ) » ⅋ⁱ-close) ᵘ»ᵘ
    ∗-assocʳ » †ᴸ-Evil-no/⇛ᵐ

  -- Therefore, combining Evil-intro/⇛ᵐ and Evil-no/⇛ᵐ, we get contradiction out
  -- of [^ nm ]ᴺ, which is a paradox!

  [^nm]ᴺ-no/⇛ᵐ :  [^ nm ]ᴺ  ⊢[ ∞ ][ 0 ]⇛  ⊥'
  [^nm]ᴺ-no/⇛ᵐ =  ⊤∗-intro »
    ⇛-frameˡ Evil-intro/⇛ᵐ ᵘ»ᵘ ∃∗-elim λ _ → Evil-no/⇛ᵐ

--------------------------------------------------------------------------------
-- If we have existential quantification over SProp∞ as well as lifting of
-- the fancy update sequent, then we have the paradox observed above,
-- because then we can encode the fancy update modality ⇛ᵐ

-- Lifting of the fancy update sequent would be readily available if we worked
-- on a meta-logic that has the impredicative universe Prop (like Coq)

module _ {nm : Name} (∃ᴾ˙ :  (SProp∞ → SProp∞) →  SProp∞)
  (∃ᴾ-elim :  ∀{P˙ Q} →  (∀ R →  P˙ R ⊢[ ∞ ][ 0 ]⇛ Q) →  ∃ᴾ˙ P˙ ⊢[ ∞ ][ 0 ]⇛ Q)
  (∃ᴾ-intro :  ∀{P˙} R →  P˙ R ⊢[ ∞ ] ∃ᴾ˙ P˙)
  (⌜_⊢⇛_⌝∧_ :  SProp∞ →  SProp∞ →  SProp∞ →  SProp∞)
  (⊢⇛∧-elim :  ∀{P Q R S} →  (P ⊢[ ∞ ][ 0 ]⇛ Q →  R ⊢[ ∞ ][ 0 ]⇛ S) →
                             ⌜ P ⊢⇛ Q ⌝∧ R ⊢[ ∞ ][ 0 ]⇛ S)
  (⊢⇛∧-intro :  ∀{P Q R} →  P ⊢[ ∞ ][ 0 ]⇛ Q →  R ⊢[ ∞ ] ⌜ P ⊢⇛ Q ⌝∧ R)
  where abstract

  -- We can encode the fancy update modality ⇛ᵐ

  ⇛ᵐ/∃ᴾ :  SProp∞ →  SProp∞
  ⇛ᵐ/∃ᴾ P =  ∃ᴾ˙ λ Q →  ⌜ Q ⊢⇛ P ⌝∧  Q

  ⇛ᵐ-intro/∃ᴾ :  P ⊢[ ∞ ][ 0 ]⇛ Q →  P ⊢[ ∞ ] ⇛ᵐ/∃ᴾ Q
  ⇛ᵐ-intro/∃ᴾ P⊢⇛Q =  ⊢⇛∧-intro P⊢⇛Q » ∃ᴾ-intro _

  ⇛ᵐ-elim/∃ᴾ :  P ⊢[ ∞ ] ⇛ᵐ/∃ᴾ Q →  P ⊢[ ∞ ][ 0 ]⇛ Q
  ⇛ᵐ-elim/∃ᴾ P⊢⇛ᵐQ =  P⊢⇛ᵐQ » ∃ᴾ-elim λ R → ⊢⇛∧-elim λ R⊢⇛Q → R⊢⇛Q

  -- Therefore, by [^nm]ᴺ-no/⇛ᵐ, we get contradiction out of [^ nm ]ᴺ,
  -- which is a paradox!

  [^nm]ᴺ-no/∃ᴾ :  [^ nm ]ᴺ  ⊢[ ∞ ][ 0 ]⇛  ⊥'
  [^nm]ᴺ-no/∃ᴾ =  [^nm]ᴺ-no/⇛ᵐ ⇛ᵐ/∃ᴾ ⇛ᵐ-intro/∃ᴾ ⇛ᵐ-elim/∃ᴾ

--------------------------------------------------------------------------------
-- If we can turn ○ P into P, then we get P after a fancy update,
-- thanks to □○-new-rec

○-rec :  ○ ¡ᴾ P ⊢[ ∞ ] P →  ⊤' ⊢[ ∞ ][ 0 ]⇛ P
○-rec ○P⊢P =  -∗-introˡ (∗-elimˡ » □-mono ○P⊢P) » □○-new-rec ᵘ»ᵘ □-elim » ○-use

--------------------------------------------------------------------------------
-- If we can use ⊸⇛ without level increment, then we get a paradox

module _
  -- ⊸⇛-use without level increment
  (⊸⇛-use' :  ∀{P˂ Q˂} →  P˂ .!  ∗  (P˂ ⊸[ 0 ]⇛ Q˂)  ⊢[ ∞ ][ 0 ]⇛  Q˂ .!)
  where abstract

  -- We can strip ○ from ⊸⇛, using ⊸⇛-use'

  ○⇒-⊸⇛/⊸⇛-use' :  ○ ¡ᴾ (P˂ ⊸[ 0 ]⇛ Q˂)  ⊢[ ∞ ]  P˂ ⊸[ 0 ]⇛ Q˂
  ○⇒-⊸⇛/⊸⇛-use' =  ○⇒⊸⇛ $ ⇒< ⊸⇛-use'

  -- Therefore, by ○-rec, we can do any fancy update --- a paradox!

  ⇛/⊸⇛-use' :  P  ⊢[ ∞ ][ 0 ]⇛  Q
  ⇛/⊸⇛-use' =  ∗⊤-intro »
    ⇛-frameʳ (○-rec ○⇒-⊸⇛/⊸⇛-use') ᵘ»ᵘ ⊸⇛-use' {¡ᴾ _} {¡ᴾ _}

--------------------------------------------------------------------------------
-- If we can use ⊸ᵃ⟨ ⟩ without level increment, then we get a paradox

module _ {red : Redex T}
  -- ⊸ᵃ⟨⟩-use without level increment
  (⊸ᵃ⟨⟩-use' :  ∀{P˂ Q˂˙} →
    P˂ .!  ∗  (P˂ ⊸[ 0 ]ᵃ⟨ red ⟩ Q˂˙)  ⊢[ ∞ ][ 0 ]ᵃ⟨ red ⟩ λ v →  Q˂˙ v .!)
  where abstract

  -- We can strip ○ from ⊸ᵃ⟨⟩, using ⊸ᵃ⟨⟩-use'

  ○⇒-⊸ᵃ⟨⟩/⊸ᵃ⟨⟩-use' :
    ○ ¡ᴾ (P˂ ⊸[ 0 ]ᵃ⟨ red ⟩ Q˂˙)  ⊢[ ∞ ]  P˂ ⊸[ 0 ]ᵃ⟨ red ⟩ Q˂˙
  ○⇒-⊸ᵃ⟨⟩/⊸ᵃ⟨⟩-use' =  ○⇒⊸ᵃ⟨⟩ $ ⇒< ⊸ᵃ⟨⟩-use'

  -- Therefore, by ○-rec, we have any total Hoare triple --- a paradox!

  ahor/⊸ᵃ⟨⟩-use' :  P  ⊢[ ∞ ][ 0 ]ᵃ⟨ red ⟩  Q˙
  ahor/⊸ᵃ⟨⟩-use' =  ∗⊤-intro » ⇛-frameʳ (○-rec ○⇒-⊸ᵃ⟨⟩/⊸ᵃ⟨⟩-use') ᵘ»ᵃʰ
    ⊸ᵃ⟨⟩-use' {P˂ = ¡ᴾ _} {λ v → ¡ᴾ _}

--------------------------------------------------------------------------------
-- If we can use ⊸⟨ ⟩ᴾ without pure reduction, then we get a paradox

module _ {e : Expr∞ T}
  -- ⊸⟨⟩ᴾ-use without pure reduction
  (⊸⟨⟩ᴾ-use' :  ∀{P˂ Q˂˙} →
    P˂ .!  ∗  (P˂ ⊸⟨ e ⟩ᴾ Q˂˙)  ⊢[ ∞ ]⟨ e ⟩ᴾ λ v →  Q˂˙ v .!)
  where abstract

  -- We can strip ○ from ⊸⟨⟩ᴾ, using ⊸⟨⟩ᴾ-use'

  ○⇒-⊸⟨⟩ᴾ/⊸⟨⟩ᴾ-use' :  ○ ¡ᴾ (P˂ ⊸⟨ e ⟩ᴾ Q˂˙)  ⊢[ ∞ ]  P˂ ⊸⟨ e ⟩ᴾ Q˂˙
  ○⇒-⊸⟨⟩ᴾ/⊸⟨⟩ᴾ-use' =  ○⇒⊸⟨⟩ $ ⇒< ⊸⟨⟩ᴾ-use'

  -- Therefore, by ○-rec, we have any partial Hoare triple --- a paradox!

  horᴾ/⊸⟨⟩ᴾ-use' :  P  ⊢[ ∞ ]⟨ e ⟩ᴾ  Q˙
  horᴾ/⊸⟨⟩ᴾ-use' =  ∗⊤-intro » ⇛-frameʳ (○-rec ○⇒-⊸⟨⟩ᴾ/⊸⟨⟩ᴾ-use') ᵘ»ʰ
    ⊸⟨⟩ᴾ-use' {P˂ = ¡ᴾ _} {λ _ → ¡ᴾ _}

--------------------------------------------------------------------------------
-- If we can use ⊸⟨ ⟩ᵀ without level increment, then we get a paradox

module _ {e : Expr∞ T}
  -- ⊸⟨⟩ᵀ-use without level increment
  (⊸⟨⟩ᵀ-use' :  ∀{P˂ Q˂˙} →
    P˂ .!  ∗  (P˂ ⊸⟨ e ⟩ᵀ[ 0 ] Q˂˙)  ⊢[ ∞ ]⟨ e ⟩ᵀ[ 0 ] λ v →  Q˂˙ v .!)
  where abstract

  -- We can strip ○ from ⊸⟨⟩ᵀ, using ⊸⟨⟩ᵀ-use'

  ○⇒-⊸⟨⟩ᵀ/⊸⟨⟩ᵀ-use' :  ○ ¡ᴾ (P˂ ⊸⟨ e ⟩ᵀ[ 0 ] Q˂˙)  ⊢[ ∞ ]  P˂ ⊸⟨ e ⟩ᵀ[ 0 ] Q˂˙
  ○⇒-⊸⟨⟩ᵀ/⊸⟨⟩ᵀ-use' =  ○⇒⊸⟨⟩ $ ⇒< ⊸⟨⟩ᵀ-use'

  -- Therefore, by ○-rec, we have any total Hoare triple --- a paradox!

  horᵀ/⊸⟨⟩ᵀ-use' :  P  ⊢[ ∞ ]⟨ e ⟩ᵀ[ 0 ]  Q˙
  horᵀ/⊸⟨⟩ᵀ-use' =  ∗⊤-intro » ⇛-frameʳ (○-rec ○⇒-⊸⟨⟩ᵀ/⊸⟨⟩ᵀ-use') ᵘ»ʰ
    ⊸⟨⟩ᵀ-use' {P˂ = ¡ᴾ _} {λ _ → ¡ᴾ _}

--------------------------------------------------------------------------------
-- If we can use ⊸⟨ ⟩ᵀ with pure reduction, not level increment,
-- then we get a paradox

module _
  -- ⊸⟨⟩ᵀ-use with pure reduction, not level increment
  (⊸⟨⟩ᵀ-use⇒ᴾ :  ∀{e e' : Expr∞ T} {P˂ Q˂˙} →  e ⇒ᴾ e' →
    P˂ .!  ∗  (P˂ ⊸⟨ e' ⟩ᵀ[ 0 ] Q˂˙)  ⊢[ ∞ ]⟨ e ⟩ᵀ[ 0 ] λ v →  Q˂˙ v .!)
  where abstract

  -- We can strip ○ from ⊸⟨ loop ⟩ᵀ, using ⊸⟨⟩ᵀ-use

  ○⇒-⊸⟨loop⟩ᵀ/⊸⟨⟩ᵀ-use⇒ᴾ :  ○ ¡ᴾ (P˂ ⊸⟨ loop {T = T} ⟩ᵀ[ 0 ] Q˂˙)  ⊢[ ∞ ]
                              P˂ ⊸⟨ loop {T = T} ⟩ᵀ[ 0 ] Q˂˙
  ○⇒-⊸⟨loop⟩ᵀ/⊸⟨⟩ᵀ-use⇒ᴾ =  ○⇒⊸⟨⟩ $ ⇒< $ ⊸⟨⟩ᵀ-use⇒ᴾ {loop} (-, redᴾ refl)

  -- Therefore, by ○-rec, we have any total Hoare triple for the expression
  -- loop, which is a paradox: Although the total Hoare triple should ensure
  -- termination, loop does not terminate!

  horᵀ-loop/⊸⟨⟩ᵀ-use⇒ᴾ :  P  ⊢[ ∞ ]⟨ loop {T = T} ⟩ᵀ[ 0 ]  Q˙
  horᵀ-loop/⊸⟨⟩ᵀ-use⇒ᴾ =  ∗⊤-intro »
    ⇛-frameʳ (○-rec ○⇒-⊸⟨loop⟩ᵀ/⊸⟨⟩ᵀ-use⇒ᴾ) ᵘ»ʰ
    ⊸⟨⟩ᵀ-use⇒ᴾ {loop} {P˂ = ¡ᴾ _} {λ _ → ¡ᴾ _} (-, redᴾ refl)

--------------------------------------------------------------------------------
-- If we can use ⊸⟨ ⟩∞ without level increment, then we get a paradox

module _ {e : Expr∞ T}
  -- ⊸⟨⟩∞-use without level increment
  (⊸⟨⟩∞-use' :  ∀{P˂} →  P˂ .!  ∗  (P˂ ⊸[ 0 ]⟨ e ⟩∞)  ⊢[ ∞ ][ 0 ]⟨ e ⟩∞)
  where abstract

  -- We can strip ○ from ⊸⟨⟩∞, using ⊸⟨⟩∞-use'

  ○⇒-⊸⟨⟩∞/⊸⟨⟩∞-use' :  ○ ¡ᴾ (P˂ ⊸[ 0 ]⟨ e ⟩∞)  ⊢[ ∞ ]  P˂ ⊸[ 0 ]⟨ e ⟩∞
  ○⇒-⊸⟨⟩∞/⊸⟨⟩∞-use' =  ○⇒⊸⟨⟩∞ $ ⇒< ⊸⟨⟩∞-use'

  -- Therefore, by ○-rec, we have any total Hoare triple --- a paradox!

  ihor/⊸⟨⟩∞-use' :  P  ⊢[ ∞ ][ 0 ]⟨ e ⟩∞
  ihor/⊸⟨⟩∞-use' =  ∗⊤-intro »
    ⇛-frameʳ (○-rec ○⇒-⊸⟨⟩∞/⊸⟨⟩∞-use') ᵘ»ⁱʰ ⊸⟨⟩∞-use' {P˂ = ¡ᴾ _}
