--------------------------------------------------------------------------------
-- Fancy update on the bprrpw
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Symp.Model.Fupd.Bor where

open import Base.Level using (Level; _⊔ᴸ_; 1ᴸ)
open import Base.Func using (_$_; _▷_; _›_; id)
open import Base.Eq using (_≡_; refl)
open import Base.Bool using (𝔹; tt; ff)
open import Base.Option using (¿_; š_; ň)
open import Base.Prod using (_×_; _,_; -,_; _,-; -ᴵ,_; ∑-case)
open import Base.Nat using (ℕ)
open import Base.Ratp using (ℚ⁺; _/2⁺; ≈ᴿ⁺-refl; ≈ᴿ⁺-sym)
open import Symp.Logic.Prop using (Lft; SProp∞)
open import Symp.Model.ERA.Bor using (Envᴮᵒʳ)
open import Symp.Model.ERA.Glob using (jᴮᵒʳ; ∅ᴵⁿᴳ)
open import Symp.Model.Prop.Base using (SPropᵒ; _⊨✓_; _⊨_; ⊨_; ⌜_⌝ᵒ×_; _∗ᵒ_;
  _-∗ᵒ_; ∗ᵒ⇒∗ᵒ'; ∗ᵒ'⇒∗ᵒ; ∗ᵒ-Mono; ∗ᵒ-mono; ∗ᵒ-mono✓ˡ; ∗ᵒ-monoˡ; ∗ᵒ-mono✓ʳ;
  ∗ᵒ-monoʳ; ∗ᵒ-comm; ∗ᵒ-assocˡ; ∗ᵒ-assocʳ; ?∗ᵒ-comm; ∗ᵒ-pullʳ²; ∗ᵒ-pullʳ²ˡ;
  ∗ᵒ-pushʳ²ˡ; ?∗ᵒ-intro; ∗ᵒ?-intro; ∗ᵒ-elimˡ; ∗ᵒ-elimʳ; ∃ᵒ∗ᵒ-out; -∗ᵒ-introʳ;
  -∗ᵒ-intro'; -∗ᵒ-applyˡ; -∗ᵒ-applyʳ; □ᵒ-elim; dup-□ᵒ; ⤇ᴱ⟨⟩-mono✓; ⤇ᴱ⟨⟩-mono;
  ⤇ᴱ⟨⟩-param; ⤇ᴱ⟨⟩-eatʳ)
open import Symp.Model.Prop.Basic using (⸨_⸩ᴮ; ⸨⸩ᴮ-Mono)
open import Symp.Model.Prop.Smry using (Smry; Smry-0; Smry-add-š; Smry-rem-<;
  Smry-upd)
open import Symp.Model.Prop.Lft using ([_]ᴸ⟨_⟩ᵒ; †ᴸᵒ_; []ᴸ⟨⟩ᵒ-resp;
  []ᴸ⟨⟩ᵒ-merge-/2; []ᴸ⟨⟩ᵒ-split-/2; dup-†ᴸᵒ; []ᴸ⟨⟩ᵒ-†ᴸᵒ-no)
open import Symp.Model.Prop.Bor using (Borᵐ; &ᵐ⟨_⟩ᵒ_; Oborᵐ; ⅋ᵐ⟨_⟩ᵒ_; Lend;
  ⟨†_⟩ᵒ_; &ᵐᵒ-new'; &ᵐᵒ-make; Borᵐ-open'; Oborᵐ-close'; Lend-back')
open import Symp.Model.Prop.Basic using (⸨⸩ᴮ-Mono)
open import Symp.Model.Prop.Interp using (⸨_⸩; ⸨⸩-ᴮ⇒; ⸨⸩-Mono)
open import Symp.Model.Prop.Sound using (⊢-sem)
open import Symp.Model.Fupd.Base using ([_]⇛ᵍ¹_; ⇛ᵍ-mono✓; ⇛ᵍ-mono; ⊨✓⇒⊨-⇛ᵍ;
  ⇛ᵍ¹-make; ⇛ᵍ¹-intro; ⇛ᵍ-eatˡ)

private variable
  ł :  Level
  i :  ℕ
  p :  ℚ⁺
  pˇ :  ¿ ℚ⁺
  b :  𝔹
  α :  Lft
  P P' Q :  SProp∞
  Pᵒ :  SPropᵒ ł

--------------------------------------------------------------------------------
-- Fancy update on Borᴱᴿᴬ

-- Lineᴮᵒʳ :  Line for Invᴮᵒʳ

Lineᴮᵒʳ :  ¿ ℚ⁺ × 𝔹 × Lft × SProp∞ × SProp∞ →  SPropᵒ 1ᴸ
Lineᴮᵒʳ (-, ff , α , _) =  †ᴸᵒ α
Lineᴮᵒʳ (ň , tt , -, P , Q) =  ⸨ P ⸩ ∗ᵒ (⸨ P ⸩ -∗ᵒ ⸨ Q ⸩)
Lineᴮᵒʳ (š p , tt , α , P , Q) =  [ α ]ᴸ⟨ p /2⁺ ⟩ᵒ ∗ᵒ (⸨ P ⸩ -∗ᵒ ⸨ Q ⸩)

-- Invᴮᵒʳ :  Invariant for Borᴱᴿᴬ

Invᴮᵒʳ :  Envᴮᵒʳ →  SPropᵒ 1ᴸ
Invᴮᵒʳ (E˙ , n) =  Smry (λ _ → Lineᴮᵒʳ) E˙ n

-- Fancy update on InvᴱᴿᴬBorᴱᴿᴬ

infix 3 ⇛ᴮᵒʳ_
⇛ᴮᵒʳ_ :  SPropᵒ ł →  SPropᵒ (1ᴸ ⊔ᴸ ł)
⇛ᴮᵒʳ Pᵒ =  [ jᴮᵒʳ , Invᴮᵒʳ ]⇛ᵍ¹ Pᵒ

abstract

  -- Get Invᴮᵒʳ (∅ᴵⁿᴳ jᴮᵒʳ) for free

  Invᴮᵒʳ-∅ :  ⊨ Invᴮᵒʳ (∅ᴵⁿᴳ jᴮᵒʳ)
  Invᴮᵒʳ-∅ =  Smry-0

  -- Introduce ⇛ᴮᵒʳ

  ⇛ᴮᵒʳ-intro :  Pᵒ  ⊨ ⇛ᴮᵒʳ  Pᵒ
  ⇛ᴮᵒʳ-intro =  ⇛ᵍ¹-intro

  -- Get &ᵐ⟨ α ⟩ᵒ P and ⟨† α ⟩ᵒ P by storing ⸨ P ⸩

  &ᵐᵒ-new :  ⸨ P ⸩  ⊨ ⇛ᴮᵒʳ  &ᵐ⟨ α ⟩ᵒ P  ∗ᵒ  ⟨† α ⟩ᵒ P
  &ᵐᵒ-new {P} =  ∗ᵒ?-intro (-∗ᵒ-intro' (⸨⸩-Mono {P}) λ _ → id) › ⇛ᵍ¹-make $
    ?∗ᵒ-intro &ᵐᵒ-new' › ⤇ᴱ⟨⟩-eatʳ › ⤇ᴱ⟨⟩-mono (λ _ → ∗ᵒ-monoʳ Smry-add-š) ›
    ⤇ᴱ⟨⟩-param

  -- Get ⸨ P ⸩ out of Lineᴮᵒʳ with ň using [ α ]ᴸ⟨ p ⟩ᵒ

  []ᴸ⟨⟩ᵒ-open :  [ α ]ᴸ⟨ p ⟩ᵒ  ∗ᵒ  Lineᴮᵒʳ (ň , b , α , P , Q)  ⊨✓
                   ⌜ b ≡ tt ⌝ᵒ×  [ α ]ᴸ⟨ p ⟩ᵒ  ∗ᵒ  ⸨ P ⸩  ∗ᵒ (⸨ P ⸩ -∗ᵒ ⸨ Q ⸩)
  []ᴸ⟨⟩ᵒ-open {b = tt} _ =  refl ,_
  []ᴸ⟨⟩ᵒ-open {b = ff} ✓∙ =  []ᴸ⟨⟩ᵒ-†ᴸᵒ-no ✓∙ › λ ()

  -- Take ⸨ P ⸩ out using Borᵐ and [ α ]ᴸ⟨ p ⟩ᵒ,
  -- getting [ α ]ᴸ⟨ p /2⁺ ⟩ᵒ and Oborᵐ i α p P in return

  Borᵐ-open :  [ α ]ᴸ⟨ p ⟩ᵒ  ∗ᵒ  Borᵐ i α P  ⊨ ⇛ᴮᵒʳ
                 ⸨ P ⸩  ∗ᵒ  [ α ]ᴸ⟨ p /2⁺ ⟩ᵒ  ∗ᵒ  Oborᵐ i α p P
  Borᵐ-open =  ⇛ᵍ¹-make $ ∗ᵒ-assocʳ › ?∗ᵒ-comm › ∗ᵒ-monoˡ Borᵐ-open' ›
    -- Obor∗[α]p∗Inv → Obor∗[α]p∗Line∗Inv → → → Obor∗[α]p∗P∗(P-∗Q)∗Inv → → →
    -- Obor∗[α]p/2∗[α]p/2∗P∗(P-∗Q)∗Inv → → → Obor∗[α]p/2∗P∗([α]p/2∗(P-∗Q))∗Inv →
    -- Obor∗[α]p/2∗P∗Inv → → (Obor∗[α]p/2∗P)∗Inv → → (P∗[α]p/2∗Obor)∗Inv
    ⤇ᴱ⟨⟩-eatʳ › ⤇ᴱ⟨⟩-mono✓ (λ (i<n , b , Q , Ei≡) ✓∙ → ∗ᵒ-mono✓ʳ (λ ✓∙ →
      ∗ᵒ-monoʳ (Smry-rem-< i<n Ei≡) › ∗ᵒ-assocˡ ›
      ∗ᵒ-mono✓ˡ ([]ᴸ⟨⟩ᵒ-open {b = b}) ✓∙ › ∃ᵒ∗ᵒ-out › ∑-case λ{ refl →
      ∗ᵒ-assocʳ › ∗ᵒ-monoʳ ∗ᵒ-assocʳ › ∗ᵒ-monoˡ []ᴸ⟨⟩ᵒ-split-/2 › ∗ᵒ-assocʳ ›
      ∗ᵒ-monoʳ (?∗ᵒ-comm › ∗ᵒ-monoʳ (∗ᵒ-assocˡ › Smry-upd)) › ∗ᵒ-assocˡ }) ✓∙ ›
      ∗ᵒ-assocˡ › ∗ᵒ-monoˡ $ ?∗ᵒ-comm › ∗ᵒ-pullʳ²) › ⤇ᴱ⟨⟩-param

  -- Take ⸨ P ⸩ out using &ᵐ⟨ α ⟩ᵒ P and [ α ]ᴸ⟨ p ⟩ᵒ,
  -- getting ⅋ᵐ⟨ α , p ⟩ᵒ P in return

  &ᵐᵒ-open :  [ α ]ᴸ⟨ p ⟩ᵒ  ∗ᵒ  &ᵐ⟨ α ⟩ᵒ P  ⊨ ⇛ᴮᵒʳ  ⸨ P ⸩  ∗ᵒ  ⅋ᵐ⟨ α , p ⟩ᵒ P
  &ᵐᵒ-open {p = p} =  ∗ᵒ⇒∗ᵒ' ›
    λ{ (-, -, ∙⊑ , [α]b , -, Q , -ᴵ, -, (Q∗R⊢P , Q∗P⊢R) , □Q∗BorRc) →
    let MonoQ = ⸨⸩ᴮ-Mono {Q} in ∗ᵒ'⇒∗ᵒ (-, -, ∙⊑ , [α]b , □Q∗BorRc) ▷
    -- [α]p∗□Q∗Bor → □Q∗[α]p∗Bor → → □Q∗R∗[α]p/2∗Obor → → → → →
    -- Q∗Q∗R∗[α]p/2∗Obor → → → P∗Q∗[α]p/2∗Obor → P∗⅋
    ?∗ᵒ-comm ▷ ∗ᵒ-monoʳ Borᵐ-open ▷ ⇛ᵍ-eatˡ ▷ ⇛ᵍ-mono✓ (λ ✓∙ →
    ∗ᵒ-monoˡ (dup-□ᵒ MonoQ ›
      ∗ᵒ-mono (□ᵒ-elim MonoQ › ⸨⸩-ᴮ⇒ {Q}) (□ᵒ-elim MonoQ)) › ∗ᵒ-assocʳ ›
    ∗ᵒ-monoʳ ?∗ᵒ-comm › ∗ᵒ-assocˡ › ∗ᵒ-mono✓ˡ (⊢-sem Q∗R⊢P) ✓∙ ›
    ∗ᵒ-monoʳ λ big → -, p , Q , -ᴵ, -, ≈ᴿ⁺-refl {p} , Q∗P⊢R , big) }

  -- Get [ α ]ᴸ⟨ p ⟩ᵒ out of Lineᴮᵒʳ with š p using [ α ]ᴸ⟨ p /2⁺ ⟩ᵒ

  []ᴸ⟨/2⟩ᵒ-close :  [ α ]ᴸ⟨ p /2⁺ ⟩ᵒ  ∗ᵒ  Lineᴮᵒʳ (š p , b , α , P , Q)  ⊨✓
                      ⌜ b ≡ tt ⌝ᵒ×  ([ α ]ᴸ⟨ p ⟩ᵒ  ∗ᵒ  (⸨ P ⸩ -∗ᵒ ⸨ Q ⸩))
  []ᴸ⟨/2⟩ᵒ-close {b = tt} _ big =  refl ,
    big ▷ ∗ᵒ-assocˡ ▷ ∗ᵒ-monoˡ []ᴸ⟨⟩ᵒ-merge-/2
  []ᴸ⟨/2⟩ᵒ-close {b = ff} ✓∙ =  []ᴸ⟨⟩ᵒ-†ᴸᵒ-no ✓∙ › λ ()

  -- Retrieve [ α ]ᴸ⟨ p ⟩ᵒ and Borᵐ i α P'
  -- using ⸨ P' ⸩, ⸨ P' ⸩ -∗ ⸨ P ⸩, [ α ]ᴸ⟨ p /2⁺ ⟩ᵒ and Oborᵐ i α p P

  Oborᵐ-close-sub :
    ⸨ P' ⸩  ∗ᵒ  (⸨ P' ⸩ -∗ᵒ ⸨ P ⸩)  ∗ᵒ  [ α ]ᴸ⟨ p /2⁺ ⟩ᵒ  ∗ᵒ  Oborᵐ i α p P
      ⊨ ⇛ᴮᵒʳ  [ α ]ᴸ⟨ p ⟩ᵒ  ∗ᵒ  Borᵐ i α P'
  Oborᵐ-close-sub {P = P} =  ∗ᵒ-assocˡ › ∗ᵒ-assocˡ › ⇛ᵍ¹-make $ ∗ᵒ-assocʳ ›
    ?∗ᵒ-comm › ∗ᵒ-monoˡ Oborᵐ-close' › ⤇ᴱ⟨⟩-eatʳ ›
    ⤇ᴱ⟨⟩-mono✓ (λ (i<n , b , Q , Ei≡) ✓∙ → -- Let PP be P'∗(P'-∗P)
      -- Bor∗(PP∗[α]p/2)∗Inv → Bor∗(PP∗[α]p/2)∗Line∗Inv → → →
      -- Bor∗([α]p/2∗Line)∗PP∗Inv → → Bor∗([α]p∗(P-∗Q))∗PP∗Inv → → →
      -- Bor∗[α]p∗(P'∗(P-∗Q)∗(P'-∗P))∗Inv → → →
      -- Bor∗[α]p∗(P'∗(P'-∗Q))∗Inv → Bor∗[α]p∗Inv → → ([α]p∗Bor)∗Inv
      ∗ᵒ-mono✓ʳ (λ ✓∙ → ∗ᵒ-monoʳ (Smry-rem-< i<n Ei≡) › ∗ᵒ-assocʳ › ∗ᵒ-pushʳ²ˡ ›
      ∗ᵒ-assocˡ › ∗ᵒ-mono✓ˡ ([]ᴸ⟨/2⟩ᵒ-close {b = b}) ✓∙ › ∃ᵒ∗ᵒ-out › ∑-case
      λ{ refl → ∗ᵒ-assocʳ › ∗ᵒ-monoʳ $ ∗ᵒ-assocˡ ›
        ∗ᵒ-monoˡ (?∗ᵒ-comm › ∗ᵒ-monoʳ $ -∗ᵒ-introʳ λ ✓∙ → ∗ᵒ-assocʳ ›
        ∗ᵒ-mono✓ʳ (-∗ᵒ-applyʳ $ ⸨⸩-Mono {P}) ✓∙ › -∗ᵒ-applyʳ (⸨⸩-Mono {Q}) ✓∙) ›
        Smry-upd }) ✓∙ › ∗ᵒ-assocˡ › ∗ᵒ-monoˡ ∗ᵒ-comm) ›
    ⤇ᴱ⟨⟩-param

  -- Retrieve [ α ]ᴸ⟨ p ⟩ᵒ and &ᵐ⟨ α ⟩ᵒ P using ⸨ P ⸩ and ⅋ᵐ⟨ α , p ⟩ᵒ P

  ⅋ᵐᵒ-close-sub :  ⸨ P' ⸩  ∗ᵒ  (⸨ P' ⸩ -∗ᵒ ⸨ P ⸩)  ∗ᵒ  ⅋ᵐ⟨ α , p ⟩ᵒ P  ⊨ ⇛ᴮᵒʳ
                     [ α ]ᴸ⟨ p ⟩ᵒ  ∗ᵒ  &ᵐ⟨ α ⟩ᵒ P'
  ⅋ᵐᵒ-close-sub {P = P} {p = p} =  ∗ᵒ-assocˡ › ∗ᵒ⇒∗ᵒ' › λ{ (-, -, ∙⊑ , PPb ,
    -, q , Q , -ᴵ, -, p≈q , Q∗P⊢R , Q∗[α]∗OborRc) →
    ∗ᵒ'⇒∗ᵒ (-, -, ∙⊑ , PPb , Q∗[α]∗OborRc) ▷ -- Let PP be P'∗(P'-∗P)
    -- PP∗Q∗[α]q/2∗Obor → → → →
    -- P'∗(Q∗(P'-∗P))∗[α]q/2∗Obor → → → P'∗(P'-∗R)∗[α]q/2∗Obor → → [α]q∗&
    ⊨✓⇒⊨-⇛ᵍ λ ✓∙ → ∗ᵒ-monoʳ (∗ᵒ-monoˡ $ ⸨⸩-ᴮ⇒ {Q}) › ∗ᵒ-assocʳ ›
    ∗ᵒ-monoʳ (∗ᵒ-assocˡ › ∗ᵒ-monoˡ $ ∗ᵒ-comm › -∗ᵒ-introʳ λ ✓∙ → ∗ᵒ-assocʳ ›
      ∗ᵒ-mono✓ʳ (-∗ᵒ-applyʳ $ ⸨⸩-Mono {P}) ✓∙ › ⊢-sem Q∗P⊢R ✓∙) ›
    Oborᵐ-close-sub › ⇛ᵍ-mono $
      ∗ᵒ-mono ([]ᴸ⟨⟩ᵒ-resp $ ≈ᴿ⁺-sym {p} {q} p≈q) &ᵐᵒ-make }

  -- Get ⸨ P ⸩ out of Lineᴮᵒʳ with tt using †ᴸᵒ α

  †ᴸᵒ-back :  †ᴸᵒ α  ∗ᵒ  Lineᴮᵒʳ (pˇ , tt , α , P , Q)  ⊨✓  ⸨ Q ⸩
  †ᴸᵒ-back {pˇ = ň} {Q = Q} ✓∙ =
    ∗ᵒ-mono✓ʳ (-∗ᵒ-applyˡ $ ⸨⸩-Mono {Q}) ✓∙ › ∗ᵒ-elimʳ $ ⸨⸩-Mono {Q}
  †ᴸᵒ-back {pˇ = š _} ✓∙ =  ?∗ᵒ-comm › ∗ᵒ-assocˡ ›
    ∗ᵒ-mono✓ˡ []ᴸ⟨⟩ᵒ-†ᴸᵒ-no ✓∙ › ∗ᵒ⇒∗ᵒ' › λ ()

  -- Get ⸨ P ⸩ back from Lend i α P using †ᴸᵒ α

  Lend-back :  †ᴸᵒ α  ∗ᵒ  Lend i α P  ⊨ ⇛ᴮᵒʳ  ⸨ P ⸩
  Lend-back =  ⇛ᵍ¹-make $ ∗ᵒ-assocʳ › ?∗ᵒ-comm › ∗ᵒ-monoˡ Lend-back' ›
    ⤇ᴱ⟨⟩-eatʳ › ⤇ᴱ⟨⟩-mono✓ (λ (i<n , pˇ , Q , Ei≡) ✓∙ →
      -- -∗†∗Inv → → †∗Inv → (†∗†)∗Line∗Inv → †∗†∗Line∗Inv → →
      -- (†∗Line)∗†∗Inv → P∗†∗Inv → P∗†∗Inv → P∗Inv
      ∗ᵒ-elimʳ ∗ᵒ-Mono › ∗ᵒ-mono dup-†ᴸᵒ (Smry-rem-< i<n Ei≡) › ∗ᵒ-assocʳ ›
      ∗ᵒ-monoʳ ?∗ᵒ-comm › ∗ᵒ-assocˡ › ∗ᵒ-mono✓ˡ (†ᴸᵒ-back {pˇ = pˇ}) ✓∙ ›
      ∗ᵒ-monoʳ Smry-upd) › ⤇ᴱ⟨⟩-param

  -- Get ⸨ P ⸩ back from ⟨† α ⟩ᵒ P using †ᴸᵒ α

  ⟨†⟩ᵒ-back :  †ᴸᵒ α  ∗ᵒ  ⟨† α ⟩ᵒ P  ⊨ ⇛ᴮᵒʳ  ⸨ P ⸩
  ⟨†⟩ᵒ-back =  ∗ᵒ⇒∗ᵒ' › λ{ (-, -, ∙⊑ , †αb , -, Q , -ᴵ, -, Q∗R⊢P , Q∗LendRc) →
    ∗ᵒ'⇒∗ᵒ (-, -, ∙⊑ , †αb , Q∗LendRc) ▷ ?∗ᵒ-comm ▷ ∗ᵒ-monoʳ Lend-back ▷
    ⇛ᵍ-eatˡ ▷ ⇛ᵍ-mono✓ (λ ✓∙ → ∗ᵒ-monoˡ (⸨⸩-ᴮ⇒ {Q}) › ⊢-sem Q∗R⊢P ✓∙) }
