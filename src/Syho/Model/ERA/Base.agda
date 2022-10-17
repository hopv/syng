--------------------------------------------------------------------------------
-- Environmental resource algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Syho.Model.ERA.Base where

open import Base.Level using (Level; _⊔ᴸ_; ṡᴸ_; Up; ↑_; ↓)
open import Base.Func using (_$_; id; _▷_; flip; _∘_)
open import Base.Few using (⊤; ⊤₀)
open import Base.Eq using (_≡_; refl)
open import Base.Prod using (∑-syntax; _×_; π₀; π₁; _,_; -,_; curry)
open import Base.Nat using (ℕ)
open import Base.List using (List; []; _∷_; _$ᴸ_; _$ⁱᴸ_; _$ⁱᴸ⟨_⟩_)

--------------------------------------------------------------------------------
-- ERA :  Environmental resource algebra

-- The ERA is similar to the (unital) resource algebra (RA) used in Iris, but
-- the ERA has the notion of environment Env, and the ERA's validity predicate ✓
-- inputs not only the resource but also the environment.
-- You can view an environment of an ERA as analogous to an authoritative state
-- ● a of the Auth RA in Iris.
-- The environment simplifies the proof of various properties (especially
-- resource updates ↝), thanks to the fact that we always stably have a single
-- environment separately from resources.

record  ERA łᴿ ł≈ łᴱ ł✓ : Set (ṡᴸ (łᴿ ⊔ᴸ ł≈ ⊔ᴸ łᴱ ⊔ᴸ ł✓))  where
  ------------------------------------------------------------------------------
  -- Fields
  infix 4 _≈_
  infixr 7 _∙_
  infix 4 _✓_
  infix 0 ◠˜_
  infixr -1 _◇˜_
  field
    ----------------------------------------------------------------------------
    -- Main components

    -- Res :  Resource
    Res :  Set łᴿ

    -- ≈ :  Equivalence of resources
    _≈_ :  Res →  Res →  Set ł≈

    -- ∙ :  Product of resources, used for modeling the separating conjunction ∗
    _∙_ :  Res →  Res →  Res

    -- ε :  Unit resource
    ε :  Res

    -- ⌞ ⌟ :  Core of a resource, used for modeling the persistence modality □
    ⌞_⌟ :  Res →  Res

    -- Env :  Environment
    Env :  Set łᴱ

    -- ✓ :  Validity of a pair of an environment and a resource
    _✓_ :  Env →  Res →  Set ł✓

    ----------------------------------------------------------------------------
    -- On ≈

    -- ≈ is reflexive, symmetric and transitive

    refl˜ :  ∀{a} →  a ≈ a
    ◠˜_ :  ∀{a b} →  a ≈ b →  b ≈ a
    _◇˜_ :  ∀{a b c} →  a ≈ b →  b ≈ c →  a ≈ c

    ----------------------------------------------------------------------------
    -- On ∙

    -- ∙ preserves ≈, and is unital with the unit ε, commutative and associative
    -- w.r.t. ≈

    ∙-congˡ :  ∀{a b c} →  a ≈ b →  a ∙ c ≈ b ∙ c
    ∙-unitˡ :  ∀{a} →  ε ∙ a ≈ a
    ∙-comm :  ∀{a b} →  a ∙ b ≈ b ∙ a
    ∙-assocʳ :  ∀{a b c} →  (a ∙ b) ∙ c ≈ a ∙ (b ∙ c)

    ----------------------------------------------------------------------------
    -- On ⌞⌟

    -- ⌞⌟ preserves ≈

    ⌞⌟-cong :  ∀{a b} →  a ≈ b →  ⌞ a ⌟ ≈ ⌞ b ⌟

    -- When ⌞⌟'s argument gets added, ⌞⌟'s result gets added

    ⌞⌟-add :  ∀{a b} →  ∑ a' ,  ⌞ a ∙ b ⌟  ≈ a' ∙ ⌞ b ⌟

    -- ⌞ a ⌟ is absorbed by a

    ⌞⌟-unitˡ :  ∀{a} →  ⌞ a ⌟ ∙ a  ≈  a

    -- ⌞⌟ is idempotent

    ⌞⌟-idem :  ∀{a} →  ⌞ ⌞ a ⌟ ⌟ ≈ ⌞ a ⌟

    ----------------------------------------------------------------------------
    -- On ✓

    -- ✓ respects ≈

    ✓-resp :  ∀{E a b} →  a ≈ b →  E ✓ a →  E ✓ b

    -- ✓ is kept after a resource is removed

    ✓-rem :  ∀{E a b} →  E ✓ a ∙ b →  E ✓ b

  private variable
    ł :  Level
    X Y :  Set ł
    f :  Y → X
    a a' b b' c d :  Res
    b˙ b'˙ :  X → Res
    E E' F F' :  Env
    F˙ :  X → Env
    Fb˙ :  X → Env × Res

  abstract
    ----------------------------------------------------------------------------
    -- On ≈

    -->  ◠˜_ :  a ≈ b →  b ≈ a
    -->  _◇˜_ :  a ≈ b →  b ≈ c →  a ≈ c

    -- ≈ is reflexive

    -->  refl˜ :  a ≈ a

    ≡⇒≈ :  a ≡ b →  a ≈ b
    ≡⇒≈ refl =  refl˜

    ----------------------------------------------------------------------------
    -- On ∙

    -->  ∙-comm :  a ∙ b ≈ b ∙ a

    -- ∙ preserves ≈

    -->  ∙-congˡ :  a ≈ b →  a ∙ c ≈ b ∙ c

    ∙-congʳ :  a ≈ b →  c ∙ a ≈ c ∙ b
    ∙-congʳ a≈b =  ∙-comm ◇˜ ∙-congˡ a≈b ◇˜ ∙-comm

    ∙-cong :  a ≈ b →  c ≈ d →  a ∙ c ≈ b ∙ d
    ∙-cong a≈b c≈d =  ∙-congˡ a≈b ◇˜ ∙-congʳ c≈d

    -- ∙ is unital

    -->  ∙-unitˡ :  ε ∙ a ≈ a

    ∙-unitʳ :  a ∙ ε ≈ a
    ∙-unitʳ =  ∙-comm ◇˜ ∙-unitˡ

    -- ∙ is associative

    -->  ∙-assocʳ :  (a ∙ b) ∙ c ≈ a ∙ (b ∙ c)

    ∙-assocˡ :  a ∙ (b ∙ c) ≈ (a ∙ b) ∙ c
    ∙-assocˡ =  ◠˜ ∙-assocʳ

    ----------------------------------------------------------------------------
    -- On ✓

    -->  ✓-rem :  E ✓ a ∙ b →  E ✓ b

    ----------------------------------------------------------------------------
    -- On ⌞⌟

    -->  ⌞⌟-cong :  a ≈ b →  ⌞ a ⌟ ≈ ⌞ b ⌟

    -->  ⌞⌟-add :  ∑ a' ,  ⌞ a ∙ b ⌟  ≈ a' ∙ ⌞ b ⌟

    -->  ⌞⌟-idem :  ⌞ ⌞ a ⌟ ⌟ ≈ ⌞ a ⌟

    -- ⌞ a ⌟ is absorbed by a

    -->  ⌞⌟-unitˡ :  ⌞ a ⌟ ∙ a  ≈  a

    ⌞⌟-unitʳ :  a ∙ ⌞ a ⌟ ≈ a
    ⌞⌟-unitʳ =  ∙-comm ◇˜ ⌞⌟-unitˡ

    -- ⌞ ⌟ can be duplicated

    ⌞⌟-dup :  ⌞ a ⌟ ∙ ⌞ a ⌟ ≈ ⌞ a ⌟
    ⌞⌟-dup =  ∙-congˡ (◠˜ ⌞⌟-idem) ◇˜ ⌞⌟-unitˡ

    -- ⌞ ε ⌟ is ε

    ⌞⌟-ε :  ⌞ ε ⌟ ≈ ε
    ⌞⌟-ε =  ◠˜ ∙-unitʳ ◇˜ ⌞⌟-unitˡ

  ------------------------------------------------------------------------------
  -- ⊑ :  Derived pre-order

  abstract

    infix 4 _⊑_
    _⊑_ :  Res → Res → Set (łᴿ ⊔ᴸ ł≈)
    a ⊑ b =  ∑ c ,  c ∙ a  ≈  b

    -- Unfold ⊑

    ⊑≡ :  _⊑_  ≡  λ a b → ∑ c , c ∙ a ≈ b
    ⊑≡ =  refl

    -- ⊑ is reflexive

    ≈⇒⊑ :  a ≈ b →  a ⊑ b
    ≈⇒⊑ a≈b =  ε , ∙-unitˡ ◇˜ a≈b

    ⊑-refl :  a ⊑ a
    ⊑-refl =  ≈⇒⊑ refl˜

    -- ⊑ is transitive

    ⊑-trans :  a ⊑ b →  b ⊑ c →  a ⊑ c
    ⊑-trans (d , d∙a≈b) (e , e∙b≈c) =  d ∙ e ,
      ∙-congˡ ∙-comm ◇˜ ∙-assocʳ ◇˜ ∙-congʳ d∙a≈b ◇˜ e∙b≈c

    -- ⊑ respects ≈

    ⊑-resp :  a ≈ b →  c ≈ d →  a ⊑ c →  b ⊑ d
    ⊑-resp a≈b c≈d (e , e∙a≈c) =  e , ∙-congʳ (◠˜ a≈b) ◇˜ e∙a≈c ◇˜ c≈d

    ⊑-respˡ :  a ≈ b →  a ⊑ c →  b ⊑ c
    ⊑-respˡ a≈b a⊑c =  ⊑-resp a≈b refl˜ a⊑c

    ⊑-respʳ :  a ≈ b →  c ⊑ a →  c ⊑ b
    ⊑-respʳ b≈c a⊑b =  ⊑-resp refl˜ b≈c a⊑b

    -- ε is the minimum

    ε-min :  ε ⊑ a
    ε-min =  -, ∙-unitʳ

    -- ∙ is increasing

    ∙-incrˡ :  a  ⊑  b ∙ a
    ∙-incrˡ =  -, refl˜

    ∙-incrʳ :  a  ⊑  a ∙ b
    ∙-incrʳ =  ⊑-respʳ ∙-comm ∙-incrˡ

    -- Monotonicity of ✓, ∙ and ⌞⌟

    ✓-mono :  a ⊑ b →  E ✓ b →  E ✓ a
    ✓-mono (c , c∙a≈b) E✓b =  E✓b ▷ ✓-resp (◠˜ c∙a≈b) ▷ ✓-rem

    ∙-monoˡ :  a ⊑ b →  a ∙ c  ⊑  b ∙ c
    ∙-monoˡ (d , d∙a≈b) =  d , ∙-assocˡ ◇˜ ∙-congˡ d∙a≈b

    ∙-monoʳ :  a ⊑ b →  c ∙ a  ⊑  c ∙ b
    ∙-monoʳ a⊑b =  ⊑-resp ∙-comm ∙-comm $ ∙-monoˡ a⊑b

    ∙-mono :  a ⊑ b →  c ⊑ d →  a ∙ c  ⊑  b ∙ d
    ∙-mono a⊑b c⊑d =  ⊑-trans (∙-monoˡ a⊑b) (∙-monoʳ c⊑d)

    ⌞⌟-mono :  a ⊑ b →  ⌞ a ⌟ ⊑ ⌞ b ⌟
    ⌞⌟-mono (c , c∙a≈b)  with ⌞⌟-add {c}
    … | c' , ⌞c∙a⌟≈'∙⌞a⌟ =  c' , ◠˜ ⌞c∙a⌟≈'∙⌞a⌟ ◇˜ ⌞⌟-cong c∙a≈b

    -- ⌞ ⌟ is decreasing

    ⌞⌟-decr :  ⌞ a ⌟ ⊑ a
    ⌞⌟-decr =  ⊑-respʳ ⌞⌟-unitˡ ∙-incrʳ

    -- ⌞ ⌟ and ∙ commute weakly

    ⌞⌟-∙ :  ⌞ a ⌟ ∙ ⌞ b ⌟ ⊑ ⌞ a ∙ b ⌟
    ⌞⌟-∙ =  ⊑-respʳ ⌞⌟-dup $ ∙-mono (⌞⌟-mono ∙-incrʳ) (⌞⌟-mono ∙-incrˡ)

    -- E ✓ a implies E ✓ ⌞ a ⌟

    ✓-⌞⌟ :  E ✓ a →  E ✓ ⌞ a ⌟
    ✓-⌞⌟ ✓a =  ✓-mono ⌞⌟-decr ✓a

  ------------------------------------------------------------------------------
  -- [∙] :  Iterated resource product

  [∙] :  List Res →  Res
  [∙] [] =  ε
  [∙] (a ∷ as) =  a ∙ [∙] as

  -- Syntax for [∙] $ᴸ / $ⁱᴸ

  infix 8 [∙∈]-syntax [∙∈ⁱ]-syntax [∙∈ⁱ⟨⟩]-syntax
  [∙∈] [∙∈]-syntax :  (X → Res) →  List X →  Res
  [∙∈] a˙ xs =  [∙] $ a˙ $ᴸ xs
  [∙∈]-syntax =  [∙∈]
  [∙∈ⁱ] [∙∈ⁱ]-syntax :  (ℕ × X → Res) →  List X →  Res
  [∙∈ⁱ] a˙ xs =  [∙] $ curry a˙ $ⁱᴸ xs
  [∙∈ⁱ]-syntax =  [∙∈ⁱ]
  [∙∈ⁱ⟨⟩] [∙∈ⁱ⟨⟩]-syntax :  (ℕ × X → Res) →  ℕ →  List X →  Res
  [∙∈ⁱ⟨⟩] a˙ k xs =  [∙] $ curry a˙ $ⁱᴸ⟨ k ⟩ xs
  [∙∈ⁱ⟨⟩]-syntax =  [∙∈ⁱ⟨⟩]
  syntax [∙∈]-syntax (λ x → a) xs =  [∙ x ∈ xs ] a
  syntax [∙∈ⁱ]-syntax (λ ix → a) xs =  [∙ ix ∈ⁱ xs ] a
  syntax [∙∈ⁱ⟨⟩]-syntax (λ ix → a) k xs =  [∙ ix ∈ⁱ⟨ k ⟩ xs ] a

  ------------------------------------------------------------------------------
  -- ↝ :  Environmental resource update

  infix 2 _↝_

  -- (E , a) ↝ Fb˙ :  The environment-resource pair (E , a) can be updated into
  --                  Fb˙ x for some x, regardless the frame resource c

  _↝_ :  ∀{X : Set ł} →  Env × Res →  (X →  Env × Res) →  Set (łᴿ ⊔ᴸ ł✓ ⊔ᴸ ł)
  (E , a) ↝ Fb˙ =  ∀ c →  E ✓ a ∙ c →  ∑ x ,  let (F , b) = Fb˙ x in  F ✓ b ∙ c

  abstract

    -- Modify ↝ with ≈

    ↝-mono :  a ⊑ a'  →   (∀{x} → b'˙ x ⊑ b˙ x)  →
      (E , a) ↝ (λ x → F˙ x , b˙ x)  →   (E , a') ↝ λ x → F˙ x , b'˙ x
    ↝-mono a⊑a' b'x⊑bx Ea↝Fxbx c˙ E✓a'∙c
      with Ea↝Fxbx c˙ $ ✓-mono (∙-monoˡ a⊑a') E✓a'∙c
    … | x , Fx✓bx∙c =  x , ✓-mono (∙-monoˡ b'x⊑bx) Fx✓bx∙c

    ↝-resp :  a ≈ a'  →   (∀{x} → b˙ x ≈ b'˙ x)  →
      (E , a) ↝ (λ x → F˙ x , b˙ x)  →   (E , a') ↝ λ x → F˙ x , b'˙ x
    ↝-resp a≈a' bx≈b'x =  ↝-mono (≈⇒⊑ a≈a') (≈⇒⊑ $ ◠˜ bx≈b'x)

    ↝-monoˡ :  a ⊑ a'  →
      (E , a) ↝ (λ x → F˙ x , b˙ x)  →   (E , a') ↝ λ x → F˙ x , b˙ x
    ↝-monoˡ a⊑a' =  ↝-mono a⊑a' ⊑-refl

    ↝-respˡ :  a ≈ a'  →
      (E , a) ↝ (λ x → F˙ x , b˙ x)  →   (E , a') ↝ λ x → F˙ x , b˙ x
    ↝-respˡ a≈a' =  ↝-monoˡ $ ≈⇒⊑ a≈a'

    ↝-monoʳ :  (∀{x} → b'˙ x ⊑ b˙ x)  →
      (E , a) ↝ (λ x → F˙ x , b˙ x)  →   (E , a) ↝ λ x → F˙ x , b'˙ x
    ↝-monoʳ =  ↝-mono ⊑-refl

    ↝-respʳ :  (∀{x} → b˙ x ≈ b'˙ x)  →
      (E , a) ↝ (λ x → F˙ x , b˙ x)  →   (E , a) ↝ λ x → F˙ x , b'˙ x
    ↝-respʳ b≈b' =  ↝-monoʳ $ ≈⇒⊑ $ ◠˜ b≈b'

    ↝-ε :  (E , a) ↝ (λ x → F˙ x , b˙ x)  →   (E , a) ↝ λ x → F˙ x , ε
    ↝-ε =  ↝-monoʳ ε-min

    -- Change parameterization of ↝

    ↝-param :  (E , a) ↝ Fb˙ ∘ f →  (E , a) ↝ Fb˙
    ↝-param {f = f} Ea↝Fbf c˙ E✓a∙c  with Ea↝Fbf c˙ E✓a∙c
    … | y , Ffy✓bfy∙c =  f y , Ffy✓bfy∙c

open ERA using (Res; _≈_; _∙_; ε; ⌞_⌟; Env; _✓_; refl˜; ◠˜_; _◇˜_; ∙-congˡ;
  ∙-unitˡ; ∙-comm; ∙-assocʳ; ⌞⌟-cong; ⌞⌟-add; ⌞⌟-unitˡ; ⌞⌟-idem; ✓-resp; ✓-rem)

private variable
  łᴿ łᴿ' ł≈ ł≈' łᴱ łᴱ' ł✓ ł✓' :  Level

--------------------------------------------------------------------------------
-- ⊤ᴱᴿᴬ : Trivial ERA

⊤ᴱᴿᴬ :  ERA łᴿ ł≈ łᴱ ł✓
⊤ᴱᴿᴬ .Res =  ⊤
⊤ᴱᴿᴬ ._≈_ _ _ =  ⊤
⊤ᴱᴿᴬ ._∙_ =  _
⊤ᴱᴿᴬ .ε =  _
⊤ᴱᴿᴬ .⌞_⌟ =  _
⊤ᴱᴿᴬ .Env =  ⊤
⊤ᴱᴿᴬ ._✓_ _ _ =  ⊤
⊤ᴱᴿᴬ .refl˜ =  _
⊤ᴱᴿᴬ .◠˜_ =  _
⊤ᴱᴿᴬ ._◇˜_ =  _
⊤ᴱᴿᴬ .∙-congˡ =  _
⊤ᴱᴿᴬ .∙-unitˡ =  _
⊤ᴱᴿᴬ .∙-comm =  _
⊤ᴱᴿᴬ .∙-assocʳ =  _
⊤ᴱᴿᴬ .⌞⌟-cong =  _
⊤ᴱᴿᴬ .⌞⌟-add =  _
⊤ᴱᴿᴬ .⌞⌟-unitˡ =  _
⊤ᴱᴿᴬ .⌞⌟-idem =  _
⊤ᴱᴿᴬ .✓-resp =  _
⊤ᴱᴿᴬ .✓-rem =  _

--------------------------------------------------------------------------------
-- ×ᴱᴿᴬ :  Product ERA

infixr 1 _×ᴱᴿᴬ_
_×ᴱᴿᴬ_ :  ERA łᴿ ł≈ łᴱ ł✓ →  ERA łᴿ' ł≈' łᴱ' ł✓' →
        ERA (łᴿ ⊔ᴸ łᴿ') (ł≈ ⊔ᴸ ł≈') (łᴱ ⊔ᴸ łᴱ') (ł✓ ⊔ᴸ ł✓')
(Era ×ᴱᴿᴬ Era') .Res =  Era .Res  ×  Era' .Res
(Era ×ᴱᴿᴬ Era') ._≈_ (a , a') (b , b') =  Era ._≈_ a b  ×  Era' ._≈_ a' b'
(Era ×ᴱᴿᴬ Era') ._∙_ (a , a') (b , b') =  Era ._∙_ a b  ,  Era' ._∙_ a' b'
(Era ×ᴱᴿᴬ Era') .ε =  Era .ε  ,  Era' .ε
(Era ×ᴱᴿᴬ Era') .⌞_⌟ (a , a') =  Era .⌞_⌟ a  ,  Era' .⌞_⌟ a'
(Era ×ᴱᴿᴬ Era') .Env =  Era .Env  ×  Era' .Env
(Era ×ᴱᴿᴬ Era') ._✓_ (E , E') (a , a') =  Era ._✓_ E a  ×  Era' ._✓_ E' a'
(Era ×ᴱᴿᴬ Era') .refl˜ =  Era .refl˜  ,  Era' .refl˜
(Era ×ᴱᴿᴬ Era') .◠˜_ (a≈b , a'≈b') =  Era .◠˜_ a≈b  ,  Era' .◠˜_ a'≈b'
(Era ×ᴱᴿᴬ Era') ._◇˜_ (a≈b , a'≈b') (b≈c , b'≈c') =
  Era ._◇˜_ a≈b b≈c  ,  Era' ._◇˜_ a'≈b' b'≈c'
(Era ×ᴱᴿᴬ Era') .∙-congˡ (a≈b , a'≈b') =
  Era .∙-congˡ a≈b  ,  Era' .∙-congˡ a'≈b'
(Era ×ᴱᴿᴬ Era') .∙-unitˡ =  Era .∙-unitˡ  ,  Era' .∙-unitˡ
(Era ×ᴱᴿᴬ Era') .∙-comm =  Era .∙-comm  ,  Era' .∙-comm
(Era ×ᴱᴿᴬ Era') .∙-assocʳ =  Era .∙-assocʳ  ,  Era' .∙-assocʳ
(Era ×ᴱᴿᴬ Era') .⌞⌟-cong (a≈b , a'≈b') =
  Era .⌞⌟-cong a≈b  ,  Era' .⌞⌟-cong a'≈b'
(Era ×ᴱᴿᴬ Era') .⌞⌟-add .π₀ =  Era .⌞⌟-add .π₀  ,  Era' .⌞⌟-add .π₀
(Era ×ᴱᴿᴬ Era') .⌞⌟-add .π₁ =  Era .⌞⌟-add .π₁  ,  Era' .⌞⌟-add .π₁
(Era ×ᴱᴿᴬ Era') .⌞⌟-unitˡ =  Era .⌞⌟-unitˡ  ,  Era' .⌞⌟-unitˡ
(Era ×ᴱᴿᴬ Era') .⌞⌟-idem =  Era .⌞⌟-idem  ,  Era' .⌞⌟-idem
(Era ×ᴱᴿᴬ Era') .✓-resp (a≈b , a'≈b') (E✓a , E'✓a') =
  Era .✓-resp a≈b E✓a  ,  Era' .✓-resp a'≈b' E'✓a'
(Era ×ᴱᴿᴬ Era') .✓-rem (E✓a , E'✓a') =  Era .✓-rem E✓a  ,  Era' .✓-rem E'✓a'

--------------------------------------------------------------------------------
-- Envmᴱᴿᴬ :  Environment modification ERA

Envmᴱᴿᴬ :  (Era : ERA łᴿ ł≈ łᴱ ł✓) (Env' : Set łᴱ') →  (Env' → Era .Env) →
           ERA łᴿ ł≈ łᴱ' ł✓
Envmᴱᴿᴬ Era _ _ .Res =  Era .Res
Envmᴱᴿᴬ Era _ _ ._≈_ =  Era ._≈_
Envmᴱᴿᴬ Era _ _ ._∙_ =  Era ._∙_
Envmᴱᴿᴬ Era _ _ .ε =  Era .ε
Envmᴱᴿᴬ Era _ _ .⌞_⌟ =  Era .⌞_⌟
Envmᴱᴿᴬ _ Env' _ .Env =  Env'
Envmᴱᴿᴬ Era _ H ._✓_ E =   Era ._✓_ (H E)
Envmᴱᴿᴬ Era _ _ .refl˜ =  Era .refl˜
Envmᴱᴿᴬ Era _ _ .◠˜_ =  Era .◠˜_
Envmᴱᴿᴬ Era _ _ ._◇˜_ =  Era ._◇˜_
Envmᴱᴿᴬ Era _ _ .∙-congˡ =  Era .∙-congˡ
Envmᴱᴿᴬ Era _ _ .∙-unitˡ =  Era .∙-unitˡ
Envmᴱᴿᴬ Era _ _ .∙-comm =  Era .∙-comm
Envmᴱᴿᴬ Era _ _ .∙-assocʳ =  Era .∙-assocʳ
Envmᴱᴿᴬ Era _ _ .⌞⌟-cong =  Era .⌞⌟-cong
Envmᴱᴿᴬ Era _ _ .⌞⌟-add =  Era .⌞⌟-add
Envmᴱᴿᴬ Era _ _ .⌞⌟-unitˡ =  Era .⌞⌟-unitˡ
Envmᴱᴿᴬ Era _ _ .⌞⌟-idem =  Era .⌞⌟-idem
Envmᴱᴿᴬ Era _ _ .✓-resp a≈b HE✓a =  Era .✓-resp a≈b HE✓a
Envmᴱᴿᴬ Era _ _ .✓-rem HE✓a∙b =  Era .✓-rem HE✓a∙b

--------------------------------------------------------------------------------
-- Envvᴱᴿᴬ :  Environment validity ERA

Envvᴱᴿᴬ :  (Era : ERA łᴿ ł≈ łᴱ ł✓) →  (Era .Env → Set ł✓') →
           ERA łᴿ ł≈ łᴱ (ł✓ ⊔ᴸ ł✓')
Envvᴱᴿᴬ Era _ .Res =  Era .Res
Envvᴱᴿᴬ Era _ ._≈_ =  Era ._≈_
Envvᴱᴿᴬ Era _ ._∙_ =  Era ._∙_
Envvᴱᴿᴬ Era _ .ε =  Era .ε
Envvᴱᴿᴬ Era _ .⌞_⌟ =  Era .⌞_⌟
Envvᴱᴿᴬ Era _ .Env =  Era .Env
Envvᴱᴿᴬ Era ✓'_ ._✓_ E a =   ✓' E  ×  Era ._✓_ E a
Envvᴱᴿᴬ Era _ .refl˜ =  Era .refl˜
Envvᴱᴿᴬ Era _ .◠˜_ =  Era .◠˜_
Envvᴱᴿᴬ Era _ ._◇˜_ =  Era ._◇˜_
Envvᴱᴿᴬ Era _ .∙-congˡ =  Era .∙-congˡ
Envvᴱᴿᴬ Era _ .∙-unitˡ =  Era .∙-unitˡ
Envvᴱᴿᴬ Era _ .∙-comm =  Era .∙-comm
Envvᴱᴿᴬ Era _ .∙-assocʳ =  Era .∙-assocʳ
Envvᴱᴿᴬ Era _ .⌞⌟-cong =  Era .⌞⌟-cong
Envvᴱᴿᴬ Era _ .⌞⌟-add =  Era .⌞⌟-add
Envvᴱᴿᴬ Era _ .⌞⌟-unitˡ =  Era .⌞⌟-unitˡ
Envvᴱᴿᴬ Era _ .⌞⌟-idem =  Era .⌞⌟-idem
Envvᴱᴿᴬ Era _ .✓-resp a≈b (✓E , E✓a) =  ✓E  ,  Era .✓-resp a≈b E✓a
Envvᴱᴿᴬ Era _ .✓-rem (✓E , E✓a∙b) =  ✓E  ,  Era .✓-rem E✓a∙b

--------------------------------------------------------------------------------
-- Valmᴱᴿᴬ :  Validity modification ERA

Valmᴱᴿᴬ :  (Era :  ERA łᴿ ł≈ łᴱ ł✓) (_✓'_ :  Era .Env → Era .Res → Set ł✓') →
  (∀{E a b} →  Era ._≈_ a b →  E ✓' a →  E ✓' b) →
  (∀{E a b} →  E ✓' Era ._∙_ a b →  E ✓' b) →  ERA łᴿ ł≈ łᴱ (ł✓' ⊔ᴸ ł✓)
Valmᴱᴿᴬ Era _ _ _ .Res =  Era .Res
Valmᴱᴿᴬ Era _ _ _ ._≈_ =  Era ._≈_
Valmᴱᴿᴬ Era _ _ _ ._∙_ =  Era ._∙_
Valmᴱᴿᴬ Era _ _ _ .ε =  Era .ε
Valmᴱᴿᴬ Era _ _ _ .⌞_⌟ =  Era .⌞_⌟
Valmᴱᴿᴬ Era _ _ _ .Env =  Era .Env
Valmᴱᴿᴬ Era _✓'_ _ _ ._✓_ E a =  E ✓' a  ×  Era ._✓_ E a
Valmᴱᴿᴬ Era _ _ _ .refl˜ =  Era .refl˜
Valmᴱᴿᴬ Era _ _ _ .◠˜_ =  Era .◠˜_
Valmᴱᴿᴬ Era _ _ _ ._◇˜_ =  Era ._◇˜_
Valmᴱᴿᴬ Era _ _ _ .∙-congˡ =  Era .∙-congˡ
Valmᴱᴿᴬ Era _ _ _ .∙-unitˡ =  Era .∙-unitˡ
Valmᴱᴿᴬ Era _ _ _ .∙-comm =  Era .∙-comm
Valmᴱᴿᴬ Era _ _ _ .∙-assocʳ =  Era .∙-assocʳ
Valmᴱᴿᴬ Era _ _ _ .⌞⌟-cong =  Era .⌞⌟-cong
Valmᴱᴿᴬ Era _ _ _ .⌞⌟-add =  Era .⌞⌟-add
Valmᴱᴿᴬ Era _ _ _ .⌞⌟-unitˡ =  Era .⌞⌟-unitˡ
Valmᴱᴿᴬ Era _ _ _ .⌞⌟-idem =  Era .⌞⌟-idem
Valmᴱᴿᴬ Era _ ✓'-resp _ .✓-resp a≈b (E✓'a , E✓a) =
  ✓'-resp a≈b E✓'a , Era .✓-resp a≈b E✓a
Valmᴱᴿᴬ Era _ _ ✓'-rem .✓-rem (E✓'a∙b , E✓a∙b) =
  ✓'-rem E✓'a∙b , Era .✓-rem E✓a∙b

--------------------------------------------------------------------------------
-- Upᴱᴿᴬ :  Level-up ERA

Upᴱᴿᴬ :  ERA łᴿ ł≈ łᴱ ł✓ →  ERA (łᴿ ⊔ᴸ łᴿ') (ł≈ ⊔ᴸ ł≈') (łᴱ ⊔ᴸ łᴱ') (ł✓ ⊔ᴸ ł✓')
Upᴱᴿᴬ {łᴿ' = łᴿ'} Era .Res =  Up (Era .Res) {łᴿ'}
Upᴱᴿᴬ {ł≈' = ł≈'} Era ._≈_ (↑ a) (↑ b) =  Up (Era ._≈_ a b) {ł≈'}
Upᴱᴿᴬ Era ._∙_ (↑ a) (↑ b) .↓ =  Era ._∙_ a b
Upᴱᴿᴬ Era .ε .↓ =  Era .ε
Upᴱᴿᴬ Era .⌞_⌟ (↑ a) .↓ =  Era .⌞_⌟ a
Upᴱᴿᴬ {łᴱ' = łᴱ'} Era .Env =  Up (Era .Env) {łᴱ'}
Upᴱᴿᴬ {ł✓' = ł✓'} Era ._✓_ (↑ E) (↑ a) =  Up (Era ._✓_ E a) {ł✓'}
Upᴱᴿᴬ Era .refl˜ .↓ =  Era .refl˜
Upᴱᴿᴬ Era .◠˜_ (↑ a≈b) .↓ =  Era .◠˜_ a≈b
Upᴱᴿᴬ Era ._◇˜_ (↑ a≈b) (↑ b≈c) .↓ =  Era ._◇˜_ a≈b b≈c
Upᴱᴿᴬ Era .∙-congˡ (↑ a≈b) .↓ =  Era .∙-congˡ a≈b
Upᴱᴿᴬ Era .∙-unitˡ .↓ =  Era .∙-unitˡ
Upᴱᴿᴬ Era .∙-comm .↓ =  Era .∙-comm
Upᴱᴿᴬ Era .∙-assocʳ .↓ =  Era .∙-assocʳ
Upᴱᴿᴬ Era .⌞⌟-cong (↑ a≈b) .↓ =  Era .⌞⌟-cong a≈b
Upᴱᴿᴬ Era .⌞⌟-add .π₀ .↓ =  Era .⌞⌟-add .π₀
Upᴱᴿᴬ Era .⌞⌟-add .π₁ .↓ =  Era .⌞⌟-add .π₁
Upᴱᴿᴬ Era .⌞⌟-unitˡ .↓ =  Era .⌞⌟-unitˡ
Upᴱᴿᴬ Era .⌞⌟-idem .↓ =  Era .⌞⌟-idem
Upᴱᴿᴬ Era .✓-resp (↑ a≈b) (↑ E✓a) .↓ =  Era .✓-resp a≈b E✓a
Upᴱᴿᴬ Era .✓-rem (↑ E✓a∙b) .↓ =  Era .✓-rem E✓a∙b
