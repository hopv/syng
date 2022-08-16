--------------------------------------------------------------------------------
-- Environmental Resource Algebra
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Syho.Model.ERA where

open import Base.Level using (Level; _⊔ᴸ_; sucᴸ)
open import Base.Eq using (_≡_; refl)
open import Base.Func using (_$_; id; _▷_; flip; _∈_)
open import Base.Prod using (_×_; _,_; ∑-syntax)
open import Base.Setoid using (Setoid)

--------------------------------------------------------------------------------
-- Environmental Resource algebra

record  ERA {ℓᴱ ℓ ℓ≈ᴱ ℓ≈ ℓ✓} : Set (sucᴸ (ℓᴱ ⊔ᴸ ℓ ⊔ᴸ ℓ≈ᴱ ⊔ᴸ ℓ≈ ⊔ᴸ ℓ✓))  where
  ------------------------------------------------------------------------------
  -- Fields
  infix 4 _≈ᴱ_ _≈_
  infix 3 _✓_
  infixr 7 _∙_
  infix 0 ◠˜ᴱ_ ◠˜_
  infixr -1 _◇˜ᴱ_ _◇˜_
  field
    ----------------------------------------------------------------------------
    -- Main components

    -- Env :  Environment
    Env :  Set ℓᴱ

    -- Res :  Resource
    Res :  Set ℓ

    -- ≈ᴱ :  Equivalence on environments
    _≈ᴱ_ :  Env →  Env →  Set ℓ≈ᴱ

    -- ≈ :  Equivalence on resources
    _≈_ :  Res →  Res →  Set ℓ≈

    -- ✓ :  Validity
    _✓_ :  Env →  Res →  Set ℓ✓

    -- ∙ :  Product
    _∙_ :  Res →  Res →  Res

    -- ε :  Unit
    ε :  Res

    -- ⌞ ⌟ :  Core
    ⌞_⌟ :  Res → Res

    ----------------------------------------------------------------------------
    -- On ≈ᴱ

    -- ≈ᴱ is reflexive, symmetric and transitive

    refl˜ᴱ :  ∀ {E} →  E ≈ᴱ E
    ◠˜ᴱ_ :  ∀ {E F} →  E ≈ᴱ F →  F ≈ᴱ E
    _◇˜ᴱ_ :  ∀ {E F G} →  E ≈ᴱ F →  F ≈ᴱ G →  E ≈ᴱ G

    ----------------------------------------------------------------------------
    -- On ≈

    -- ≈ is reflexive, symmetric and transitive

    refl˜ :  ∀ {a} →  a ≈ a
    ◠˜_ :  ∀ {a b} →  a ≈ b →  b ≈ a
    _◇˜_ :  ∀ {a b c} →  a ≈ b →  b ≈ c →  a ≈ c

    ----------------------------------------------------------------------------
    -- On ∙

    -- ∙ is congruent, unital with ε, commutative, and associative

    ∙-congˡ :  ∀ {a b c} →  a ≈ b →  a ∙ c ≈ b ∙ c
    ∙-unitˡ :  ∀ {a} →  ε ∙ a ≈ a
    ∙-comm :  ∀ {a b} →  a ∙ b ≈ b ∙ a
    ∙-assocˡ :  ∀ {a b c} →  (a ∙ b) ∙ c ≈ a ∙ (b ∙ c)

    ----------------------------------------------------------------------------
    -- On ✓

    -- ✓ respects ≈ᴱ and ≈

    ✓-resp :  ∀ {E F a b} →  E ≈ᴱ F →  a ≈ b →  E ✓ a →  F ✓ b

    -- ✓ is kept after a resource is removed

    ✓-rem :  ∀ {E a b} →  E ✓ a ∙ b →  E ✓ b

    -- ε satisfies ✓

    ✓-ε :  ∀{E} →  E ✓ ε

    ----------------------------------------------------------------------------
    -- On ⌞⌟

    -- ⌞⌟ preserves ≈

    ⌞⌟-cong :  ∀ {a b} →  a ≈ b →  ⌞ a ⌟ ≈ ⌞ b ⌟

    -- When ⌞⌟'s argument gets added, ⌞⌟'s result gets added

    ⌞⌟-add :  ∀ {a b} →  ∑ b' ,  b' ∙ ⌞ a ⌟ ≈ ⌞ b ∙ a ⌟

    -- ⌞ a ⌟ is absorbed by a

    ⌞⌟-unitˡ :  ∀ {a} →  ⌞ a ⌟ ∙ a  ≈  a

    -- ⌞⌟ is idempotent

    ⌞⌟-idem :  ∀ {a} →  ⌞ ⌞ a ⌟ ⌟ ≈ ⌞ a ⌟

  -- Setoid structures for Env and Res

  Env-setoid :  Setoid ℓᴱ ℓ≈ᴱ
  Env-setoid =  record {
    Car = Env; _≈_ = _≈ᴱ_; refl˜ = refl˜ᴱ; ◠˜_ = ◠˜ᴱ_; _◇˜_ = _◇˜ᴱ_ }

  Res-setoid :  Setoid ℓ ℓ≈
  Res-setoid =  record {
    Car = Res; _≈_ = _≈_; refl˜ = refl˜; ◠˜_ = ◠˜_; _◇˜_ = _◇˜_ }

  private variable
    a a' b b' c d :  Res
    E E' F F' :  Env
    Ea E'a' Fb F'b' Gc :  Env × Res
    ℓX :  Level
    X :  Set ℓX
    Fb˙ F'b'˙ :  X →  Env × Res

  abstract
    ----------------------------------------------------------------------------
    -- On ∙

    -->  ∙-comm :  a ∙ b ≈ b ∙ a

    -- ∙ is congruent

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

    -->  ∙-assocˡ :  (a ∙ b) ∙ c ≈ a ∙ (b ∙ c)

    ∙-assocʳ :  a ∙ (b ∙ c) ≈ (a ∙ b) ∙ c
    ∙-assocʳ =  ◠˜ ∙-assocˡ

    ----------------------------------------------------------------------------
    -- On ✓

    -->  ✓-rem :  E ✓ a ∙ b →  E ✓ b

    -->  ✓-ε :  E ✓ ε

    --  ✓ respects equivalence

    -->  ✓-resp :  E ≈ᴱ F →  a ≈ b →  E ✓ a →  F ✓ b

    ✓-respˡ :  E ≈ᴱ F →  E ✓ a →  F ✓ a
    ✓-respˡ E≈F =  ✓-resp E≈F refl˜

    ✓-respʳ :  a ≈ b →  E ✓ a →  E ✓ b
    ✓-respʳ =  ✓-resp refl˜ᴱ

    ----------------------------------------------------------------------------
    -- On ⌞⌟

    -->  ⌞⌟-cong :  a ≈ b →  ⌞ a ⌟ ≈ ⌞ b ⌟

    -->  ⌞⌟-add :  ∑ b' ,  b' ∙ ⌞ a ⌟ ≈ ⌞ b ∙ a ⌟

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
  -- ≈ᴱᴿ :  Equivalence between environment-resource pairs

  infix 4 _≈ᴱᴿ_

  _≈ᴱᴿ_ :  Env × Res →  Env × Res →  Set (ℓ≈ᴱ ⊔ᴸ ℓ≈)
  (E , a) ≈ᴱᴿ (F , b) =  E ≈ᴱ F  ×  a ≈ b

  abstract

    infix 0 ◠˜ᴱᴿ_
    infixr -1 _◇˜ᴱᴿ_

    -- ≈ᴱᴿ is reflexive, symmetric and transitive

    refl˜ᴱᴿ :  Ea ≈ᴱᴿ Ea
    refl˜ᴱᴿ =  refl˜ᴱ , refl˜

    ◠˜ᴱᴿ_ :  Ea ≈ᴱᴿ Fb →  Fb ≈ᴱᴿ Ea
    ◠˜ᴱᴿ (E≈F , a≈b) =  ◠˜ᴱ E≈F , ◠˜ a≈b

    _◇˜ᴱᴿ_ :  Ea ≈ᴱᴿ Fb →  Fb ≈ᴱᴿ Gc →  Ea ≈ᴱᴿ Gc
    (E≈F , a≈b) ◇˜ᴱᴿ (F≈G , b≈c) =  (E≈F ◇˜ᴱ F≈G) , (a≈b ◇˜ b≈c)

  ------------------------------------------------------------------------------
  -- ⊑ :  Derived pre-order

  infix 4 _⊑_
  _⊑_ :  Res → Res → Set (ℓ ⊔ᴸ ℓ≈)
  a ⊑ b =  ∑ c ,  c ∙ a  ≈  b

  abstract

    -- ⊑ is reflexive

    ≈⇒⊑ :  a ≈ b →  a ⊑ b
    ≈⇒⊑ a≈b =  ε , ∙-unitˡ ◇˜ a≈b

    ⊑-refl :  a ⊑ a
    ⊑-refl =  ≈⇒⊑ refl˜

    -- ⊑ is transitive

    ⊑-trans :  a ⊑ b →  b ⊑ c →  a ⊑ c
    ⊑-trans (d , d∙a≈b) (e , e∙b≈c) =  d ∙ e ,
      ∙-congˡ ∙-comm ◇˜ ∙-assocˡ ◇˜ ∙-congʳ d∙a≈b ◇˜ e∙b≈c

    -- ⊑ respects ≈

    ⊑-resp :  a ≈ b →  c ≈ d →  a ⊑ c →  b ⊑ d
    ⊑-resp a≈b c≈d (e , e∙a≈c) =  e , ∙-congʳ (◠˜ a≈b) ◇˜ e∙a≈c ◇˜ c≈d

    ⊑-respˡ :  a ≈ b →  a ⊑ c →  b ⊑ c
    ⊑-respˡ a≈b a⊑c =  ⊑-resp a≈b refl˜ a⊑c

    ⊑-respʳ :  ∀ {a b c} →  b ≈ c →  a ⊑ b →  a ⊑ c
    ⊑-respʳ b≈c a⊑b =  ⊑-resp refl˜ b≈c a⊑b

    -- ε is the minimum

    ε-min :  ε ⊑ a
    ε-min =  _ , ∙-unitʳ

    -- ∙ is increasing

    ∙-incrˡ :  a  ⊑  b ∙ a
    ∙-incrˡ =  _ , refl˜

    ∙-incrʳ :  a  ⊑  a ∙ b
    ∙-incrʳ =  ⊑-respʳ ∙-comm ∙-incrˡ

    -- Monotonicity of ✓, ∙ and ⌞⌟

    ✓-mono :  a ⊑ b →  E ✓ b →  E ✓ a
    ✓-mono (c , c∙a≈b) E✓b =  E✓b ▷ ✓-respʳ (◠˜ c∙a≈b) ▷ ✓-rem

    ∙-monoˡ :  a ⊑ b →  a ∙ c  ⊑  b ∙ c
    ∙-monoˡ (d , d∙a≈b) =  d , ∙-assocʳ ◇˜ ∙-congˡ d∙a≈b

    ∙-monoʳ :  a ⊑ b →  c ∙ a  ⊑  c ∙ b
    ∙-monoʳ a⊑b =  ⊑-resp ∙-comm ∙-comm $ ∙-monoˡ a⊑b

    ∙-mono :  a ⊑ b →  c ⊑ d →  a ∙ c  ⊑  b ∙ d
    ∙-mono a⊑b c⊑d =  ⊑-trans (∙-monoˡ a⊑b) (∙-monoʳ c⊑d)

    ⌞⌟-mono :  a ⊑ b →  ⌞ a ⌟ ⊑ ⌞ b ⌟
    ⌞⌟-mono (c , c∙a≈b)  with ⌞⌟-add {_} {c}
    ... | c' , c'∙⌞a⌟≈⌞c∙a⌟ =  c' , c'∙⌞a⌟≈⌞c∙a⌟ ◇˜ ⌞⌟-cong c∙a≈b

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
  -- ↝/↝˙ : Environmental resource update

  infix 2 _↝_ _↝˙_

  -- (E , a) ↝ (F, b) : A resource a with an environment E can be updated into
  -- a resource b with an environment F, regardless of the frame resource c
  _↝_ :  Env × Res →  Env × Res →  Set (ℓ ⊔ᴸ ℓ✓)
  (E , a) ↝ (F , b) =  ∀ c →  E ✓ c ∙ a →  F ✓ c ∙ b

  -- a ↝˙ b˙ : a can be updated into b˙ x for some x,
  -- regardless of the environment E and the frame c
  _↝˙_ :  {X : Set ℓX} →
    Env × Res →  (X →  Env × Res) →  Set (ℓ ⊔ᴸ ℓ✓ ⊔ᴸ ℓX)
  (E , a) ↝˙ Fb˙ =  ∀ c →  E ✓ c ∙ a →
    ∑ x ,  let (F , b) = Fb˙ x in  F ✓ c ∙ b

  abstract

    -- Reflexivity

    ↝-refl :  Ea ↝ Ea
    ↝-refl _ =  id

    -- ↝ respects ≈

    ↝-resp :  Ea ≈ᴱᴿ E'a' →  Fb ≈ᴱᴿ F'b' →  Ea ↝ Fb →  E'a' ↝ F'b'
    ↝-resp (E≈E' , a≈a') (F≈F' , b≈b') Ea↝Fb c E'✓c∙a' =  E'✓c∙a' ▷
      ✓-resp (◠˜ᴱ E≈E') (∙-congʳ $ ◠˜ a≈a') ▷ Ea↝Fb c ▷
      ✓-resp F≈F' (∙-congʳ b≈b')

    ↝-respˡ :  Ea ≈ᴱᴿ E'a' →  Ea ↝ Fb →  E'a' ↝ Fb
    ↝-respˡ Ea≈E'a' =  ↝-resp Ea≈E'a' refl˜ᴱᴿ

    ↝-respʳ :  Fb ≈ᴱᴿ F'b' →  Ea ↝ Fb →  Ea ↝ F'b'
    ↝-respʳ =  ↝-resp refl˜ᴱᴿ

    -- ↝˙ respects ≈

    ↝˙-resp :  Ea ≈ᴱᴿ E'a' →  (∀ x →  Fb˙ x ≈ᴱᴿ F'b'˙ x) →
      Ea ↝˙ Fb˙ →  E'a' ↝˙ F'b'˙
    ↝˙-resp (E≈E' , a≈a') ∀xFbx≈F'b'x a↝˙b c E'✓c∙a'
      with  E'✓c∙a' ▷ ✓-resp (◠˜ᴱ E≈E') (∙-congʳ $ ◠˜ a≈a') ▷ a↝˙b c
    ... | x , Fx✓c∙bx  =  let (Fx≈F'x , bx≈b'x) = ∀xFbx≈F'b'x x in
      x , ✓-resp Fx≈F'x (∙-congʳ bx≈b'x) Fx✓c∙bx

    ↝˙-respˡ :  Ea ≈ᴱᴿ E'a' →  Ea ↝˙ Fb˙ →  E'a' ↝˙ Fb˙
    ↝˙-respˡ Ea≈E'a' =  ↝˙-resp Ea≈E'a' (λ _ → refl˜ᴱᴿ)

    ↝˙-respʳ :  (∀ x →  Fb˙ x ≈ᴱᴿ F'b'˙ x) →  Ea ↝˙ Fb˙ →  Ea ↝˙ F'b'˙
    ↝˙-respʳ =  ↝˙-resp refl˜ᴱᴿ
