--------------------------------------------------------------------------------
-- Size, thunk and shrunk
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Base.Size where

open import Base.Level using (Level)

open import Base.Acc using (Acc; acc)

-- Import and re-export
open import Agda.Builtin.Size public using (
  -- Universe of 𝕊
  SizeUniv;
  -- Inaccessible size/ordinal
  -- ∞ :  𝕊
  ∞) renaming (
  -- Size or ordinal
  -- 𝕊 :  SizeUniv
  Size to 𝕊;
  -- Subtype of 𝕊, consisting of sizes smaller than the given size
  -- 𝕊< :  𝕊 →  SizeUniv
  Size<_ to 𝕊<;
  -- Successor size
  -- ṡˢ_ :  𝕊 →  𝕊
  ↑_ to infix 10 ṡˢ_;
  -- Maximum of 𝕊
  -- _⊔ˢ_ :  𝕊 →  𝕊 →  𝕊
  _⊔ˢ_ to infixr 5 _⊔ˢ_)

private variable
  ł :  Level
  ι :  𝕊
  F G :  𝕊 → Set ł

--------------------------------------------------------------------------------
-- 𝕊' :  Set ł wrapper for 𝕊

-- This is handy but rather dangerous; it should be used with care

record  𝕊' (ł : Level) :  Set ł  where
  constructor sz
  field
    sz⁻¹ :  𝕊

open 𝕊' public

--------------------------------------------------------------------------------
-- <ˢ :  Well-founded order on Size₀

infix 4 _<ˢ_

data  _<ˢ_ {ł : Level} :  𝕊' ł →  𝕊' ł →  Set ł  where
  size< :  ∀{ι' : 𝕊< ι} →  sz ι' <ˢ sz ι

abstract

  -- <ˢ is well-founded

  <ˢ-wf :  Acc (_<ˢ_ {ł}) (sz ι)
  <ˢ-wf =  acc λ{ size< → <ˢ-wf }

--------------------------------------------------------------------------------
-- Thunk F ι :  For flexibly coinductive or coinductive-inductive data types

-- This type intuitively means ∀ ι' < ι . F ι' (*universally* quantified),
-- and thus is *contravariant* w.r.t. ι in subtyping

infix 8 ¡_
record  Thunk (F : 𝕊 → Set ł) (ι : 𝕊) :  Set ł  where
  coinductive

  -- ¡ :  Construct a thunk
  constructor ¡_

  -- ! :  Force Thunk F ι into F ι' for any ι' < ι
  -- It can force Thunk F ∞ into F ∞ (when F satisfies some conditions)
  field  ! :  {ι' : 𝕊< ι} →  F ι'

open Thunk public

-- Map over a thunk

infixr -1 _$ᵀʰ_
_$ᵀʰ_ :  (∀{ι} → F ι → G ι) →  Thunk F ι →  Thunk G ι
(f $ᵀʰ ThF) .! =  f (ThF .!)

--------------------------------------------------------------------------------
-- Shrunk F ι :  For flexibly inductive data types

-- This type intuitively means ∃ ι' < ι . F ι' (*existentially* quantified),
-- and thus is *covariant* w.r.t. ι in subtyping

infix 8 §_
data  Shrunk (F : 𝕊 → Set ł) (ι : 𝕊) :  Set ł  where

  -- Construct a shrunk
  §_ :  {ι' : 𝕊< ι} →  F ι' →  Shrunk F ι

-- Map over a shrunk

infixr -1 _$ˢʰʳ_
_$ˢʰʳ_ :  (∀{ι} → F ι → G ι) →  Shrunk F ι →  Shrunk G ι
f $ˢʰʳ § ShrF =  § f ShrF
