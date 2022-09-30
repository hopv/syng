--------------------------------------------------------------------------------
-- Size, thunk and shrunk
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Base.Size where

open import Base.Level using (Level)

open import Base.Acc using (Acc; acc)

-- Import and re-export
open import Agda.Builtin.Size public using (
  -- Universe of Size
  SizeUniv;
  -- Size or ordinal
  -- Size :  SizeUniv
  Size;
  -- Inaccessible size/ordinal
  -- ∞ :  Size
  ∞) renaming (
  -- Subtype of Size, consisting of sizes smaller than the given size
  -- Size< :  Size →  SizeUniv
  Size<_ to Size<;
  -- Successor size
  -- ṡˢ_ :  Size →  Size
  ↑_ to infix 10 ṡˢ_;
  -- Maximum of Size
  -- _⊔ˢ_ :  Size →  Size →  Size
  _⊔ˢ_ to infixr 5 _⊔ˢ_)

private variable
  ł :  Level
  ι :  Size
  F G :  Size → Set ł

--------------------------------------------------------------------------------
-- Size₀ :  Set₀ wrapper for Size

-- This is handy but rather dangerous; it should be used with care

record  Size₀ :  Set₀  where
  constructor sz
  field
    sz⁻¹ :  Size

open Size₀ public

--------------------------------------------------------------------------------
-- <ˢ :  Well-founded order on Size₀

infix 4 _<ˢ_

data  _<ˢ_ :  Size₀ →  Size₀ →  Set₀  where
  size< :  ∀{ι' : Size< ι} →  sz ι' <ˢ sz ι

abstract

  -- <ˢ is well-founded

  <ˢ-wf :  Acc _<ˢ_ (sz ι)
  <ˢ-wf =  acc λ{ size< → <ˢ-wf }

--------------------------------------------------------------------------------
-- Thunk F ι :  For flexibly coinductive or coinductive-inductive data types

-- This type intuitively means ∀ ι' < ι . F ι' (*universally* quantified),
-- and thus is *contravariant* with respect to ι in subtyping

infix 8 ¡_
record  Thunk (F : Size → Set ł) (ι : Size) :  Set ł  where
  coinductive

  -- ¡ :  Construct a thunk
  constructor ¡_

  -- ! :  Force Thunk F ι into F ι' for any ι' < ι
  -- It can force Thunk F ∞ into F ∞ (when F satisfies some conditions)
  field  ! :  {ι' : Size< ι} →  F ι'

open Thunk public

-- Map over a thunk

infixr -1 _$ᵀʰ_
_$ᵀʰ_ :  (∀{ι} → F ι → G ι) →  Thunk F ι →  Thunk G ι
(f $ᵀʰ ThF) .! =  f (ThF .!)

--------------------------------------------------------------------------------
-- Shrunk F ι :  For flexibly inductive data types

-- This type intuitively means ∃ ι' < ι . F ι' (*existentially* quantified),
-- and thus is *covariant* with respect to ι in subtyping

infix 8 §_
data  Shrunk (F : Size → Set ł) (ι : Size) :  Set ł  where

  -- Construct a shrunk
  §_ :  {ι' : Size< ι} →  F ι' →  Shrunk F ι

-- Map over a shrunk

infixr -1 _$ˢʰʳ_
_$ˢʰʳ_ :  (∀{ι} → F ι → G ι) →  Shrunk F ι →  Shrunk G ι
f $ˢʰʳ § ShrF =  § f ShrF
