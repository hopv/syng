{-# OPTIONS --sized-types #-}

module Logic.Prop where

open import Size
open import Level
open import Data.Bool
open import Codata.Sized.Thunk

data SProp {ℓ} (i : Size) : Set (suc ℓ) where
  all : {A : Set ℓ} → (A → SProp {ℓ} i) → SProp i
  ex : {A : Set ℓ} → (A → SProp {ℓ} i) → SProp i
  ⌈_⌉ : Set ℓ → SProp i
  save : Bool → Thunk (SProp {ℓ}) i → SProp i

syntax all (λ x → P) = `∀ x `→ P
syntax ex (λ x → P) = `∃ x `→ P
