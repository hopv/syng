--------------------------------------------------------------------------------
-- Lists and natural numbers
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.List.Nat where

open import Base.Level using (Level)
open import Base.List using (List; []; _∷_)
open import Base.Nat using (ℕ; suc)
open import Base.Option using (??_; some; none)
open import Base.Func using (_$_)

private variable
  ℓA :  Level
  A :  Set ℓA

-- Length

len :  List A →  ℕ
len [] =  0
len (_ ∷ as) =  suc $ len as

-- Partial lookup

infix 5 _!!_
_!!_ :  List A →  ℕ →  ?? A
[] !! _ =  none
(a ∷ _) !! 0 =  some a
(_ ∷ as) !! suc n =  as !! n

-- Index update

upd :  ℕ →  A →  List A →  List A
upd _ _ [] =  []
upd 0 b (_ ∷ as) =  b ∷ as
upd (suc n) b (a ∷ as) =  a ∷ upd n b as

-- Repeat

repeat :  ℕ →  A →  List A
repeat 0 _ =  []
repeat (suc n) a =  a ∷ repeat n a
