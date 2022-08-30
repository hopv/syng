--------------------------------------------------------------------------------
-- Lists and natural numbers
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.List.Nat where

open import Base.Level using (Level)
open import Base.Func using (_$_)
open import Base.Nat using (ℕ; suc)
open import Base.Option using (¿_; some; none)
open import Base.List using (List; []; _∷_)

private variable
  ł :  Level
  A B :  Set ł

-- Length

len :  List A →  ℕ
len [] =  0
len (_ ∷ as) =  suc $ len as

-- Partial lookup

infix 5 _‼_
_‼_ :  List A →  ℕ →  ¿ A
[] ‼ _ =  none
(a ∷ _) ‼ 0 =  some a
(_ ∷ as) ‼ suc n =  as ‼ n

-- Index update

upd :  ℕ →  A →  List A →  List A
upd _ _ [] =  []
upd 0 b (_ ∷ as) =  b ∷ as
upd (suc n) b (a ∷ as) =  a ∷ upd n b as

-- Repeat

rep :  ℕ →  A →  List A
rep 0 _ =  []
rep (suc n) a =  a ∷ rep n a

-- Map with an index

infixr -1 _$ⁱᴸ⟨_⟩_ _$ⁱᴸ_

_$ⁱᴸ⟨_⟩_ :  (ℕ → A → B) →  ℕ →  List A →  List B
_ $ⁱᴸ⟨ _ ⟩ [] =  []
f $ⁱᴸ⟨ i ⟩ a ∷ as =  f i a ∷ (f $ⁱᴸ⟨ suc i ⟩ as)

_$ⁱᴸ_ :  (ℕ → A → B) →  List A →  List B
f $ⁱᴸ as =  f $ⁱᴸ⟨ 0 ⟩ as
