--------------------------------------------------------------------------------
-- Lists and natural numbers
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Base.List.Nat where

open import Base.Level using (Level)
open import Base.Func using (_$_)
open import Base.Nat using (ℕ; ṡ_)
open import Base.Option using (¿_; š_; ň)
open import Base.List using (List; []; _∷_)

private variable
  ł :  Level
  A B :  Set ł

-- Length

len :  List A →  ℕ
len [] =  0
len (_ ∷ as) =  ṡ len as

-- Partial lookup

infix 5 _‼_
_‼_ :  List A →  ℕ →  ¿ A
[] ‼ _ =  ň
(a ∷ _) ‼ 0 =  š a
(_ ∷ as) ‼ ṡ n =  as ‼ n

-- Index update

upd :  ℕ →  A →  List A →  List A
upd _ _ [] =  []
upd 0 b (_ ∷ as) =  b ∷ as
upd (ṡ n) b (a ∷ as) =  a ∷ upd n b as

-- Repeat

rep :  ℕ →  A →  List A
rep 0 _ =  []
rep (ṡ n) a =  a ∷ rep n a

-- Map with an index

infixr -1 _$ⁱᴸ⟨_⟩_ _$ⁱᴸ_

_$ⁱᴸ⟨_⟩_ :  (ℕ → A → B) →  ℕ →  List A →  List B
_ $ⁱᴸ⟨ _ ⟩ [] =  []
f $ⁱᴸ⟨ i ⟩ a ∷ as =  f i a ∷ (f $ⁱᴸ⟨ ṡ i ⟩ as)

_$ⁱᴸ_ :  (ℕ → A → B) →  List A →  List B
f $ⁱᴸ as =  f $ⁱᴸ⟨ 0 ⟩ as
