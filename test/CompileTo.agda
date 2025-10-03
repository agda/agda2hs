
open import Haskell.Prim
open import Haskell.Prelude

private variable
    @0 n : Nat

data Vec (a : Set) : @0 Nat → Set where
    [] : Vec a 0
    _∷_ : a → Vec a n → Vec a (suc n)

{-# COMPILE AGDA2HS Vec to List #-}

test1 : Vec Int 3
test1 = 1 ∷ 2 ∷ 3 ∷ []

{-# COMPILE AGDA2HS test1 #-}

listToVec : (xs : List a) → Vec a (lengthNat xs)
listToVec [] = []
listToVec (x ∷ xs) = x ∷ listToVec xs

{-# COMPILE AGDA2HS listToVec transparent #-}

test2 : Vec Int 3
test2 = listToVec (map (_+ 1) (1 ∷ 2 ∷ 3 ∷ []))

{-# COMPILE AGDA2HS test2 #-}

llength : List a → Nat
llength [] = 0
llength (x ∷ xs) = 1 + llength xs

{-# COMPILE AGDA2HS llength #-}

vlength : Vec a n → Nat
vlength [] = 0
vlength (x ∷ xs) = 1 + vlength xs

{-# COMPILE AGDA2HS vlength to llength #-}

test3 : Nat
test3 = vlength test1

{-# COMPILE AGDA2HS test3 #-}
