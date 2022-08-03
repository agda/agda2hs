
module Haskell.Prim.Integer where

open import Haskell.Prim
open import Haskell.Prim.Bool


--------------------------------------------------
-- Literals

private
  negNat : Nat → Integer
  negNat 0       = pos 0
  negNat (suc n) = negsuc n

instance
  iNumberInteger : Number Integer
  iNumberInteger .Number.Constraint _ = ⊤
  iNumberInteger .fromNat n = pos n

  iNegativeInteger : Negative Integer
  iNegativeInteger .Negative.Constraint _ = ⊤
  iNegativeInteger .fromNeg n = negNat n


--------------------------------------------------
-- Arithmetic

private
  subNat : Nat → Nat → Integer
  subNat n m = if (ltNat n m) then negsuc (monusNat m (suc n)) else pos (monusNat n m)

negateInteger : Integer → Integer
negateInteger (pos 0)       = pos 0
negateInteger (pos (suc n)) = negsuc n
negateInteger (negsuc n)    = pos (suc n)

addInteger : Integer → Integer → Integer
addInteger (pos    n) (pos    m) = pos (addNat n m)
addInteger (pos    n) (negsuc m) = subNat n (suc m)
addInteger (negsuc n) (pos    m) = subNat m (suc n)
addInteger (negsuc n) (negsuc m) = negsuc (suc (addNat n m))

subInteger : Integer → Integer → Integer
subInteger n m = addInteger n (negateInteger m)

mulInteger : Integer → Integer → Integer
mulInteger (pos    n) (pos    m) = pos (mulNat n m)
mulInteger (pos    n) (negsuc m) = negNat (mulNat n (suc m))
mulInteger (negsuc n) (pos    m) = negNat (mulNat (suc n) m)
mulInteger (negsuc n) (negsuc m) = pos (mulNat (suc n) (suc m))

absInteger : Integer → Integer
absInteger (pos    n) = pos n
absInteger (negsuc n) = pos (suc n)

signInteger : Integer → Integer
signInteger (pos 0)       = 0
signInteger (pos (suc _)) = 1
signInteger (negsuc _)    = -1


--------------------------------------------------
-- Comparisons

eqInteger : Integer → Integer → Bool
eqInteger (pos n)    (pos m)    = eqNat n m
eqInteger (negsuc n) (negsuc m) = eqNat n m
eqInteger _          _          = False

ltInteger : Integer → Integer → Bool
ltInteger (pos    n) (pos    m) = ltNat n m
ltInteger (pos    n) (negsuc _) = False
ltInteger (negsuc n) (pos    _) = True
ltInteger (negsuc n) (negsuc m) = ltNat m n


--------------------------------------------------
-- Show

showInteger : Integer → List Char
showInteger n = primStringToList (primShowInteger n)


--------------------------------------------------
-- Constraints

isNegativeInteger : Integer → Bool
isNegativeInteger (pos _)    = False
isNegativeInteger (negsuc _) = True

IsNonNegativeInteger : Integer → Set
IsNonNegativeInteger (pos _)      = ⊤
IsNonNegativeInteger n@(negsuc _) =
  TypeError (primStringAppend (primShowInteger n) (" is negative"))
