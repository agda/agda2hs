
module Haskell.Prim.Integer where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Agda.Builtin.Unit
open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg

import Agda.Builtin.Int
open Agda.Builtin.Int public using () renaming (Int to Integer)
open Agda.Builtin.Int renaming (Int to Integer)

open import Haskell.Prim


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
  subNat n m = if n < m then negsuc (m - suc n) else pos (n - m)

negateInteger : Integer → Integer
negateInteger (pos 0)       = pos 0
negateInteger (pos (suc n)) = negsuc n
negateInteger (negsuc n)    = pos (suc n)

addInteger : Integer → Integer → Integer
addInteger (pos    n) (pos    m) = pos (n + m)
addInteger (pos    n) (negsuc m) = subNat n (suc m)
addInteger (negsuc n) (pos    m) = subNat m (suc n)
addInteger (negsuc n) (negsuc m) = negsuc (n + m + 1)

subInteger : Integer → Integer → Integer
subInteger n m = addInteger n (negateInteger m)

mulInteger : Integer → Integer → Integer
mulInteger (pos    n) (pos    m) = pos (n * m)
mulInteger (pos    n) (negsuc m) = negNat (n * suc m)
mulInteger (negsuc n) (pos    m) = negNat (suc n * m)
mulInteger (negsuc n) (negsuc m) = pos (suc n * suc m)

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
eqInteger (pos n)    (pos m)    = n == m
eqInteger (negsuc n) (negsuc m) = n == m
eqInteger _          _          = false

ltInteger : Integer → Integer → Bool
ltInteger (pos    n) (pos    m) = n < m
ltInteger (pos    n) (negsuc _) = false
ltInteger (negsuc n) (pos    _) = true
ltInteger (negsuc n) (negsuc m) = m < n


--------------------------------------------------
-- Show

showInteger : Integer → List Char
showInteger n = primStringToList (primShowInteger n)

--------------------------------------------------
-- Constraints

isNegativeInteger : Integer → Bool
isNegativeInteger (pos _)    = false
isNegativeInteger (negsuc _) = true

IsNonNegativeInteger : Integer → Set
IsNonNegativeInteger (pos _)      = ⊤
IsNonNegativeInteger n@(negsuc _) =
  TypeError (primStringAppend (primShowInteger n) (" is negative"))
