module Haskell.Prim.Floating where

open import Haskell.Prim


--------------------------------------------------
-- Literals


instance
  iNumberFloating : Number Floating
  iNumberFloating .Number.Constraint _ = ⊤
  iNumberFloating .fromNat n = pos n

  iNegativeFloating : Negative Floating
  iNegativeFloating .Negative.Constraint _ = ⊤
  iNegativeFloating .fromNeg n = negNat n


postulate
  pi      : Floating
  exp     : Floating → Floating
  log     : Floating → Floating
  sqrt	  : Floating → Floating
  infixr 8 _**_
  _**_    : Floating → Floating → Floating
  logBase : Floating → Floating → Floating
  sin     : Floating → Floating
  cos     : Floating → Floating
  asin    : Floating → Floating
  acos    : Floating → Floating
  atan    : Floating → Floating
  sinh    : Floating → Floating
  cosh    : Floating → Floating
  asinh   : Floating → Floating
  acosh   : Floating → Floating
  atanh   : Floating → Floating
  log1p   : Floating → Floating
  expm1   : Floating → Floating
  log1pexp: Floating → Floating
  log1mexp: Floating → Floating

--------------------------------------------------
-- Arithmetic


--------------------------------------------------
-- Constraints

isNegativeFloating : Floating → Bool
isNegativeFloating (pos _)    = False
isNegativeFloating (negsuc _) = True

IsNonNegativeFloating : Floating → Set
IsNonNegativeFloating (pos _)      = ⊤
IsNonNegativeFloating n@(negsuc _) =
  TypeError (primStringAppend (primShowFloating n) (" is negative"))