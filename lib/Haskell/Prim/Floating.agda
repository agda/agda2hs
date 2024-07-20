module Haskell.Prim.Floating where

open import Haskell.Prim

postulate
  pi      : Floating
  exp     : Floating → Floating
  log     : Floating → Floating
  sqrt	  : Floating → Floating
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

