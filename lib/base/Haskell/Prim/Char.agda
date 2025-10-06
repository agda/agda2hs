module Haskell.Prim.Char where

open import Haskell.Prim

import Agda.Builtin.Char
open Agda.Builtin.Char using (Char)

eqChar : Char → Char → Bool
eqChar a b = eqNat (c2n a) (c2n b)
